import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Geometry.Gradient

/-!
# Coordinate-basis expansion of the chart-α globally smooth orthonormal frame

For a closed Riemannian manifold `(M, g)`, a chart centre `α : M`, and an
index `i : Fin (Module.finrank ℝ E)`, the globally smooth tangent-bundle
section `chartFrameNormGlobalSmooth g α i : Cₛ^∞⟮I; E, TangentSpace I⟯`
agrees, on the chart-α partition-of-unity tsupport intersected with the
chart-α Levi-Civita good set, with the `g`-Gram-Schmidt orthonormalisation
`chartFrameNorm g α i` of the chart-α coordinate frame
`chartBasisVecFiber α k`.

This file records:

* the change-of-basis matrix `C(b)^k_i := (chartBasisFamily α hb).repr (B_i b) k`
  expressing the orthonormal frame `B_i(b) := chartFrameNormGlobalSmooth g α i b`
  in the chart-α coordinate basis `chartBasisVecFiber α k b`;
* the coordinate expansion `B_i b = Σ_k C(b)^k_i • chartBasisVecFiber α k b`;
* the inverse-Gram identity
  `Σ_i C(b)^k_i · C(b)^l_i = chartInvGramMatrix g α b k l`,
  which is the algebraic content carrying an orthonormal-frame trace
  `Σ_i ⟨B_i, ·⟩⟨B_i, ·⟩` to the metric trace
  `g^{kl}(b) ⟨∂_k, ·⟩⟨∂_l, ·⟩`.

The base point `b` ranges over `chartLeviCivitaGoodSet α` (which in
particular sits inside the chart-α trivialization base set), on which both
the chart-α coordinate basis and the chart-α Gram matrix are well-defined
and the inverse Gram matrix is the genuine matrix inverse of the Gram
matrix.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Definition: the coordinate-basis matrix -/

/-- The Gram-Schmidt coefficient matrix expressing the chart-α orthonormal frame
`chartFrameNormGlobalSmooth g α i` in the chart-α coordinate basis
`chartBasisVecFiber α k`. The `(i, k)`-th entry is the `k`-th coordinate of
`chartFrameNormGlobalSmooth g α i b` against the basis
`chartBasisFamily α hb`, taken at a base-set point. Off the chart-α base
set, the matrix is `0` (junk value). -/
noncomputable def chartFrameNormGlobalSmoothCoordMatrix
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (b : M) : ℝ := by
  classical
  exact
    if h : b ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (chartBasisFamily (I := I) α h).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k
    else 0

/-- On the chart-α base set, the coordinate-basis matrix unfolds as the
`Basis.repr` of the global frame in the chart-α basis. -/
private lemma chartFrameNormGlobalSmoothCoordMatrix_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b =
      (chartBasisFamily (I := I) α hb).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k := by
  classical
  unfold chartFrameNormGlobalSmoothCoordMatrix
  rw [dif_pos hb]

/-! ## Expansion of the orthonormal frame in the coordinate basis -/

/-- **Expansion of the chart-α orthonormal frame in the chart-α coordinate
basis** at a chart-α Levi-Civita good-set point. -/
theorem chartFrameNormGlobalSmooth_eq_coordMatrix_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
          chartBasisVecFiber (I := I) α k b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  -- Apply Basis.sum_repr to the chart-α basis at b.
  have hsum := (chartBasisFamily (I := I) α hb_base).sum_repr
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
  -- hsum : ∑ k, (basis.repr v) k • basis k = v
  -- Rewrite basis k = chartBasisVecFiber α k b and the repr via the matrix.
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce]
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [chartFrameNormGlobalSmoothCoordMatrix_of_mem (I := I) (M := M) g α i k hb_base]
  rw [chartBasisFamily_apply (I := I) α hb_base k]

/-! ## Linear-algebra interlude: the basis-expansion sums

The proof of the inverse-Gram identity proceeds by expanding both arguments
of the orthonormal-frame inner product
`g.inner b (B_i b) (B_j b)` against the chart-α coordinate basis
`chartBasisVecFiber α k b`, and identifying the resulting matrix identity
`C^T G C = I` with `C C^T = G^{-1}`.
-/

section LinearAlgebra

variable (g : SmoothRiemannianMetric I M) (α : M) {b : M}

/-- The change-of-basis matrix at a base-set point, packaged as a `Matrix`.
The `(i, k)`-th entry is `C(b)^k_i = chartFrameNormGlobalSmoothCoordMatrix
g α i k b`. -/
private noncomputable def coordMatrixOf (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b

private noncomputable def coordMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun i k => coordMatrixOf (I := I) (M := M) g α (b := b) i k)

@[simp] private lemma coordMatrix_apply (i k : Fin (Module.finrank ℝ E)) :
    coordMatrix (I := I) (M := M) g α (b := b) i k =
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b := rfl

/-- Expansion identity for one slot of the orthonormal frame as a sum of
coordinate-basis vectors at a chart-α Levi-Civita good-set point. -/
private lemma chartFrameNormGlobalSmooth_eq_coord_sum_of_mem
    (i : Fin (Module.finrank ℝ E))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      ∑ k : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k •
          chartBasisVecFiber (I := I) α k b := by
  classical
  have h :=
    chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := b) hb
  -- The headline rewrote the LHS using the coercion (= .toFun); restore.
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce] at h
  rw [h]
  rfl

/-- **Bilinear expansion of `g_b(B_i b, B_j b)` via the chart-α coordinate
basis (Gram form).** -/
private lemma gram_expand_coordBasis
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) j l *
            chartGramMatrix (I := I) g α b k l := by
  classical
  -- Expand both arguments via the coordinate-basis sum.
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α i hb]
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α j hb]
  -- Now expand the bilinear form `g.inner b`.
  set v : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun k => chartBasisVecFiber (I := I) α k b with hv_def
  set a : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => coordMatrix (I := I) (M := M) g α (b := b) i k with ha_def
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => coordMatrix (I := I) (M := M) g α (b := b) j l with hc_def
  -- Want: g.inner b (∑ k, a k • v k) (∑ l, c l • v l)
  --      = ∑ k ∑ l, a k * c l * g.inner b (v k) (v l)
  -- which is a standard bilinear expansion.
  have hL :
      g.inner b (∑ k, a k • v k) =
        ∑ k, a k • g.inner b (v k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  -- (a k • g.inner b (v k)) (∑ l, c l • v l)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- a k * (g.inner b (v k)) (∑ l, c l • v l)
  have hR :
      g.inner b (v k) (∑ l, c l • v l) =
        ∑ l, c l * g.inner b (v k) (v l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]; rfl
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- a k * (c l * g.inner b (v k) (v l))
  -- versus a k * c l * chartGramMatrix g α b k l
  rw [chartGramMatrix_apply]
  ring

/-- **Matrix form of orthonormality.** At a chart-α Levi-Civita good-set
point in the chart-α partition-of-unity tsupport, the change-of-basis matrix
`C(b)` satisfies `C(b) * G(b) * C(b)ᵀ = I`, where `G(b) = chartGramMatrix g α b`. -/
private lemma orthonormal_matrix_form_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    coordMatrix (I := I) (M := M) g α (b := b) *
        chartGramMatrix (I := I) g α b *
          (coordMatrix (I := I) (M := M) g α (b := b)).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  -- Compute (C * G * Cᵀ) i j and match to δ_{ij}.
  -- By `gram_expand_coordBasis`, the RHS double sum equals `g.inner b (B_i b) (B_j b)`,
  -- and by orthonormality this equals δ_{ij}.
  have hbpouGood :
      b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α := ⟨hb_pou, hb⟩
  have horth :=
    chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
      (I := I) (M := M) g α (b := b) hbpouGood i j
  -- horth : g.inner b (B_i b) (B_j b) = if i = j then 1 else 0
  have hexp := gram_expand_coordBasis (I := I) (M := M) g α (b := b) hb i j
  rw [horth] at hexp
  -- hexp: (if i = j then 1 else 0) = ∑ k ∑ l, C_{ik} * C_{jl} * G_{kl}
  -- Goal: (C * G * Cᵀ) i j = (1 : Matrix _ _ _) i j
  rw [Matrix.mul_apply]
  -- Goal: ∑ k₀, (C * G) i k₀ * (Cᵀ) k₀ j = (1 : Matrix _ _ _) i j
  have h_inner : ∀ k₀ : Fin (Module.finrank ℝ E),
      (coordMatrix (I := I) (M := M) g α (b := b) *
          chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j =
      ∑ l₀ : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ := by
    intro k₀
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k₀, (coordMatrix (I := I) (M := M) g α (b := b) *
            chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j) =
      ∑ k₀, ∑ l₀,
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ from
    Finset.sum_congr rfl (fun k₀ _ => h_inner k₀)]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hexp]
  -- LHS double sum: ∑ k₀ ∑ l₀, C_{i l₀} * G_{l₀ k₀} * C_{j k₀}
  -- RHS double sum: ∑ k ∑ l, C_{ik} * C_{jl} * G_{kl}
  -- Swap LHS sum order and relabel.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  ring

/-- **Inverse-matrix consequence of orthonormality.** At a chart-α Levi-Civita
good-set point in the chart-α partition-of-unity tsupport,
`Cᵀ * C = G⁻¹`, where `C = coordMatrix` and `G = chartGramMatrix g α b`. -/
private lemma orthonormal_matrix_inverse_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (coordMatrix (I := I) (M := M) g α (b := b)).transpose *
        coordMatrix (I := I) (M := M) g α (b := b) =
      chartInvGramMatrix (I := I) g α b := by
  classical
  have hAGA := orthonormal_matrix_form_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  -- A G Aᵀ = 1 means A * (G * Aᵀ) = 1, so A⁻¹ = G * Aᵀ.
  -- Then (G * Aᵀ) * A = A⁻¹ * A = 1, so G * (Aᵀ * A) = 1, so Aᵀ * A = G⁻¹.
  set A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    coordMatrix (I := I) (M := M) g α (b := b)
  set G : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := chartGramMatrix (I := I) g α b
  -- hAGA : A * G * A.transpose = 1.
  have hAGA_right : A * (G * A.transpose) = 1 := by
    rw [← Matrix.mul_assoc]; exact hAGA
  have hG_At_eq_invA : G * A.transpose = A⁻¹ :=
    (Matrix.inv_eq_right_inv hAGA_right).symm
  -- Use `mul_eq_one_comm` to flip multiplication order in the matrix ring.
  have hA_left_inv : (G * A.transpose) * A = 1 :=
    mul_eq_one_comm.mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  -- hA_left_inv : G * (A.transpose * A) = 1, hence A.transpose * A = G⁻¹.
  have hAt_eq_Ginv : A.transpose * A = G⁻¹ :=
    (Matrix.inv_eq_right_inv hA_left_inv).symm
  -- chartInvGramMatrix g α b = (chartGramMatrix g α b)⁻¹ by definition.
  unfold chartInvGramMatrix
  exact hAt_eq_Ginv

end LinearAlgebra

/-! ## Headline: orthonormality identity for the coordinate matrix -/

/-- **Orthonormality identity for the coordinate matrix.**
At a base point `b` lying in the chart-α partition-of-unity tsupport
intersected with the chart-α Levi-Civita good set, the chart-α coordinate
matrix `C(b)` of the chart-α orthonormal frame satisfies
```
Σ_i C(b)^k_i · C(b)^l_i = (g^{kl})(b)
```
where `g^{kl}(b) = chartInvGramMatrix g α b k l`. This is the inverse-Gram
identity that carries an orthonormal-frame trace
`Σ_i ⟨B_i, ·⟩⟨B_i, ·⟩` to the metric trace
`g^{kl} ⟨∂_k, ·⟩⟨∂_l, ·⟩`. -/
theorem chartFrameNormGlobalSmoothCoordMatrix_orthonormality
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (k l : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b) =
      chartInvGramMatrix (I := I) g α b k l := by
  classical
  have h := orthonormal_matrix_inverse_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  -- h : Cᵀ * C = G⁻¹ = chartInvGramMatrix g α b.
  -- Evaluate (Cᵀ * C) k l:
  have heval : ((coordMatrix (I := I) (M := M) g α (b := b)).transpose *
      coordMatrix (I := I) (M := M) g α (b := b)) k l =
        chartInvGramMatrix (I := I) g α b k l := by
    rw [h]
  -- (Cᵀ * C) k l = ∑ i, Cᵀ k i * C i l = ∑ i, C i k * C i l.
  rw [Matrix.mul_apply] at heval
  rw [show (∑ i,
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k i *
          coordMatrix (I := I) (M := M) g α (b := b) i l) =
      ∑ i,
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) i l from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]] at heval
  -- Unfold coordMatrix to chartFrameNormGlobalSmoothCoordMatrix.
  simp only [coordMatrix_apply] at heval
  exact heval

section
#print axioms
  DifferentialGeometry.Integral.Connection.chartFrameNormGlobalSmooth_eq_coordMatrix_sum
#print axioms
  DifferentialGeometry.Integral.Connection.chartFrameNormGlobalSmoothCoordMatrix_orthonormality
end

end Connection
end Integral
end DifferentialGeometry
