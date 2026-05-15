import DifferentialGeometry.Analysis.Laplacian.Regularity.HessianChartAlphaMatrix

/-!
# Unconditional chart-α Frobenius invariance

This module discharges `chartFrobeniusInvariance g α f x` (defined in
`HessianChartInvariance`) unconditionally on the chart-α source, by porting the
matrix-algebra infrastructure from `Integral/Connection/Bochner.lean` and
`BochnerConcrete.lean` to the chart-α basis at a manifold point `x`.

## Strategy

Let `α, x : M` with `x ∈ (chartAt H α).source`, and let `f : M → ℝ` be smooth.
Define:

* `B_i_α := chartBasisVecFiber α i x` — the chart-α basis at `x`, transported
  from the model basis via the trivialization at `α`.
* `B_i_x := chartBasisVecFiber x i x = (chartModelBasis E) i` — the chart-x
  basis at `x`.
* `P_{ij} := (chartModelBasis E).repr (B_i_α) j` — the change-of-basis matrix
  from chart-α to chart-x basis at `x`.

Both bases span `T_x M`. The Gram matrices satisfy
`G_α = P G_x P^T` (gram expansion), hence `G_α^{-1} = (P^T)^{-1} G_x^{-1} P^{-1}`,
equivalently `P^T G_α^{-1} P = G_x^{-1}`.

Using the chart-α matrix identity (`chartAlphaMatrixIdentity_holds`),
`H_{ij,α} = abstractHessian g f x (B_i_α) (B_j_α) = ∑_{ab} P_{ia} P_{jb} H_{ab,x}`
where `H_{ij,x} = chartHessianTensor g x f i j x` (by the chart-x matrix
identity at `x`).

Substituting into the chart-α Frobenius squared:
```
∑_{ijkl} G_α^{ik} G_α^{jl} H_{ij,α} H_{kl,α}
  = ∑_{abcd} (∑_{ik} P_{ia} G_α^{ik} P_{kc}) (∑_{jl} P_{jb} G_α^{jl} P_{ld}) H_{ab,x} H_{cd,x}
  = ∑_{abcd} G_x^{ac} G_x^{bd} H_{ab,x} H_{cd,x}
  = chartHessFrobeniusSq g f x.
```

This is the chart-α Frobenius invariance.

## Main results

* `chartFrobeniusInvariance_holds` — the chart-α Frobenius invariance Prop
  holds unconditionally for `x ∈ (chartAt H α).source`.

* `chartFrobeniusSqHSBridge_holds` — the chart-α HS bridge Prop holds
  unconditionally for `x ∈ (chartAt H α).source`.

* `smoothTensorPairingChart_eq_hessPairingChart_pullback` — the chart-α tensor
  pairing on `EuclN` equals the chart-invariant pairing on `M` at the pulled-back
  point, unconditionally on the chart target.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaFrobenius

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Chart-α change-of-basis matrix at `x`

The matrix `P_α(x)` records the coordinates of the chart-α basis vectors
`B_i_α := chartBasisVecFiber α i x` in the chart-x basis `(chartModelBasis E)`. -/

/-- Change-of-basis matrix from the chart-α basis at `x` (vectors
`chartBasisVecFiber α i x ∈ T_x M`) to the chart-x basis at `x` (the model basis
`(chartModelBasis E)` via `chartBasisVecFiber_self`). -/
private noncomputable def chartAlphaCoBchange
    (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k =>
    (chartModelBasis E).repr
      ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k

@[simp] private lemma chartAlphaCoBchange_apply
    (α : M) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartAlphaCoBchange (I := I) α x i k =
      (chartModelBasis E).repr
        ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k := rfl

/-! ## Decomposition of the chart-α basis vector in the chart-x model basis -/

/-- `B_i_α = ∑_k P_{ik} • (chartModelBasis E) k` (as a tangent vector in `T_x M`,
identified with the model space `E` via the chart-x trivialization at `x`). -/
private lemma chartBasisVecFiber_decompose_in_modelBasis
    (α : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k •
          ((chartModelBasis E) k : TangentSpace I x) := by
  classical
  have h := (chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x)
  exact h.symm

/-! ## Gram-expansion: `G_α(x) = P G_x P^T` -/

/-- Helper: the bilinear expansion of a CLM-bilinear pairing against two finite sums.
For any continuous bilinear `Hb : T_x M →L T_x M →L ℝ`, coefficient sequences
`c_i, d_j : Fin n → ℝ`, and tangent vectors `u, w : Fin n → T_x M`,
`Hb (∑ i c_i • u i) (∑ j d_j • w j) = ∑ i j, c_i * d_j * Hb (u i) (w j)`. -/
private lemma clm_bilinear_expand_two_sums
    {x : M} (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (n : ℕ)
    (c : Fin n → ℝ) (d : Fin n → ℝ)
    (u w : Fin n → TangentSpace I x) :
    Hb (∑ i : Fin n, c i • u i) (∑ j : Fin n, d j • w j) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * d j * Hb (u i) (w j) := by
  classical
  -- First expand Hb on the outer sum: Hb (∑ i, c i • u i) = ∑ i, c i • Hb (u i).
  have h_outer : Hb (∑ i : Fin n, c i • u i) =
      ∑ i : Fin n, c i • Hb (u i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Hb.map_smul]
  rw [h_outer]
  -- Apply the CLM sum to (∑ j, d j • w j).
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- (c i • Hb (u i)) applied to (∑ j, d j • w j).
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- c i * Hb (u i) (∑ j, d j • w j) = c i * (∑ j, d j * Hb (u i) (w j)).
  have h_inner : Hb (u i) (∑ j : Fin n, d j • w j) =
      ∑ j : Fin n, d j * Hb (u i) (w j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [(Hb (u i)).map_smul]
    rw [smul_eq_mul]
  rw [h_inner]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- Specialisation to `g.inner x`. -/
private lemma g_inner_bilinear_expand_two_sums
    (g : SmoothRiemannianMetric I M) (x : M)
    (n : ℕ)
    (c : Fin n → ℝ) (d : Fin n → ℝ)
    (u w : Fin n → TangentSpace I x) :
    g.inner x (∑ i : Fin n, c i • u i) (∑ j : Fin n, d j • w j) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * d j * g.inner x (u i) (w j) :=
  clm_bilinear_expand_two_sums (I := I) (g.inner x) n c d u w

/-- The chart-α Gram matrix at `x` admits a P-expansion against the chart-x
Gram matrix at `x`:
`chartGramMatrix g α x i j = ∑_{kl} P_{ik} P_{jl} chartGramMatrix g x x k l`. -/
private lemma chartGramMatrix_alpha_eq_PGPt
    (g : SmoothRiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α x i j =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k *
          chartAlphaCoBchange (I := I) α x j l *
          chartGramMatrix (I := I) g x x k l := by
  classical
  -- Decompose B_i_α and B_j_α in the model basis.
  have hi := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x i
  have hj := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x j
  -- Apply the CLM-bilinear expansion lemma (specialised to g.inner x).
  have h_expand :
      g.inner x (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k *
          chartAlphaCoBchange (I := I) α x j l *
          g.inner x ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    conv_lhs => rw [hi, hj]
    exact clm_bilinear_expand_two_sums (I := I) (g.inner x) (Module.finrank ℝ E)
      (fun k => chartAlphaCoBchange (I := I) α x i k)
      (fun l => chartAlphaCoBchange (I := I) α x j l)
      (fun k => (chartModelBasis E) k)
      (fun l => (chartModelBasis E) l)
  rw [chartGramMatrix_apply]
  rw [h_expand]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Identify g.inner x e_k e_l = chartGramMatrix g x x k l.
  have h_inner : g.inner x ((chartModelBasis E) k : TangentSpace I x)
      ((chartModelBasis E) l : TangentSpace I x) =
      chartGramMatrix (I := I) g x x k l := by
    rw [chartGramMatrix_apply]
    rw [chartBasisVecFiber_self (I := I) x k]
    rw [chartBasisVecFiber_self (I := I) x l]
  rw [h_inner]

/-! ## Matrix form of the Gram expansion: `G_α = P G_x P^T` -/

/-- The matrix identity `G_α(x) = P G_x P^T`, where `P` is the chart-α
change-of-basis matrix. -/
private lemma chartGramMatrix_alpha_eq_PGPt_matrix
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    chartGramMatrix (I := I) g α x =
      chartAlphaCoBchange (I := I) α x *
        chartGramMatrix (I := I) g x x *
        (chartAlphaCoBchange (I := I) α x).transpose := by
  classical
  ext i j
  rw [chartGramMatrix_alpha_eq_PGPt (I := I) g α x i j]
  -- (P * G * P^T) i j = ∑ k (P G) i k * P^T k j = ∑ k ∑ l P_{il} G_{lk} P_{jk}.
  rw [Matrix.mul_apply]
  -- Now (P G) i k = ∑ l P_{il} G_{lk}, and P^T k j = P_{jk}.
  have h_inner : ∀ k : Fin (Module.finrank ℝ E),
      (chartAlphaCoBchange (I := I) α x *
          chartGramMatrix (I := I) g x x) i k *
        (chartAlphaCoBchange (I := I) α x).transpose k j =
      ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i l *
          chartGramMatrix (I := I) g x x l k *
          chartAlphaCoBchange (I := I) α x j k := by
    intro k
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k, (chartAlphaCoBchange (I := I) α x *
            chartGramMatrix (I := I) g x x) i k *
        (chartAlphaCoBchange (I := I) α x).transpose k j) =
      ∑ k, ∑ l,
        chartAlphaCoBchange (I := I) α x i l *
          chartGramMatrix (I := I) g x x l k *
          chartAlphaCoBchange (I := I) α x j k from
    Finset.sum_congr rfl (fun k _ => h_inner k)]
  -- Swap order: ∑ k l A B = ∑ l k A B (i.e., relabel).
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-! ## Invertibility of P at `x` in the chart-α source

The chart-α basis at `x` is a basis of `T_x M` (since `x ∈ (chartAt H α).source`
implies `x ∈ baseSet α`). Hence the change-of-basis matrix `P` is invertible.

Concretely: from `G_α = P G_x P^T`, and the fact that `G_α` and `G_x` are both
invertible (positive-definite), we deduce that `P` is invertible. -/

/-- For `x ∈ (chartAt H α).source`, the chart-α Gram matrix at `x` is invertible. -/
private lemma chartGramMatrix_alpha_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    IsUnit (chartGramMatrix (I := I) g α x).det := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hpos := chartGramMatrix_posDef (I := I) g α hbase
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)

/-- For any `x : M`, the chart-x Gram matrix at `x` is invertible (since
`x ∈ baseSet x` always). -/
private lemma chartGramMatrix_x_isUnit
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsUnit (chartGramMatrix (I := I) g x x).det := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hpos := chartGramMatrix_posDef (I := I) g x hbase
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)

/-- The chart-α change-of-basis matrix at `x` (for `x ∈ (chartAt H α).source`)
is invertible, with determinant nonzero. We derive this from `G_α = P G_x P^T`. -/
private lemma chartAlphaCoBchange_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    IsUnit (chartAlphaCoBchange (I := I) α x).det := by
  classical
  -- From `G_α = P G_x P^T`, det(G_α) = det(P) det(G_x) det(P^T) = det(P)^2 det(G_x).
  -- Since det(G_α) ≠ 0 and det(G_x) ≠ 0, det(P) ≠ 0.
  have h_mat := chartGramMatrix_alpha_eq_PGPt_matrix (I := I) g α x
  -- Take det.
  have h_det : (chartGramMatrix (I := I) g α x).det =
      (chartAlphaCoBchange (I := I) α x).det *
        (chartGramMatrix (I := I) g x x).det *
        (chartAlphaCoBchange (I := I) α x).transpose.det := by
    rw [h_mat]
    rw [Matrix.det_mul, Matrix.det_mul]
  have h_det' : (chartGramMatrix (I := I) g α x).det =
      (chartAlphaCoBchange (I := I) α x).det^2 *
        (chartGramMatrix (I := I) g x x).det := by
    rw [h_det, Matrix.det_transpose]; ring
  have h_alpha := chartGramMatrix_alpha_isUnit (I := I) g α hx
  have h_x := chartGramMatrix_x_isUnit (I := I) g x
  have h_alpha_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
    h_alpha.ne_zero
  have h_x_ne : (chartGramMatrix (I := I) g x x).det ≠ 0 :=
    h_x.ne_zero
  rw [h_det'] at h_alpha_ne
  -- A^2 * b ≠ 0 ⇒ A ≠ 0.
  have hAne : (chartAlphaCoBchange (I := I) α x).det ≠ 0 := by
    intro hA0
    apply h_alpha_ne
    rw [hA0]
    ring
  exact isUnit_iff_ne_zero.mpr hAne

/-! ## Inverse-Gram identity: `P^T G_α^{-1} P = G_x^{-1}` -/

/-- The key matrix identity: in chart-α basis, the inverse Gram of `g_α` pulled
back by `P` equals the inverse Gram of `g_x`:
`P^T G_α^{-1} P = G_x^{-1}`.

This follows from `G_α = P G_x P^T` by inverting both sides. -/
private lemma PT_chartInvGram_alpha_P_eq_chartInvGram_x
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    (chartAlphaCoBchange (I := I) α x).transpose *
        chartInvGramMatrix (I := I) g α x *
        chartAlphaCoBchange (I := I) α x =
      chartInvGramMatrix (I := I) g x x := by
  classical
  -- From `G_α = P G_x P^T`, taking inverses:
  -- `G_α^{-1} = (P^T)^{-1} G_x^{-1} P^{-1}` (since (ABC)^{-1} = C^{-1} B^{-1} A^{-1}).
  -- Multiply by P^T on the left and P on the right:
  -- `P^T G_α^{-1} P = P^T (P^T)^{-1} G_x^{-1} P^{-1} P = G_x^{-1}`.
  set P : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartAlphaCoBchange (I := I) α x with hP_def
  set Gα : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α x with hGα_def
  set Gx : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g x x with hGx_def
  -- `Gα = P * Gx * Pᵀ`.
  have h_GalphaPGP : Gα = P * Gx * P.transpose :=
    chartGramMatrix_alpha_eq_PGPt_matrix (I := I) g α x
  -- Invertibility.
  have h_Galpha_det : IsUnit Gα.det := chartGramMatrix_alpha_isUnit (I := I) g α hx
  have h_Gx_det : IsUnit Gx.det := chartGramMatrix_x_isUnit (I := I) g x
  have h_P_det : IsUnit P.det := chartAlphaCoBchange_isUnit (I := I) g α hx
  have h_PT_det : IsUnit P.transpose.det := by
    rw [Matrix.det_transpose]; exact h_P_det
  -- Show: P^T * Gα^{-1} * P = Gx^{-1}.
  -- Strategy: show Gx * (P^T * Gα^{-1} * P) = 1 (right inverse) and
  -- (P^T * Gα^{-1} * P) * Gx = 1 (left inverse).
  -- Since Gx is invertible, this will give P^T * Gα^{-1} * P = Gx^{-1}.
  -- Approach: compute Gx * (P^T * Gα^{-1} * P) using h_GalphaPGP.
  -- Actually easier: Use h_GalphaPGP to express Gα^{-1}.
  -- From `Gα = P * Gx * P^T`, the inverse satisfies
  -- `Gα * Gα^{-1} = 1` and `Gα^{-1} * Gα = 1`.
  -- We claim: `Gα^{-1} = (P^T)^{-1} * Gx^{-1} * P^{-1}`.
  -- Check: `Gα * Gα^{-1} = (P * Gx * P^T) * ((P^T)^{-1} * Gx^{-1} * P^{-1}) =
  --   P * Gx * (P^T * (P^T)^{-1}) * Gx^{-1} * P^{-1} = P * Gx * Gx^{-1} * P^{-1} =
  --   P * P^{-1} = 1`. ✓
  --
  -- So `Gα^{-1} = (P^T)^{-1} * Gx^{-1} * P^{-1}`, i.e.
  -- `chartInvGramMatrix g α x = (P^T)^{-1} * chartInvGramMatrix g x x * P^{-1}`.
  -- Multiplying both sides by `P^T` on the left and `P` on the right:
  -- `P^T * chartInvGramMatrix g α x * P = P^T * (P^T)^{-1} * chartInvGramMatrix g x x * P^{-1} * P`
  --                                    = `chartInvGramMatrix g x x`.
  --
  -- Let's prove it by showing both sides agree after multiplication by Gx (and using cancellation).
  have h_Galpha_inv : chartInvGramMatrix (I := I) g α x * Gα = 1 := by
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hx
    exact chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase
  have h_Gx_inv : chartInvGramMatrix (I := I) g x x * Gx = 1 := by
    have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' x
    exact chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase
  -- Approach: show `(P^T * Gα^{-1} * P) * Gx = 1` using h_GalphaPGP and h_Galpha_inv.
  have h_target : (P.transpose * chartInvGramMatrix (I := I) g α x * P) * Gx = 1 := by
    -- Compute via reassociation:
    -- (P^T * Gα^{-1} * P) * Gx
    --   = P^T * (Gα^{-1} * P) * Gx           [mul_assoc P^T Gα^{-1} P]
    --   = P^T * ((Gα^{-1} * P) * Gx)         [mul_assoc P^T (Gα^{-1} * P) Gx]
    --   = P^T * (Gα^{-1} * (P * Gx))          [mul_assoc Gα^{-1} P Gx, inside]
    -- Use P * Gx = Gα * (P^T)⁻¹.
    -- Then = P^T * (Gα^{-1} * (Gα * (P^T)⁻¹))
    --     = P^T * ((Gα^{-1} * Gα) * (P^T)⁻¹)
    --     = P^T * (1 * (P^T)⁻¹)
    --     = P^T * (P^T)⁻¹ = 1.
    -- Step: P * Gx = Gα * (P^T)⁻¹.
    have h_PGx_eq : P * Gx = Gα * P.transpose⁻¹ := by
      have h := h_GalphaPGP
      have h_PT_inv_right :
          Gα * P.transpose⁻¹ = P * Gx * P.transpose * P.transpose⁻¹ := by
        rw [h]
      rw [Matrix.mul_assoc] at h_PT_inv_right
      have h_PT_inv : P.transpose * P.transpose⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ h_PT_det
      rw [h_PT_inv] at h_PT_inv_right
      rw [Matrix.mul_one] at h_PT_inv_right
      exact h_PT_inv_right.symm
    -- Now reassociate to expose `P * Gx`.
    rw [Matrix.mul_assoc P.transpose (chartInvGramMatrix (I := I) g α x) P]
    -- Now goal: P^T * (Gα^{-1} * P) * Gx = 1.
    rw [Matrix.mul_assoc P.transpose (chartInvGramMatrix (I := I) g α x * P) Gx]
    -- Now goal: P^T * ((Gα^{-1} * P) * Gx) = 1.
    rw [Matrix.mul_assoc (chartInvGramMatrix (I := I) g α x) P Gx]
    -- Now goal: P^T * (Gα^{-1} * (P * Gx)) = 1.
    rw [h_PGx_eq]
    -- Now goal: P^T * (Gα^{-1} * (Gα * (P^T)⁻¹)) = 1.
    rw [show chartInvGramMatrix (I := I) g α x * (Gα * P.transpose⁻¹) =
        (chartInvGramMatrix (I := I) g α x * Gα) * P.transpose⁻¹ from
      (Matrix.mul_assoc _ _ _).symm]
    rw [h_Galpha_inv]
    rw [Matrix.one_mul]
    exact Matrix.mul_nonsing_inv P.transpose h_PT_det
  -- Now we have `(P^T * Gα^{-1} * P) * Gx = 1`, hence `P^T * Gα^{-1} * P = Gx^{-1}`.
  -- Apply `mul_eq_one_comm` to flip the order, then use `Matrix.inv_eq_right_inv`.
  have h_target' : Gx * (P.transpose * chartInvGramMatrix (I := I) g α x * P) = 1 :=
    (mul_eq_one_comm).mp h_target
  -- From `Gx * (P^T * Gα^{-1} * P) = 1`, we get `Gx⁻¹ = P^T * Gα^{-1} * P`.
  have h_inv : (P.transpose * chartInvGramMatrix (I := I) g α x * P) = Gx⁻¹ :=
    (Matrix.inv_eq_right_inv h_target').symm
  rw [h_inv]
  rfl

/-! ## Pointwise inverse-Gram identity in summed form -/

/-- For each `a, c`, `∑_{ik} P_{ia} G_α^{ik} P_{kc} = G_x^{ac}`. This is the
entry-by-entry form of `P^T G_α^{-1} P = G_x^{-1}`. -/
private lemma sum_chartAlphaCoBchange_chartInvGramMatrix_alpha
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (a c : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartInvGramMatrix (I := I) g α x i k *
          chartAlphaCoBchange (I := I) α x k c =
      chartInvGramMatrix (I := I) g x x a c := by
  classical
  -- Use PT_chartInvGram_alpha_P_eq_chartInvGram_x and Matrix.mul_apply twice.
  have h := PT_chartInvGram_alpha_P_eq_chartInvGram_x (I := I) g α hx
  -- h : P^T * G_α^{-1} * P = G_x^{-1}.
  -- (P^T * G_α^{-1} * P) a c = ∑ k (P^T * G_α^{-1}) a k * P_{k c} = ∑ k ∑ i P^T_{a i} G_α^{ik} P_{kc}
  --                          = ∑ k ∑ i P_{i a} G_α^{ik} P_{kc}.
  have h_apply : (chartAlphaCoBchange (I := I) α x).transpose *
      chartInvGramMatrix (I := I) g α x *
      chartAlphaCoBchange (I := I) α x =
        chartInvGramMatrix (I := I) g x x := h
  -- Compute (P^T * G_α^{-1} * P) a c.
  have h_entry : ((chartAlphaCoBchange (I := I) α x).transpose *
      chartInvGramMatrix (I := I) g α x *
      chartAlphaCoBchange (I := I) α x) a c =
        chartInvGramMatrix (I := I) g x x a c := by
    rw [h_apply]
  rw [Matrix.mul_apply] at h_entry
  -- (∑ k (P^T * Gα^{-1}) a k * P a c k → ...): need to expand each (P^T * Gα^{-1}) a k.
  have h_expand : ∀ k : Fin (Module.finrank ℝ E),
      ((chartAlphaCoBchange (I := I) α x).transpose *
          chartInvGramMatrix (I := I) g α x) a k *
        chartAlphaCoBchange (I := I) α x k c =
      ∑ i : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartInvGramMatrix (I := I) g α x i k *
          chartAlphaCoBchange (I := I) α x k c := by
    intro k
    rw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ((chartAlphaCoBchange (I := I) α x).transpose *
          chartInvGramMatrix (I := I) g α x) a k *
        chartAlphaCoBchange (I := I) α x k c) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          chartAlphaCoBchange (I := I) α x i a *
            chartInvGramMatrix (I := I) g α x i k *
            chartAlphaCoBchange (I := I) α x k c from
    Finset.sum_congr rfl (fun k _ => h_expand k)] at h_entry
  -- Swap summation order.
  rw [Finset.sum_comm] at h_entry
  exact h_entry

/-! ## H-expansion in the chart-α basis: `H_{ij,α} = ∑_{ab} P_{ia} P_{jb} H_{ab,x}` -/

/-- The chart-α Hessian tensor admits a P-expansion against the chart-x Hessian
tensor at `x`:
`H_{ij,α}(x) = ∑_{ab} P_{ia}(x) P_{jb}(x) H_{ab,x}(x)`.

This follows from the chart-α matrix identity (`chartAlphaMatrixIdentity_holds`),
the chart-x matrix identity (`chartHessianMatrixIdentity_holds`), and bilinearity
of `abstractHessian` together with the model-basis decomposition of the chart-α
basis vectors. -/
private lemma chartHessianTensor_alpha_eq_P_chartHessianTensor_x
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M} (hx : x ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartHessianTensor (I := I) g α f i j x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartAlphaCoBchange (I := I) α x j b *
          chartHessianTensor (I := I) g x f a b x := by
  classical
  -- Step 1: by chart-α matrix identity, LHS = abstractHessian g f x (B_i_α) (B_j_α).
  have hM_alpha : chartAlphaMatrixIdentity (I := I) (M := M) g α f x :=
    chartAlphaMatrixIdentity_holds_chartSource (I := I) g α hf hx
  rw [← hM_alpha i j]
  -- Step 2: decompose B_i_α and B_j_α in the model basis.
  have hi := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x i
  have hj := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x j
  -- Chart-x matrix identity.
  have hM_x : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  -- Apply CLM bilinear expansion lemma.
  have h_expand :
      abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartAlphaCoBchange (I := I) α x j b *
          abstractHessian (I := I) g f x
            ((chartModelBasis E) a) ((chartModelBasis E) b) := by
    conv_lhs => rw [hi, hj]
    exact clm_bilinear_expand_two_sums (I := I)
      (abstractHessian (I := I) g f x)
      (Module.finrank ℝ E)
      (fun a => chartAlphaCoBchange (I := I) α x i a)
      (fun b => chartAlphaCoBchange (I := I) α x j b)
      (fun a => (chartModelBasis E) a)
      (fun b => (chartModelBasis E) b)
  rw [h_expand]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [hM_x a b]

/-! ## Main: chart-α Frobenius invariance

Substituting the P-expansion of H and using `P^T G_α^{-1} P = G_x^{-1}`,
the chart-α Frobenius squared equals the chart-x Frobenius squared. -/

/-! ## Reordering helper for nested sums

We use a single product-tuple representation. Both sides are sums over
`Fin n^8` with index permutations, and we relate them via `Finset.sum_bij`. -/

/-- Helper: an eightfold sum reordering from (i, j, k, l, a, b, c, d) to (a, b, c, d, i, k, j, l). -/
private lemma nested_sum_perm
    {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          f i j k l a b c d) := by
  classical
  -- Move ∑ a outermost by 4 sequential swaps.
  -- Step 1: ∑ ijkl ∑ a Z = ∑ ijk ∑ a ∑ l Z (swap ∑l ∑a at depth 4)
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  -- Step 2: ∑ ijk ∑ a Z = ∑ ij ∑ a ∑ k Z
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  -- Step 3: ∑ ij ∑ a ... = ∑ i ∑ a ∑ j ...
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  -- Step 4: ∑ i ∑ a ... = ∑ a ∑ i ...
  rw [show (∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    rw [Finset.sum_comm]]
  -- Now move ∑ b to position 2. Similar 4 swaps.
  -- The body is now ∑ a ∑ i ∑ j ∑ k ∑ l ∑ b ∑ c ∑ d.
  -- Move ∑ b from position 6 to position 2: 4 swaps.
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.sum_comm]]
  -- Move ∑ c to position 3. ∑ c is now at position 7 (after a, b, i, j, k, l).
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ c : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ c : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [Finset.sum_comm]]
  -- Move ∑ d to position 4. ∑ d is now at position 8.
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ d : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ d : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ d : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ d : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ d : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ d : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Finset.sum_comm]]
  -- Now swap (j, k) at the right depth (depth 6).
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro c _
  refine Finset.sum_congr rfl ?_
  intro d _
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_comm]

/-- **Chart-α Frobenius invariance (unconditional on the chart-α source).**
For `f : M → ℝ` smooth and `x ∈ (chartAt H α).source`, the chart-α tensor
Frobenius squared equals the chart-x Frobenius squared.

The proof strategy:
- Substitute `H_{ij,α} = ∑_{ab} P_{ia} P_{jb} H_{ab,x}` in the chart-α Frobenius squared.
- Reorganize the resulting eightfold sum using `nested_sum_perm`.
- Factor as `(∑_{ik} P_{ia} G_α^{ik} P_{kc})(∑_{jl} P_{jb} G_α^{jl} P_{ld}) H_{ab,x} H_{cd,x}`.
- Apply the inverse-Gram identity to get `G_x^{ac} G_x^{bd}`. -/
theorem chartFrobeniusInvariance_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartFrobeniusInvariance (I := I) (M := M) g α f x := by
  classical
  -- Abbreviations.
  set n := Module.finrank ℝ E with hn_def
  set Gα : Fin n → Fin n → ℝ :=
    fun i k => chartInvGramMatrix (I := I) g α x i k with hGα_def
  set Gx : Fin n → Fin n → ℝ :=
    fun a c => chartInvGramMatrix (I := I) g x x a c with hGx_def
  set Hα : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f i j x with hHα_def
  set Hx : Fin n → Fin n → ℝ :=
    fun a b => chartHessianTensor (I := I) g x f a b x with hHx_def
  set P : Fin n → Fin n → ℝ :=
    fun i a => chartAlphaCoBchange (I := I) α x i a with hP_def
  -- The inverse-Gram identity in summed form.
  have h_inverse : ∀ a c : Fin n,
      ∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c = Gx a c :=
    fun a c => sum_chartAlphaCoBchange_chartInvGramMatrix_alpha (I := I) g α hx a c
  -- The H-expansion identity for the chart-α tensor Hessian.
  have h_H : ∀ i j : Fin n,
      Hα i j = ∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b :=
    fun i j => chartHessianTensor_alpha_eq_P_chartHessianTensor_x (I := I) g α hf hx i j
  -- Rewrite the goal in terms of the abbreviations.
  rw [chartFrobeniusInvariance_def]
  rw [chartHessFrobeniusSqOnChartAlpha_def, chartHessFrobeniusSq_def]
  change (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            Gα i k * Gα j l * Hα i j * Hα k l) =
         (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
            Gx a c * Gx b d * Hx a b * Hx c d)
  -- Substitute Hα = ∑ ab P_ia P_jb Hx_ab in LHS to get an eightfold sum.
  have h_LHS_eq : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        Gα i k * Gα j l * Hα i j * Hα k l) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
            Hx a b * Hx c d) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [h_H i j, h_H k l]
    -- The LHS is (((Gα * Gα) * (∑ ab Z_ab)) * (∑ cd W_cd)).
    -- Each `(∑ ...) * ...` and `... * (∑ ...)` can be distributed.
    -- For each step, use a fresh `have` to explicitly state the transformation.
    -- Step 1: pull ∑ a out of the first inner sum.
    -- LHS shape: ((X * (∑ a (∑ b ...))) * (∑ c ...)). We want ∑ a (X * (∑ b ...) * (∑ c ...)).
    have h_step1 : Gα i k * Gα j l * (∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ a : Fin n,
          Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) := by
      -- The expression is ((Gα*Gα) * (∑a (∑b))) * (∑c).
      -- We want: ∑a (Gα*Gα * (∑b)) * (∑c) = ∑a ((Gα*Gα * (∑b)) * (∑c)).
      -- First absorb the outer sum: distribute ∑a (X(a) * (∑c)) = (∑a X(a)) * (∑c) for X(a) = Gα*Gα*∑b.
      -- So we use: ∑a (Y(a) * S) = (∑a Y(a)) * S (Finset.sum_mul reversed).
      conv_lhs =>
        rw [show (Gα i k * Gα j l * (∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b)) =
              ∑ a : Fin n, Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) from by
          rw [Finset.mul_sum]]
      rw [Finset.sum_mul]
    rw [h_step1]
    refine Finset.sum_congr rfl ?_
    intro a _
    -- Step 2: pull ∑ b out.
    have h_step2 : Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ b : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) := by
      conv_lhs =>
        rw [show (Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b)) =
              ∑ b : Fin n, Gα i k * Gα j l * (P i a * P j b * Hx a b) from by
          rw [Finset.mul_sum]]
      rw [Finset.sum_mul]
    rw [h_step2]
    refine Finset.sum_congr rfl ?_
    intro b _
    -- Step 3: pull ∑ c out.
    have h_step3 : Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ c : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ d : Fin n, P k c * P l d * Hx c d) := by
      rw [Finset.mul_sum]
    rw [h_step3]
    refine Finset.sum_congr rfl ?_
    intro c _
    -- Step 4: pull ∑ d out.
    have h_step4 : Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ d : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) * (P k c * P l d * Hx c d) := by
      rw [Finset.mul_sum]
    rw [h_step4]
    refine Finset.sum_congr rfl ?_
    intro d _
    ring
  rw [h_LHS_eq]
  -- Now LHS is the eightfold sum. Reorder so that (a, b, c, d) are outermost.
  rw [nested_sum_perm (fun i j k l a b c d =>
    (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) * Hx a b * Hx c d)]
  -- Now LHS is ∑ abcd ∑ ikjl (P_ia*Gα_ik*P_kc)*(P_jb*Gα_jl*P_ld)*Hx_ab*Hx_cd.
  -- Factor: ∑ ikjl X_ik*Y_jl*Hx_ab*Hx_cd = (∑ ik X_ik)*(∑ jl Y_jl)*Hx_ab*Hx_cd.
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro c _
  refine Finset.sum_congr rfl ?_
  intro d _
  -- Goal: ∑ i k j l (P_ia * Gα_ik * P_kc) * (P_jb * Gα_jl * P_ld) * Hx_ab * Hx_cd
  --     = Gx_ac * Gx_bd * Hx_ab * Hx_cd.
  have h_factor : (∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
          Hx a b * Hx c d) =
      (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
        (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
        Hx a b * Hx c d := by
    -- Move (∑ jl) outside (∑ ik): independent variables.
    have h1 : (∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
            Hx a b * Hx c d) =
        (∑ i : Fin n, ∑ k : Fin n,
          (P i a * Gα i k * P k c) *
            (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
            Hx a b * Hx c d) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro k _
      -- Goal at (i, k): ∑ j l, X * Y_jl * Hx_ab * Hx_cd = X * (∑ j l, Y_jl) * Hx_ab * Hx_cd.
      rw [show (∑ j : Fin n, ∑ l : Fin n,
              (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
                Hx a b * Hx c d) =
            (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d from by
        rw [show (P i a * Gα i k * P k c) *
                (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) =
              ∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]]
        rw [show ((∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d)) * Hx a b * Hx c d) =
              ∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) * Hx a b * Hx c d from by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.sum_mul, Finset.sum_mul]]]
    rw [h1]
    -- Now pull (∑ ik) outside.
    rw [show (∑ i : Fin n, ∑ k : Fin n,
            (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d) =
          (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
            (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
            Hx a b * Hx c d from by
      rw [show (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) =
            ∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) from by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]]
      rw [show ((∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
                (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d)) * Hx a b * Hx c d) =
            ∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d from by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul, Finset.sum_mul]]]
  rw [h_factor]
  rw [h_inverse a c, h_inverse b d]

/-! ## Packaging: chart-α HS bridge Prop holds -/

/-- **Chart-α HS bridge Prop holds.** For `f : M → ℝ` smooth and
`x ∈ (chartAt H α).source`, the chart-α HS bridge Prop holds. -/
theorem chartFrobeniusSqHSBridge_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartFrobeniusSqHSBridge (I := I) (M := M) g α f x := by
  classical
  rw [chartFrobeniusSqHSBridge_def]
  have h_inv := chartFrobeniusInvariance_holds (I := I) g α hf hx
  rw [chartFrobeniusInvariance_def] at h_inv
  rw [h_inv]
  exact (frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x).symm

/-! ## Bridge identity for `smoothTensorPairingChart` (unconditional, smooth) -/

/-- **Unconditional bridge: chart-α tensor pairing equals chart-invariant pairing.**
For smooth `φ : C^∞⟮I, M; ℝ⟯` and `v : SmoothScalar g`, and `y ∈ chartTargetEuclid α`,
the chart-α tensor pairing on `EuclN` equals the chart-invariant Hess pairing on
`M` at the pulled-back point. -/
theorem smoothTensorPairingChart_eq_hessPairingChart_pullback
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set x_y : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_y_def
  -- Establish hx_y : x_y ∈ (chartAt H α).source.
  have hx_y_chart : x_y ∈ (chartAt H α).source := by
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have hx_y_source_ext : x_y ∈ (extChartAt I α).source := by
      rw [hx_y_def]
      exact (extChartAt I α).map_target hy_target
    rwa [extChartAt_source_eq_chartAt_source] at hx_y_source_ext
  -- HS bridges for φ ± v.
  have h_HS_add : chartFrobeniusSqHSBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z + v.toFun z) x_y := by
    have hf_add : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z + v.toFun z) :=
      φ.contMDiff.add v.smooth
    exact chartFrobeniusSqHSBridge_holds (I := I) g α hf_add hx_y_chart
  have h_HS_sub : chartFrobeniusSqHSBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z - v.toFun z) x_y := by
    have hf_sub : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z - v.toFun z) :=
      φ.contMDiff.sub v.smooth
    exact chartFrobeniusSqHSBridge_holds (I := I) g α hf_sub hx_y_chart
  -- Symmetry-swap auxiliary.
  have h_swap_aux := chartAlpha_swap_aux_holds (I := I) g α (φ : M → ℝ) v.toFun x_y
  -- Apply the packaged bridge.
  exact smoothTensorPairingChart_eq_hessPairingChart_of_HSBridge
    (I := I) (M := M) g α φ v hy h_HS_add h_HS_sub h_swap_aux

end HessianChartAlphaFrobenius
end Laplacian
end Analysis
end DifferentialGeometry

end
