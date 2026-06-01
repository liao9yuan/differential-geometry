import DifferentialGeometry.Integral.Connection.RawConnLapChartProjFullExpansionViaChartInvGram
import DifferentialGeometry.Integral.Connection.CovApplyFrameToCoordExpansion

/-!
# Chart-α Leibniz remainder equals the pure first-derivative-in-`T₀` cross term

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a chart
base point `α : M`, and component multi-indices `(Idx, Jdx)`, this file ships
the identity that the chart-α Leibniz remainder
`chartLeibnizRemainder g r s α T₀ Idx Jdx b`, defined in
`RawConnLapChartProjFullExpansionViaChartInvGram` as the algebraic difference

```
chartFrameCoordMatrixWeightedDoubleSum b - chartInvGramPrincipalSum b
```

between the predecessor's chart-α frame-coordinate-matrix-weighted double sum
over `(i, l)` and the chart-α inverse-Gram-matrix-weighted principal sum over
`(k, l)`, equals at any base point `b` in the chart-α partition-of-unity
tsupport intersected with the chart-α Levi-Civita good set the pure
*first-derivative-in-`T₀`* triple sum

```
Σ_{i, l, k} C^l_i(b) · (∂_l · C^k_i)(b) ·
  π_(Idx, Jdx)[(covApply cov_RS ∂_k T₀) b],
```

where `C^l_i := chartFrameNormGlobalSmoothCoordMatrix g α i l`,
`(∂_l · C^k_i)(b) := extDerivFun (C^k_i) b (∂_l b)`, and `π_(Idx, Jdx)` is the
chart-α `(Idx, Jdx)` component projection through the canonical chart-α
trivialization.

The proof combines:

* the **Leibniz expansion** of `cov_RS (covApply cov_RS B^α_i T₀) b (∂_l b)` in
  the chart-α coordinate basis (file `CovApplyFrameToCoordExpansion`,
  theorem `cov_RS_covApply_frameVec_eq_coord_expansion`);
* the **orthonormality contraction** `Σ_i C^k_i(b) · C^l_i(b) =
  chartInvGramMatrix g α b k l` (file
  `ChartFrameNormGlobalSmoothCoordBasisExpansion`,
  theorem `chartFrameNormGlobalSmoothCoordMatrix_orthonormality`);
* the `ℝ`-bilinearity of the component projection through the
  chart-α trivialization.

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter NormedSpace
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Headline

Chart-α Leibniz remainder equals the first-derivative-in-`T₀` cross term. -/

/-- **Chart-α Leibniz remainder equals the pure first-derivative-in-`T₀`
cross term.**

At a base point `b` lying in the chart-α partition-of-unity tsupport
intersected with the chart-α Levi-Civita good set, the chart-α Leibniz
remainder equals the triple sum

```
Σ_{i, l, k} C^l_i(b) · (∂_l · C^k_i)(b) ·
  π_(Idx, Jdx)[(covApply cov_RS ∂_k T₀) b]
```

where `C^l_i = chartFrameNormGlobalSmoothCoordMatrix g α i l`,
`(∂_l · C^k_i)(b) = extDerivFun (C^k_i) b (∂_l b)`, and `π_(Idx, Jdx)` is the
chart-α `(Idx, Jdx)` component projection through the canonical chart-α
trivialization. -/
theorem chartLeibnizRemainder_eq_firstDerivOnly
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              (extDerivFun (I := I) (fun z : M =>
                  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                    g α i k z) b
                  (chartBasisVecFiber (I := I) α l b)) *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b)) := by
  classical
  -- Abbreviations.
  set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_RS_def
  set triv := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with htriv_def
  set proj : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      (triv.continuousLinearMapAt ℝ b) with hproj_def
  -- Per-(i,l) shorthand for the projected value
  -- of `cov_RS (covApply cov_RS ∂_k T₀) b ∂_l`.
  -- Per-`k` shorthand for the projected value of `covApply cov_RS ∂_k T₀ b`.
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  have hb_pou : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb.1
  -- Step A: invoke the Leibniz expansion lemma for each `(i, l)`.
  have hExpand := cov_RS_covApply_frameVec_eq_coord_expansion
    (I := I) (M := M) g r s α T₀
  -- Step B: unfold definitions of remainder, frame-weighted sum, principal sum.
  unfold chartLeibnizRemainder chartFrameCoordMatrixWeightedDoubleSum
    chartInvGramPrincipalSum
  -- Step C: rewrite each frame-weighted summand at `(i, l)` using `hExpand`.
  -- The inner content is `C^l_i · proj[cov_RS (covApply B^α_i T₀) b (∂_l b)]`.
  have hproj_lin_smul (c : ℝ) (v : TensorRSSpace r s I b) :
      proj (c • v) = c * proj v := by
    simp [hproj_def]
  have hproj_lin_add (v w : TensorRSSpace r s I b) :
      proj (v + w) = proj v + proj w := by
    simp [hproj_def]
  -- Step D: replace each inner proj[…] for `i, l` by the RHS of `hExpand`.
  have hInner_rewrite (i l : Fin (Module.finrank ℝ E)) :
      proj ((cov_RS).toFun
            (covApply cov_RS
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun z : M => T₀.toSection z)) b
            (chartBasisVecFiber (I := I) α l b)) =
        (∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b))) +
        (∑ k : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (fun z : M =>
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z)
              b (chartBasisVecFiber (I := I) α l b)) *
            proj (covApply cov_RS
              (fun z : M => chartBasisVecFiber (I := I) α k z)
              (fun z : M => T₀.toSection z) b)) := by
    have h := hExpand (i := i) (b := b) hb_good l
    -- Apply `π` (a CLM) to both sides.
    have hprojH := congrArg proj h
    -- Distribute `π` over the RHS sum + sum.
    -- proj (A + B) = proj A + proj B
    rw [hproj_lin_add] at hprojH
    -- Distribute `π` over each finset sum and pull out the scalar coefficients.
    have hsum1 :
        proj (∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
              (cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) =
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
              proj ((cov_RS).toFun
                  (covApply cov_RS
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)) := by
      rw [map_sum proj]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact hproj_lin_smul _ _
    have hsum2 :
        proj (∑ k : Fin (Module.finrank ℝ E),
            (extDerivFun (I := I) (fun z : M =>
                chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                  g α i k z) b (chartBasisVecFiber (I := I) α l b)) •
              covApply cov_RS
                (fun z : M => chartBasisVecFiber (I := I) α k z)
                (fun z : M => T₀.toSection z) b) =
          ∑ k : Fin (Module.finrank ℝ E),
            (extDerivFun (I := I) (fun z : M =>
                chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                  g α i k z) b (chartBasisVecFiber (I := I) α l b)) *
              proj (covApply cov_RS
                (fun z : M => chartBasisVecFiber (I := I) α k z)
                (fun z : M => T₀.toSection z) b) := by
      rw [map_sum proj]
      refine Finset.sum_congr rfl ?_
      intro k _
      exact hproj_lin_smul _ _
    rw [hsum1, hsum2] at hprojH
    exact hprojH
  -- Step E: rewrite the frame-weighted double sum.
  -- The frame-weighted double sum on the LHS is:
  --   Σ_{i, l} C^l_i(b) · proj[cov_RS (covApply B^α_i T₀) b ∂_l]
  -- Substitute via `hInner_rewrite` to obtain:
  --   Σ_{i, l, k} C^l_i · C^k_i · proj[cov_RS (covApply ∂_k T₀) b ∂_l]  (principal)
  -- + Σ_{i, l, k} C^l_i · (∂_l C^k_i) · proj[covApply ∂_k T₀ b]          (cross)
  -- Then collapse principal via orthonormality.
  set Z₁ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ := fun i l k =>
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
      proj ((cov_RS).toFun
          (covApply cov_RS
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z)) b
          (chartBasisVecFiber (I := I) α l b)) with hZ₁_def
  set Z₂ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ := fun i l k =>
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
      (extDerivFun (I := I) (fun z : M =>
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z) b
          (chartBasisVecFiber (I := I) α l b)) *
      proj (covApply cov_RS
        (fun z : M => chartBasisVecFiber (I := I) α k z)
        (fun z : M => T₀.toSection z) b) with hZ₂_def
  -- Rewrite the LHS frame-weighted double sum.
  have hFrameDS_eq :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) := by
    -- For each (i, l), substitute the inner proj expansion.
    have hper (i l : Fin (Module.finrank ℝ E)) :
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
          proj ((cov_RS).toFun
              (covApply cov_RS
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)) =
          (∑ k, Z₁ i l k) + (∑ k, Z₂ i l k) := by
      rw [hInner_rewrite i l]
      rw [mul_add]
      congr 1
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp only [hZ₁_def]
        ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        simp only [hZ₂_def]
        ring
    -- Sum hper over (i, l).
    have hOuter :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              proj ((cov_RS).toFun
                  (covApply cov_RS
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)) =
          ∑ i, ∑ l, ((∑ k, Z₁ i l k) + (∑ k, Z₂ i l k)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro l _
      exact hper i l
    rw [hOuter]
    -- Now distribute the addition over the double sum.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ((∑ k, Z₁ i l k) + (∑ k, Z₂ i l k))) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]]
  -- Step F: collapse the principal Σ_i C^l_i · C^k_i sum via orthonormality.
  -- Σ_i C^l_i(b) · C^k_i(b) = Σ_i C^k_i(b) · C^l_i(b) = chartInvGramMatrix g α b k l.
  have hOrtho (k l : Fin (Module.finrank ℝ E)) :
      ∑ i : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
              g α i k b =
        chartInvGramMatrix (I := I) g α b k l := by
    have h := chartFrameNormGlobalSmoothCoordMatrix_orthonormality
      (I := I) (M := M) g α (b := b) hb_pou hb_good k l
    -- The orthonormality identity says: Σ_i C^k_i · C^l_i = chartInvGramMatrix b k l.
    rw [← h]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  -- The principal triple sum reorganizes by sum_comm and the orthonormality identity.
  have hPrincipal_collapse :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartBasisVecFiber (I := I) α k)
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b))) := by
    -- First, rewrite the LHS as Σ_k Σ_l Σ_i Z₁_i_l_k via Finset.sum_comm.
    -- Use Z₁ to first absorb the i-sum into the multiplier.
    have hZ₁_factor (i l k : Fin (Module.finrank ℝ E)) :
        Z₁ i l k =
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
              g α i k b) *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) := by
      simp only [hZ₁_def]
    -- Reorder the triple sum from (i, l, k) to (k, l, i) by three swaps.
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k) from by
      -- (i, l, k): swap inner two: ∑i ∑l ∑k -> ∑i ∑k ∑l
      have h1 :
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_comm]
      -- swap outer two: ∑i ∑k -> ∑k ∑i
      have h2 :
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        rw [Finset.sum_comm]
      -- swap inner two: ∑i ∑l -> ∑l ∑i
      have h3 :
          (∑ k : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E), Z₁ i l k) =
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.sum_comm]
      rw [h1, h2, h3]]
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    -- The inner sum Σ_i Z₁ i l k = (Σ_i C^l_i · C^k_i) · proj[...].
    have hFactor :
        ∑ i : Fin (Module.finrank ℝ E), Z₁ i l k =
          (∑ i : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i k b) *
            proj ((cov_RS).toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) := by
      rw [Finset.sum_mul]
    rw [hFactor]
    rw [hOrtho]
    -- The proj[...] LHS equals the unfolded tensorChartComponentProjection on the
    -- RHS after re-folding through `hproj_def`, `htriv_def`, `hcov_RS_def`.
    simp only [hproj_def, htriv_def, hcov_RS_def, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
  -- Step G: the cross sum equals the headline RHS.
  have hCross_collapse :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), Z₂ i l k) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                (extDerivFun (I := I) (fun z : M =>
                    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                      g α i k z) b
                    (chartBasisVecFiber (I := I) α l b)) *
                tensorChartComponentProjection (E := E) r s Idx Jdx
                  ((trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (fun z : M => chartBasisVecFiber (I := I) α k z)
                      (fun z : M => T₀.toSection z) b)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [hZ₂_def, hproj_def, htriv_def, hcov_RS_def,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Step H: assemble. The unfolded LHS (frame-weighted DS minus principal sum)
  -- becomes (principal triple + cross triple) minus principal sum, which is
  -- the cross triple, i.e. the headline RHS.
  -- Recast hFrameDS_eq using `π`-notation for the principal sum.
  -- The LHS we need to compute is:
  --   frame-weighted DS  -  Σ_{k, l} chartInvGramMatrix g α b k l · proj[...]
  -- where the principal-sum content matches `hPrincipal_collapse` precisely.
  -- Substitute.
  change (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) -
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartBasisVecFiber (I := I) α k)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) = _
  -- The frame-weighted DS in the goal uses `π v = tensorChartComponentProjection ...`.
  -- These match `π` modulo the `hproj_def, htriv_def, hcov_RS_def` setting.
  have hFrameDS_eq' :
      (∑ i : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b)))) =
        (∑ i, ∑ l, ∑ k, Z₁ i l k) + (∑ i, ∑ l, ∑ k, Z₂ i l k) := by
    have hRewrite :
        (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                tensorChartComponentProjection (E := E) r s Idx Jdx
                  ((trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g)).toFun
                      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g))
                        (chartFrameNormGlobalSmooth (I := I) (M := M)
                          g α i).toFun
                        (fun z : M => T₀.toSection z)) b
                      (chartBasisVecFiber (I := I) α l b)))) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                g α i l b *
                proj ((cov_RS).toFun
                    (covApply cov_RS
                      (chartFrameNormGlobalSmooth (I := I) (M := M)
                        g α i).toFun
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b))) := by
      simp only [hproj_def, htriv_def, hcov_RS_def, ContinuousLinearMap.coe_comp',
        Function.comp_apply]
    rw [hRewrite]
    exact hFrameDS_eq
  rw [hFrameDS_eq']
  -- Rewrite the principal sum (the subtrahend) using `hPrincipal_collapse`.
  rw [← hPrincipal_collapse]
  -- Now the goal is:
  --   ((Σ_{ilk} Z₁) + (Σ_{ilk} Z₂)) - (Σ_{ilk} Z₁) = Σ_{ilk} (cross-content)
  -- with the cross-content equal to Σ_{ilk} Z₂ via `hCross_collapse`.
  rw [← hCross_collapse]
  ring

section
#print axioms
  DifferentialGeometry.Integral.Connection.chartLeibnizRemainder_eq_firstDerivOnly
end

end Connection
end Integral
end DifferentialGeometry

end
