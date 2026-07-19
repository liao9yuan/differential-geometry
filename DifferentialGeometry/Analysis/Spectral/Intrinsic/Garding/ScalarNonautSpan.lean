import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarFluxJetBound

/-!
# Uniform scalar nonautonomous estimates on compact time spans

This file upgrades the local fixed-background metric-difference estimate to a
single prescribed radius on a compact regular-time interval.  It is the first
producer needed to replay the scalar Galerkin construction on a finite interior
time slab without repeatedly choosing unrelated existential lifetimes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- A compact regular-time interval has one backward radius on which every
frozen-background metric difference is quarter-small and has a common spatial
jet envelope at that frozen time. -/
theorem metricDiff_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h,
              ((T : ℝ) - s ∈ D.regular) ∧
              gFibreOpBound (I := I) (G.metric (T : ℝ))
                (ccTensorBilinSymm (I := I) (G.metric (T : ℝ))
                  (metricDifferenceCcTensor (I := I) (M := M)
                    (G.metric (T : ℝ)) (G.metric ((T : ℝ) - s))))
                (1 / 4 : ℝ) ∧
              ∀ i x,
                riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ))
                    0 (2 + i) x
                    ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 2 i
                      (metricDifferenceCcTensor (I := I) (M := M)
                        (G.metric (T : ℝ))
                        (G.metric ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨ρ₀, hρ₀, hmetric⟩ :=
    DifferentialGeometry.HCGCompactness.metric_c1_span
      (I := I) G hG hab (by norm_num : (0 : ℝ) < 1 / 4)
  let ρ : ℝ := min 1 ρ₀
  have hρ : 0 < ρ := lt_min one_pos hρ₀
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρ₀' : ρ ≤ ρ₀ := min_le_right _ _
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let K : Set ℝ := Set.Icc ((T : ℝ) - h) (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t ↦
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKreg : K ⊆ D.regular := by
    intro t ht
    apply hab
    dsimp only [K] at ht
    exact ⟨hleft.trans ht.1, ht.2.trans hT.2⟩
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ ↦ TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M ↦ TensorRSSpace 0 2 I z) p.1
        ((P p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    sorry
  obtain ⟨B, hB, hjet⟩ := joint_jet_bdd (I := I) (M := M) q 0 2 P
    hK hKreg hPjoint
  refine ⟨B, hB, ?_⟩
  intro s hs
  have htK : (T : ℝ) - s ∈ K := by
    constructor <;> dsimp only [K] <;> linarith [hs.1, hs.2]
  have hvar : (T : ℝ) - s ∈ Set.Icc a b := by
    exact ⟨hleft.trans htK.1, htK.2.trans hT.2⟩
  have hdist : |((T : ℝ) - s) - (T : ℝ)| ≤ ρ₀ := by
    rw [show ((T : ℝ) - s) - (T : ℝ) = -s by ring, abs_neg,
      abs_of_nonneg hs.1]
    exact hs.2.trans (hhρ.trans hρ₀')
  have hsup := hmetric (T : ℝ) hT ((T : ℝ) - s) hvar hdist
  have hbound : gFibreOpBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    have hnorm :
        DifferentialGeometry.HCGCompactness.metricDerivNorm (I := I) 0
          (G.metric ((T : ℝ) - s)) q q y ≤ 1 / 4 := by
      exact (DifferentialGeometry.HCGCompactness.derivNorm_le_sup
        (I := I) (K := Set.univ) isCompact_univ (a := 0) (p := 1)
        (by omega) (G.metric ((T : ℝ) - s)) q q (Set.mem_univ y)).trans
        (by simpa only [q] using hsup)
    have heval := DifferentialGeometry.HCGCompactness.metricDiff_abs_le
      (I := I) (G.metric ((T : ℝ) - s)) q q y v w
    have hfinal :
        |(G.metric ((T : ℝ) - s)).inner y v w - q.inner y v w| ≤
          (1 / 4 : ℝ) * Real.sqrt (q.inner y v v) *
            Real.sqrt (q.inner y w w) :=
      heval.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
    simpa only [q, P, ContinuousLinearMap.sub_apply] using hfinal
  refine ⟨hab hvar, ?_, ?_⟩
  · simpa only [q, P] using hbound
  · intro i x
    simpa only [q, P] using hjet i ((T : ℝ) - s) htK x

/-- The metric-difference span radius also gives an order-dependent uniform
jet envelope for the exact scalar-flux coefficient on every admissible
backward interval. -/
theorem scalarFlux_span
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {a b : ℝ} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : ℝ) ∈ Set.Icc a b →
        ∀ h : ℝ, 0 < h → h ≤ ρ → a ≤ (T : ℝ) - h →
          ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
            ∀ s ∈ Set.Icc (0 : ℝ) h, ∀ i x,
              riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ))
                  1 (1 + i) x
                  ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 1 1 i
                    (scalarFluxCoeff (I := I) (G.metric (T : ℝ))
                      (G.metric ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨ρ, hρ, hρone, hspan⟩ := metricDiff_span (I := I) (M := M) G hG hab
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  obtain ⟨J, hJ, hdata⟩ := hspan T hT h hh hhρ hleft
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t ↦
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  obtain ⟨C, hC, hflux⟩ :=
    scalarFlux_jet_grid (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨fun i ↦
    C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i,
    fun i ↦ mul_nonneg (hC i)
      (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ i), ?_⟩
  intro s hs i x
  have hsdata := hdata s hs
  have htie : ∀ y v w,
      (G.metric ((T : ℝ) - s)).inner y v w =
        q.inner y v w + ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s)) y v w := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hbound : gFibreOpBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    simpa only [q, P] using hsdata.2.1
  have hlocal := hflux (G.metric ((T : ℝ) - s)) (P ((T : ℝ) - s)) htie
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hbound i x
  have hgrid :
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
          (fun j ↦ riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
            ((iteratedCovGrad (I := I) q 0 2 j (P ((T : ℝ) - s))).toSection x)) i ≤
        DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i := by
    rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid,
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid]
    refine Finset.sum_le_sum (fun n _ ↦ Finset.sum_le_sum (fun e _ ↦ ?_))
    exact Finset.prod_le_prod
      (fun m _ ↦ riemannianFiberNormSq_nonneg
        (I := I) (M := M) q 0 (2 + e m) x _)
      (fun m _ ↦ by simpa only [q, P] using hsdata.2.2 (e m) x)
  exact hlocal.trans (mul_le_mul_of_nonneg_left hgrid (hC i))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
