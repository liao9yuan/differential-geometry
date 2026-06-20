import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckRicciArm

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

private lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_sub]

private theorem appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Ψ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ - Ψ) W =
      appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ W).toSection x
        - (appCc (I := I) (M := M) g r s Ψ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ - Ψ).toSection x : TensorRSSpace r s I x) = Φ.toSection x - Ψ.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

private lemma unitModel_smul_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (W : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • W) x =
      c • unitModel (I := I) (M := M) g s W x := by
  rw [unitModel, unitModel]
  have hsec : (c • W).toSection x = c • W.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • W).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_smul]

private theorem appCc_smul_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in

private theorem jointRSsmul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

private theorem appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r) {S : Set ℝ}
    {x : M} (hΨ : ContinuousOn (fun s : ℝ => TensorRSSpace.toModel ((Ψ s).toSection x)) S)
    (v : Fin 2 → TangentSpace I x) :
    ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v) S := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have key : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v =
        ((TensorRSSpace.toModel ((Ψ s).toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Ψ s).toSection x) u]
  have hchain : Continuous (fun T : Tensor0SBundle.TensorRSModel r 2 ℝ E =>
      (T (Tensor0SBundle.Tensor0SSpace.toModel u)) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp
      (ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (Tensor0SBundle.Tensor0SSpace.toModel u)).continuous
  exact (hchain.comp_continuousOn hΨ).congr (fun s _ => (key s).symm)

private theorem deriv_realizedRicciChartSum_eq_rebased_chartSymbol
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    ∃ h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E,
      IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
            (I := I) g₀ T T' hδ hδ' x v w) s =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
              (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart (I := I)
                  (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                    (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                  (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                    (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x)) := by
  classical
  
  obtain ⟨h, gfam, hfam, hvel, hlocRic, _hloc⟩ :=
    exists_rebased_cutoffMetricPerturbationFamily (I := I) g₀ g₀ T T' hδ_lt hδ hδ'_lt hδ' hs x
  refine ⟨h, hvel, ?_⟩
  set gs : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  set y₀ : E := extChartAt I x x with hy₀
  have hy : y₀ ∈ interior (extChartAt I x).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  set Pval : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart (I := I)
        gs x h i k y₀ +
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
        (I := I) gs x h i k y₀ with hPval
  
  have hper : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
          x i k y₀)
        (Pval i k) s := by
    intro i k
    
    have hsplit : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (gfam σ) x i k y₀) (Pval i k) 0 := by
      rw [hPval, hgs]
      exact DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.hasDerivAt_chartRicciTensor
        (I := I) hfam i k hy
    
    have htrans : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + σ))
          x i k y₀)
        (Pval i k) 0 :=
      hsplit.congr_of_eventuallyEq (hlocRic i k).symm
    have htrans' : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + σ))
          x i k y₀)
        (Pval i k) (s - s) := by
      rwa [sub_self]
    have hsub := htrans'.comp_sub_const s s
    have hcongr : (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + (t - s)))
          x i k y₀) =
        (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
          x i k y₀) := by
      funext t; rw [add_sub_cancel]
    rwa [hcongr] at hsub
  
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
            x i k y₀)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i * (Pval i k)) s := by
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact (hper i k).const_mul _
  have hfun : DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
        (I := I) g₀ T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
            x i k y₀) := by
    funext t
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum, hy₀]
  rw [hfun]
  exact hsum.deriv

private theorem bareChartRicci_threeSlot_appCc_covariantTransfer
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Q₀fib : ℝ → SmoothCcTensor g₀ 2 2) (Q₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (Q₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x)
          (h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E),
          IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                  DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Q₀fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Q₁fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Q₂fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 ((Q₀fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 ((Q₁fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 ((Q₂fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₀fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₁fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₂fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) :=
  sorry

private theorem exists_negTwoRicciArm_chartSymbolSum_appCc_families
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀fib : ℝ → SmoothCcTensor g₀ 2 2) (P₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (P₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x)
          (h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E),
          IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
          ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                  DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (P₁fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (P₂fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 ((P₀fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 ((P₁fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 ((P₂fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₀fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₁fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₂fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) := by
  classical
  
  
  obtain ⟨Q₀fib, Q₁fib, Q₂fib, hQval, hQj₀, hQj₁, hQj₂, hQc₀, hQc₁, hQc₂⟩ :=
    bareChartRicci_threeSlot_appCc_covariantTransfer (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  
  refine ⟨fun s => (-2 : ℝ) • Q₀fib s, fun s => (-2 : ℝ) • Q₁fib s, fun s => (-2 : ℝ) • Q₂fib s,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs x v h hvel
    rw [show ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
        (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (Q₀fib s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 (Q₁fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 (Q₂fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v from by
      rw [hQval s hs x v h hvel]]
    
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
    
    rw [show (fun (s : ℝ) => (-2 : ℝ) • Q₀fib s) s = (-2 : ℝ) • Q₀fib s from rfl,
      show (fun (s : ℝ) => (-2 : ℝ) • Q₁fib s) s = (-2 : ℝ) • Q₁fib s from rfl,
      show (fun (s : ℝ) => (-2 : ℝ) • Q₂fib s) s = (-2 : ℝ) • Q₂fib s from rfl,
      appCc_smul_local, appCc_smul_local, appCc_smul_local,
      unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply,
      unitModel_smul_local, unitModel_smul_local, unitModel_smul_local]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  · exact jointRSsmul_local (r := 2) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₀fib p.2).toSection p.1) hQj₀
  · exact jointRSsmul_local (r := 3) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₁fib p.2).toSection p.1) hQj₁
  · exact jointRSsmul_local (r := 4) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₂fib p.2).toSection p.1) hQj₂
  · intro x
    refine ((hQc₀ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]
  · intro x
    refine ((hQc₁ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]
  · intro x
    refine ((hQc₂ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]

private theorem integratedLinearizedRicci_negTwo_chartSum_appCc_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ∫ s in (0 : ℝ)..1,
              deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
                (I := I) g₀ T T' hδ hδ' x (v 0) (v 1)) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  
  obtain ⟨P₀fib, P₁fib, P₂fib, hpt, hj₀, hj₁, hj₂, hc₀, hc₁, hc₂⟩ :=
    exists_negTwoRicciArm_chartSymbolSum_appCc_families (I := I) (M := M) g₀ T T'
      hδ_lt hδ hδ'_lt hδ'
  
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have hIccS : Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSI : Set.uIcc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]; exact hIccS
  
  obtain ⟨IΦ₀, heval₀⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 2 P₀fib
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₀ hc₀
  obtain ⟨IΦ₁, heval₁⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 3 P₁fib
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₁ hc₁
  obtain ⟨IΦ₂, heval₂⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 4 P₂fib
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₂ hc₂
  refine ⟨IΦ₀, IΦ₁, IΦ₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
  
  have hrhs :
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀
            + appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁
            + appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v := by
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
  rw [hrhs]
  
  rw [heval₀ x v, heval₁ x v, heval₂ x v]
  
  
  
  rw [← intervalIntegral.integral_const_mul]
  
  
  have hii₀ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s) W₀) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 2 P₀fib W₀
      (hc₀ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  have hii₁ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (P₁fib s) W₁) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 3 P₁fib W₁
      (hc₁ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  have hii₂ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (P₂fib s) W₂) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 4 P₂fib W₂
      (hc₂ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  rw [← intervalIntegral.integral_add hii₀ hii₁, ← intervalIntegral.integral_add
    (hii₀.add hii₁) hii₂]
  
  
  refine intervalIntegral.integral_congr_ae ?_
  refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
    (MeasureTheory.measure_singleton 1)
  rw [Set.mem_singleton_iff]
  by_contra hne1
  apply hs
  intro hsmem
  rw [Set.mem_uIoc] at hsmem
  rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
  · have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs0, lt_of_le_of_ne hs1 hne1⟩
    obtain ⟨h, hvel, hderiv⟩ :=
      deriv_realizedRicciChartSum_eq_rebased_chartSymbol (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        hsIoo x (v 0) (v 1)
    rw [hderiv]
    
    rw [show ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s) W₀
              + appCc (I := I) (M := M) g₀ 3 2 (P₁fib s) W₁
              + appCc (I := I) (M := M) g₀ 4 2 (P₂fib s) W₂) x v from
      hpt s hsIoo x v h hvel]
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
  · exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)

private theorem integratedLinearizedRicci_negTwo_appCc_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ∫ s in (0 : ℝ)..1,
              DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt (I := I)
                g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  
  obtain ⟨P₀, P₁, P₂, heq⟩ :=
    integratedLinearizedRicci_negTwo_chartSum_appCc_eq (I := I) (M := M) g₀ T T'
      hδ_lt hδ hδ'_lt hδ'
  refine ⟨P₀, P₁, P₂, fun x v => ?_⟩
  
  
  
  
  have hint : (∫ s in (0 : ℝ)..1,
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt (I := I)
          g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s) =
      ∫ s in (0 : ℝ)..1,
        deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
          (I := I) g₀ T T' hδ hδ' x (v 0) (v 1)) s := by
    refine intervalIntegral.integral_congr_ae ?_
    refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
      (MeasureTheory.measure_singleton 1)
    rw [Set.mem_singleton_iff]
    by_contra hne1
    apply hs
    intro hsmem
    rw [Set.mem_uIoc] at hsmem
    rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
    · exact DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_eq_deriv_chartSum_on_Ioo
        (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) ⟨hs0, lt_of_le_of_ne hs1 hne1⟩
    · exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)
  rw [hint]
  exact heq x v

theorem negTwoRicciArm_appCc_eval
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  
  obtain ⟨P₀, P₁, P₂, heq⟩ :=
    integratedLinearizedRicci_negTwo_appCc_eq (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨P₀, P₁, P₂, fun x v => ?_⟩
  
  
  show ((-2 : ℝ) * ricciTensor (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
        - (-2 : ℝ) * ricciTensor (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) = _
  
  
  rw [show ((-2 : ℝ) * ricciTensor (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
          - (-2 : ℝ) * ricciTensor (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
        (-2 : ℝ) * (ricciTensor (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - ricciTensor (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) from by ring]
  rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciTensor_realized_sub_eq_integral_linearizedRicci
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
  
  exact heq x v

theorem deTurckLieArm_appCc_eval
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        lieDerivMetricClm (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
              (deTurckVF (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
            lieDerivMetricClm (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
              (deTurckVF (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 L₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 L₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 L₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  
  
  obtain ⟨R₀, R₁, R₂, heval⟩ :=
    deTurckRicciArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  obtain ⟨P₀, P₁, P₂, hP⟩ :=
    negTwoRicciArm_appCc_eval (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨R₀ - P₀, R₁ - P₁, R₂ - P₂, fun x v => ?_⟩
  
  
  
  have hsplit : ∀ (T₀ : SmoothCcTensor g₀ 0 2) {d : ℝ} (hd_lt : d < 1)
      (hd : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) d),
      lieDerivMetricClm (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd)
            (deTurckVF (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd))
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
        DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd) x (v 0) (v 1)
          - (-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd)) x (v 0) (v 1) := by
    intro T₀ d hd_lt hd
    rw [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  
  rw [hsplit T hδ_lt hδ, hsplit T' hδ'_lt hδ']
  rw [show
      (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1))
          - (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)
              - (-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
              - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1))
          - ((-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
              - (-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) from by
    ring]
  rw [heval x v, hP x v]
  
  
  rw [appCc_sub_left, appCc_sub_left, appCc_sub_left]
  rw [show
      (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
            - appCc (I := I) (M := M) g₀ 2 2 P₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')))
          + (appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                - appCc (I := I) (M := M) g₀ 3 2 P₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')))
          + (appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
                - appCc (I := I) (M := M) g₀ 4 2 P₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) =
        (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')))
          - (appCc (I := I) (M := M) g₀ 2 2 P₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) from by
    abel]
  rw [unitModel_sub_local, ContinuousMultilinearMap.sub_apply]

theorem deTurckLieArm_appCc_graded
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Λ : ℝ), 0 ≤ Λ ∧
      ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
        (∀ (x : M) (v : Fin 2 → TangentSpace I x),
          lieDerivMetricClm (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
                (deTurckVF (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
                  (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
              lieDerivMetricClm (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
                (deTurckVF (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
                  (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 L₁
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 L₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ Λ ^ 2) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 2 2 a L₀).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 3 2 a L₁).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 4 2 a L₂).toSection x) ≤ Λ ^ 2) := by
  obtain ⟨L₀, L₁, L₂, heval⟩ :=
    deTurckLieArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 L₀
  obtain ⟨K₁, hK₁_nn, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 2 L₁
  obtain ⟨K₂, hK₂_nn, hK₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 2 L₂
  obtain ⟨J₀, hJ₀_nn, hJ₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + a)
      (iteratedCovGrad (I := I) g₀ 2 2 a L₀)
  obtain ⟨J₁, hJ₁_nn, hJ₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (2 + a)
      (iteratedCovGrad (I := I) g₀ 3 2 a L₁)
  obtain ⟨J₂, hJ₂_nn, hJ₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + a)
      (iteratedCovGrad (I := I) g₀ 4 2 a L₂)
  set Kmax : ℝ := max (max (max K₀ K₁) K₂) (max (max J₀ J₁) J₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax :=
    le_trans hK₀_nn (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine ⟨Real.sqrt Kmax, Real.sqrt_nonneg _, L₀, L₁, L₂, heval, fun x => ?_, fun x => ?_⟩
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hK₀ x) ?_, le_trans (hK₁ x) ?_, le_trans (hK₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hJ₀ x) ?_, le_trans (hJ₁ x) ?_, le_trans (hJ₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
