/-
The `t = 0` one-sided Ricci-flow derivative by continuity extension, plus the
supporting continuity helpers: interior-`Ici`-derivative to ordinary derivative,
continuity of the pulled-back inner product and Ricci tensor in time, and
continuity of Ricci in the metric-time variable. Skeleton stubs for the
short-time-existence blueprint (GAP 2, `t = 0` extension).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem interior_ici_deriv_to_ordinary
    (f : ℝ → ℝ) {T : ℝ} (e : ℝ → ℝ)
    (h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t) :
    DifferentiableOn ℝ f (Set.Ioo 0 T) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, deriv f t = e t) := by
  -- On the open interval `Ioo 0 T`, the within-`Ici 0` derivative restricts to a
  -- within-`Ioo 0 T` derivative (since `Ioo 0 T ⊆ Ici 0`); openness then identifies
  -- `derivWithin` with the ordinary `deriv` and gives `differentiableOn`.
  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun y hy => le_of_lt hy.1
  -- The restricted within-`Ioo 0 T` derivative at every interior point.
  have h_within : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt f (e t) (Set.Ioo 0 T) t := fun t ht => (h_int t ht).mono hsub
  refine ⟨fun t ht => (h_within t ht).differentiableWithinAt, fun t ht => ?_⟩
  -- `deriv f t = derivWithin f (Ioo 0 T) t` by openness, and the latter equals `e t`.
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  rw [← derivWithin_of_isOpen hopen ht]
  exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)

omit [CompactSpace M] [I.Boundaryless] in
theorem ricci_flow_pde_at_zero
    (g_fam : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (x : M)
    (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_fam s).inner x v w) (Set.Ico 0 T))
    (h_ric_cont : ContinuousWithinAt
      (fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam 0) x v w) (Set.Ici 0) 0 := by
  -- Abbreviations for the inner-product and Ricci-RHS families.
  set f : ℝ → ℝ := fun s : ℝ => (g_fam s).inner x v w with hf
  set e : ℝ → ℝ := fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w with he
  -- The interior data, transported to the present `f`/`e` notation.
  have h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t :=
    h_interior
  -- The interior `Ici`-derivatives upgrade to ordinary derivatives on `Ioo 0 T`,
  -- and `deriv f = e` there.
  obtain ⟨h_diff, h_derivEq⟩ := interior_ici_deriv_to_ordinary f e h_int
  -- We apply the continuity-extension theorem with the open interior interval as the
  -- right-neighbourhood witness.
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 T) h_diff ?_ ?_ ?_
  · -- `f` is right-continuous at `0` along `Ioo 0 T`: restrict the `Ico 0 T` continuity.
    have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
    exact (h_cont.continuousWithinAt h0).mono Set.Ioo_subset_Ico_self
  · -- `Ioo 0 T` is a right-neighbourhood of `0`.
    exact Ioo_mem_nhdsGT hT
  · -- The derivative converges to `e 0` from the right: `deriv f =ᶠ e` on `Ioo 0 T`,
    -- which is in `𝓝[>] 0`, and `e` is right-continuous at `0` by hypothesis.
    have h_eventuallyEq : (fun s : ℝ => deriv f s) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] e :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hT) h_derivEq
    exact (h_ric_cont.tendsto).congr' h_eventuallyEq.symm

theorem gfam_inner_continuous_on
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x : M) (v w : TangentSpace I x)
    (hg_joint : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ Set.univ))
    (hΦ_orbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_mfderiv : ∀ (y : M) (p : TangentSpace I y),
      ContinuousOn (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) y p : E)) (Set.Ico 0 T)) :
    ContinuousOn
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      (Set.Ico 0 T) := sorry

theorem ricci_gfam_continuous_on
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x : M) (v w : TangentSpace I x)
    (hC2 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α))
    (hΦ0 : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ : ∀ (y : M) (p : TangentSpace I y),
      ContinuousOn (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) y p : E)) (Set.Ico 0 T)) :
    ContinuousOn
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
      (Set.Ico 0 T) := sorry

theorem ricci_continuous_in_metric_time
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (x : M) (v w : TangentSpace I x)
    (hval : ∀ y : M, ∀ p q : TangentSpace I y,
      ContinuousOn (fun s : ℝ => (g_DT s).inner y p q) (Set.Icc 0 T))
    (hC2 : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T)) :
    ContinuousOn (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T) := sorry

end DifferentialGeometry.PDE.RicciFlow
