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
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.PDE.DeTurck.ChristoffelContInMetric
import DifferentialGeometry.Integral.Connection.ChartBridge.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.RiemannBasisIdentity
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
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

/-! ## Chart-coordinate Gram-data continuity-in-time converters

The hypothesis `hC2` of `ricci_continuous_in_metric_time` controls the continuity in
time of the iterated Fréchet derivatives `iteratedFDeriv ℝ k (chartGramOnE (g_DT s) α i j)`
of the chart-Gram entries, for `k ≤ 2`, at a chart point.  The chart-Christoffel /
chart-Riemann / chart-Ricci continuity chain instead consumes the directional
`partialDeriv` data (the `0`-, `1`- and `2`-jet chart-Gram entries in basis directions).
These private lemmas convert the `iteratedFDeriv`-jet continuity into the directional
`partialDeriv` continuity, using the standard `iteratedFDeriv`-to-directional identities
and the boundedness (hence continuity) of the multilinear evaluation map. -/

namespace RicciContInMetricAux

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

/-- `chartGramOnE` is twice differentiable at any point of the chart-target interior. -/
private lemma chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  exact (hcd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- The Fréchet derivative `fderiv (chartGramOnE g α i j)` is differentiable at any
point of the chart-target interior (the chart-Gram entry is `C^∞`, hence `C²`). -/
private lemma fderiv_chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  have hcdAt : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j) y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  -- `C^∞` gives the derivative map is `C^∞`, hence differentiable.
  have hderiv := hcdAt.fderiv_right (m := ∞) le_rfl
  exact hderiv.differentiableAt (by simp)

/-- The second directional partial of `chartGramOnE` equals the value of the second
iterated Fréchet derivative on the two basis directions, at a chart-target interior point. -/
private lemma partialDeriv_partialDeriv_chartGramOnE_eq_iteratedFDeriv_two
    (g : SmoothRiemannianMetric I M) (α : M) (i j m l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y =
      iteratedFDeriv ℝ 2 (chartGramOnE (I := I) g α i j) y
        ![(chartModelBasis E) m, (chartModelBasis E) l] := by
  -- `partialDeriv l f = fun z => fderiv f z (e_l)`; differentiate once more in direction `e_m`.
  have hl : (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))
      = fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z ((chartModelBasis E) l) := by
    funext z; rfl
  rw [show partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y
      = fderiv ℝ (fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z
            ((chartModelBasis E) l)) y ((chartModelBasis E) m) from by rw [hl]; rfl]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply (fderiv_chartGramOnE_diffAt_int (I := I) g α i j hy)
    (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

/-- Continuity-in-time of the `0`-jet chart-Gram entry from the `iteratedFDeriv 0`
continuity supplied by `hC2`. -/
private lemma chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : E) (s : Set ℝ)
    (h0 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ
    ![]).continuous
  have hcomp := hL.comp_continuousOn h0
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_zero_apply]

/-- Continuity-in-time of the `1`-jet directional chart-Gram partial from the
`iteratedFDeriv 1` continuity supplied by `hC2`. -/
private lemma partialDeriv_chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (l i j : Fin (Module.finrank ℝ E)) (y : E) (s : Set ℝ)
    (h1 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
    ![(chartModelBasis E) l]).continuous
  have hcomp := hL.comp_continuousOn h1
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_one_apply, Matrix.cons_val_zero]
  rfl

/-- Continuity-in-time of the `2`-jet directional second chart-Gram partial from the
`iteratedFDeriv 2` continuity supplied by `hC2`, at a chart-target interior point. -/
private lemma partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m l i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (h2 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j)) y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
    ![(chartModelBasis E) m, (chartModelBasis E) l]).continuous
  have hcomp := hL.comp_continuousOn h2
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply]
  rw [← partialDeriv_partialDeriv_chartGramOnE_eq_iteratedFDeriv_two
    (I := I) (g_DT t) α i j m l hy]

/-- Continuity-in-time of the `gramBracket` (a `1`-jet chart-Gram combination). -/
private lemma gramBracket_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) (s : Set ℝ)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y) s := by
  -- `gramBracket = ∂_i G_{lj} + ∂_j G_{li} − ∂_l G_{ij}`.
  have heq : (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j) y +
            partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i) y -
            partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y := by
    funext t; rfl
  rw [heq]
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α i l j y s (h1 l j)
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α j l i y s (h1 l i)
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α l i j y s (h1 i j)

/-- Continuity-in-time of the `gramBracketDeriv` (a `2`-jet chart-Gram combination),
at a chart-target interior point. -/
private lemma gramBracketDeriv_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y) s := by
  -- `gramBracketDeriv = ∂_m∂_i G_{lj} + ∂_m∂_j G_{li} − ∂_m∂_l G_{ij}`.
  have heq : (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) m
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j)) y +
            partialDeriv (E := E) m
              (partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i)) y -
            partialDeriv (E := E) m
              (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j)) y := by
    funext t; rfl
  rw [heq]
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m i l j hy s (h2 l j)
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m j l i hy s (h2 l i)
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m l i j hy s (h2 i j)

/-- Continuity-in-time of the directional inverse-Gram partial, at a chart-target
interior point, from the `0`- and `1`-jet chart-Gram continuity plus positive
definiteness. -/
private lemma partialDeriv_chartInvGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y) s := by
  classical
  -- Chart-Gram entry continuity from the `0`-jet, used by the inverse-Gram lemma.
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  -- Closed form `∂_m G^{kl} = −∑_{a,b} G^{ka} G^{bl} ∂_m G_{ab}`.
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y =
        -∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT t) α k a y *
              chartInvGramOnE (I := I) (g_DT t) α b l y *
              partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y := by
    intro t _
    exact partialDeriv_chartInvGramOnE_eq (I := I) (g_DT t) α y m k l hy
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.neg ?_
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx k a
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx b l
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α m a b y s (h1 a b)

/-- Continuity-in-time of the directional Christoffel partial `∂_m Γ^k_{ij}`, at a
chart-target interior point, from the `0`-, `1`- and `2`-jet chart-Gram continuity. -/
private lemma partialDeriv_chartChristoffel_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y) s := by
  classical
  -- Chart-Gram entry continuity from the `0`-jet (used by `chartInvGramOnE` continuity).
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  -- Leibniz expansion `∂_m Γ = ½ ∑_l (∂_m G^{kl}·S_{ij,l} + G^{kl}·∂_m S_{ij,l})`.
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y *
              gramBracket (I := I) (g_DT t) α i j l y +
            chartInvGramOnE (I := I) (g_DT t) α k l y *
              gramBracketDeriv (I := I) (g_DT t) α m i j l y) := by
    intro t _
    exact partialDeriv_chartChristoffel_eq (I := I) (g_DT t) α m i j k hy
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) (ContinuousOn.mul ?_ ?_)
  · exact partialDeriv_chartInvGramOnE_continuous_of_hC2
      (I := I) g_DT α m k l hy s hx h0 h1
  · exact gramBracket_continuous_of_hC2 (I := I) g_DT α i j l y s h1
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx k l
  · exact gramBracketDeriv_continuous_of_hC2 (I := I) g_DT α m i j l hy s h2

/-- Continuity-in-time of a chart-Riemann tensor entry, at a chart-target interior point,
from the `0`-, `1`- and `2`-jet chart-Gram continuity. -/
private lemma chartRiemannTensor_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i j k r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      chartRiemannTensor (I := I) (g_DT t) α i j k r y) s := by
  classical
  -- `R = ∂_j Γ_{ikr} − ∂_k Γ_{ijr} + ∑_n (Γ_{jnr}·Γ_{ikn} − Γ_{knr}·Γ_{ijn})`.
  have heq : (fun t : ℝ => chartRiemannTensor (I := I) (g_DT t) α i j k r y)
      = fun t : ℝ =>
          partialDeriv (E := E) j (chartChristoffel (I := I) (g_DT t) α i k r) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) (g_DT t) α i j r) y +
            (∑ n : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (g_DT t) α j n r y *
                  chartChristoffel (I := I) (g_DT t) α i k n y -
                chartChristoffel (I := I) (g_DT t) α k n r y *
                  chartChristoffel (I := I) (g_DT t) α i j n y)) := by
    funext t; rw [chartRiemannTensor_def]
  rw [heq]
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact partialDeriv_chartChristoffel_continuous_of_hC2
      (I := I) g_DT α j i k r hy s hx h0 h1 h2
  · exact partialDeriv_chartChristoffel_continuous_of_hC2
      (I := I) g_DT α k i j r hy s hx h0 h1 h2
  · refine continuousOn_finset_sum _ (fun n _ => ?_)
    have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
        ContinuousOn (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b c y) s := by
      intro a b c
      refine chartChristoffel_continuous_in_metric_at (I := I) g_DT α y s ?_ ?_ hx a b c
      · exact fun p q => chartGramOnE_continuous_of_hC2 (I := I) g_DT α p q y s (h0 p q)
      · exact fun p q r' =>
          partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α p q r' y s (h1 q r')
    exact ContinuousOn.sub (ContinuousOn.mul (hΓ j n r) (hΓ i k n))
      (ContinuousOn.mul (hΓ k n r) (hΓ i j n))

/-- Continuity-in-time of a chart-Ricci tensor entry, at a chart-target interior point,
from the `0`-, `1`- and `2`-jet chart-Gram continuity. -/
private lemma chartRicciTensor_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      chartRicciTensor (I := I) (g_DT t) α i k y) s := by
  classical
  have heq : (fun t : ℝ => chartRicciTensor (I := I) (g_DT t) α i k y)
      = fun t : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g_DT t) α i j k j y := by
    funext t; rw [chartRicciTensor_def]
  rw [heq]
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  exact chartRiemannTensor_continuous_of_hC2 (I := I) g_DT α i j k j hy s hx h0 h1 h2

end RicciContInMetricAux

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
      (Set.Ico 0 T) := by
  -- The bundled pullback inner product is `(g_DT s).inner (Φ_fam s x) (dΦ_s v) (dΦ_s w)`
  -- via the clean identity `pullbackMetric_inner_funext`.  Expanding at a fixed `s₀` in
  -- the chart `α := Φ_fam s₀ x` through `g_inner_eq_chart_sum`, the inner product is a
  -- finite sum whose chart-Gram factor `chartGramOnE (g_DT s) α i j (extChartAt I α (Φ_fam s x))`
  -- is continuous in `s` by composing `hg_joint α i j` with the continuous
  -- `s ↦ (s, Φ_fam s x)` (from `hΦ_orbit`).  The remaining factors are the chart-`α`
  -- trivialization coordinates of the moving pushforward `dΦ_s v`, i.e.
  -- `(triv α).continuousLinearMapAt ℝ (Φ_fam s x) (mfderiv I I (Φ_fam s) x v)`.
  --
  -- GENUINE OPEN INPUT (moving self-trivialization coordinate change).  The hypothesis
  -- `hΦ_mfderiv` supplies continuity of the *raw* model-fibre value
  -- `(mfderiv I I (Φ_fam s) x v : E)` (the identity coercion `TangentSpace I (Φ_fam s x) = E`,
  -- i.e. the *self*-trivialization coordinate at the moving point `Φ_fam s x`).  Converting
  -- this raw value to the *fixed* chart-`α` coordinate requires the coordinate change
  -- `coordChangeL (triv at Φ_fam s x) (triv α) (Φ_fam s x)`, whose first trivialization
  -- argument itself moves with `s`; Mathlib's `contMDiffOn_coordChangeL` only handles a
  -- fixed pair of trivializations.  Closing this in general (without the
  -- mathematically-false `HasLocallyConstantChartAt`) needs either the total-space
  -- continuity of `s ↦ ⟨Φ_fam s x, mfderiv I I (Φ_fam s) x v⟩` into `TangentBundle I M`
  -- (equivalently chart-`α` coordinate continuity of the pushforward), or a strengthened
  -- `hΦ_mfderiv` stated in fixed-chart coordinates.  Left as a single honest gap.
  sorry

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
      (Set.Ico 0 T) := by
  -- Reduce the pullback-metric Ricci tensor to the moving-frame form via the CLEAN
  -- naturality identity `ricci_pullback_naturality`:
  --   `ricciTensor (Φ_s^* g_DT s) x v w
  --      = ricciTensor (g_DT s) (Φ_fam s x) (dΦ_s v) (dΦ_s w)`.
  have hnat : (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
      = fun s : ℝ => ricciTensor (I := I) (g_DT s) (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w) := by
    funext s
    exact ricci_pullback_naturality (I := I) (g_DT s) (Φ_fam s) x v w
  rw [hnat]
  -- It remains to prove continuity of the moving-frame Ricci tensor in `s`.  The
  -- metric-time direction (fixed basepoint, fixed vectors) is the clean sibling
  -- `ricci_continuous_in_metric_time` (consuming the chart-`2`-jet input `hC2`); the
  -- moving basepoint `Φ_fam s x` and moving pushforward vectors `dΦ_s v`, `dΦ_s w` are
  -- the additional content here.
  --
  -- GENUINE OPEN INPUT (moving basepoint + moving frame).  Expanding the abstract Ricci
  -- tensor at the moving point `Φ_fam s x` in the fixed chart `α := Φ_fam s₀ x` (the
  -- chart-Riemann basis identity is unconditional via `chartRiemannBasisIdentity_holds`)
  -- reduces the metric/basepoint dependence to chart-Ricci entries
  -- `chartRicciTensor (g_DT s) α i k (extChartAt I α (Φ_fam s x))`, whose continuity in
  -- `s` follows from the chart-`2`-jet hypothesis `hC2` composed with the continuous
  -- orbit `s ↦ Φ_fam s x` (the same chart-Gram → Christoffel → Riemann → Ricci chain as
  -- in `ricci_continuous_in_metric_time`, but along the moving chart point).  The frame
  -- factors are the chart-`α` trivialization coordinates of the moving pushforwards
  -- `dΦ_s v`, `dΦ_s w`, whose continuity is exactly the moving-self-trivialization
  -- coordinate-change gap documented on `gfam_inner_continuous_on` (the hypothesis `hΦ`
  -- supplies only the raw model-fibre value, not the fixed-chart coordinate).  Left as a
  -- single honest gap, funnelling the same moving-frame coordinate-change input.
  sorry

-- `hval` (the chart-`0`-jet metric value continuity) is a mandated signature input that
-- the parent `deturck_solution_c2_continuous_icc0` supplies; the chart-Ricci continuity
-- chain reconstructs the full Ricci tensor from the chart-`2`-jet data `hC2` alone (the
-- `0`-jet value is already controlled by `hC2`'s `k = 0` instance), so `hval` is not
-- consumed in the proof.  Silence the resulting unused-binder linter on this binder only.
set_option linter.unusedVariables false in
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
    ContinuousOn (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T) := by
  classical
  open RicciContInMetricAux in
  -- Chart at the basepoint itself; `x` lies in its Levi-Civita good set.
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hx_base : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [(extChartAt I x).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hxgood)]
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hxgood
  -- The `k`-jet chart-Gram time-continuity at the self-chart point, repackaged per order.
  have h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 0 (by norm_num)
  have h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 1 (by norm_num)
  have h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 2 (by norm_num)
  -- Chart-coordinate expansion of the abstract Ricci tensor (constant-coefficient sum
  -- over the chart-Ricci entries) via the unconditional chart-Riemann basis identity.
  have hbridge : ∀ t : ℝ,
      ricciTensor (I := I) (g_DT t) x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k *
              ((chartModelBasis E).repr w) i *
              chartRicciTensor (I := I) (g_DT t) x i k (extChartAt I x x) := by
    intro t
    exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) (g_DT t) x
      (chartRiemannBasisIdentity_holds (I := I) (g_DT t) x) v w
  rw [show (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w)
        = fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) k *
                ((chartModelBasis E).repr w) i *
                chartRicciTensor (I := I) (g_DT s) x i k (extChartAt I x x) from by
    funext s; exact hbridge s]
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  exact chartRicciTensor_continuous_of_hC2 (I := I) g_DT x i k hx_int (Set.Icc 0 T)
    hx_base h0 h1 h2

end DifferentialGeometry.PDE.RicciFlow
