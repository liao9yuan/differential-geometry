import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.FlowC1
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
## H3 — manifold-global joint smooth dependence (headline + pending children)

This file carries the manifold-level smooth-dependence theorems of the smooth-dependence
program: the H3 headline together with its pending proof-target children.
-/

noncomputable section
open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

-- H3 headline (v5: intrinsic jointly-smooth section input `hX`; `[I.Boundaryless]` added — needed by
--  isOpen_extChartAt_target / extChartAt_target_mem_nhds, NOT derivable from [BoundarylessManifold I M].)
theorem h3_local_flow_jointSmooth_and_integralCurve [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) (p₀ : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hp₀ : p₀ ∈ U) (T : ℝ) (_hT : 0 < T)
      (Φ : M → ℝ → M),
      (∀ p ∈ U, Φ p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := sorry

-- [H3: chartcoord-jointContDiffOn-pushforward-to-contMDiffOn]
theorem h3_manifoldFlow_contMDiffOn_of_jointContDiffOn
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ T t₀ : ℝ}
    (U : Set M) (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H p₀).source)
    (hUball : ∀ p ∈ U, I ((chartAt H p₀) p) ∈ Metric.ball (I ((chartAt H p₀) p₀)) ρ)
    (hΦE_smooth : ContDiffOn ℝ ∞ Φ_E
      (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (htgt : ∀ p ∈ U, ∀ s ∈ Set.Ioo (t₀ - T) (t₀ + T),
      Φ_E (I ((chartAt H p₀) p), s) ∈ (extChartAt I p₀).target) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (extChartAt I p₀).symm (Φ_E (I ((chartAt H p₀) q.2), q.1)))
      (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) := sorry

-- C1 [H3 v3: chart-p₀ PUSHFORWARD field = X-section read in the FIXED trivialization at p₀, jointly C∞.
--  No moving chart: source=target=p₀, so this is literally the fixed-triv fiber component of the C∞ X-section.]
theorem chart_pushforward_field_jointContDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ_sub : Metric.ball (extChartAt I p₀ p₀) ρ ⊆ (extChartAt I p₀).target) :
    ContDiffOn ℝ ∞
      (Function.uncurry (fun (s : ℝ) (c : E) =>
        ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2))
      ((Set.univ : Set ℝ) ×ˢ Metric.ball (extChartAt I p₀ p₀) ρ) := sorry

-- C2 [H3 v3: cutoff globalization — multiply C1's field by a ContDiffBump supported in the chart target
--  to obtain a GLOBALLY-C∞ field on all of ℝ × E (the input exists_isLocalFlow_contDiffOn_top requires).]
theorem chart_pushforward_field_cutoff_globalContDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (G : ℝ → E → E) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      ContDiff ℝ ∞ (Function.uncurry G) ∧
      ∀ (s : ℝ), ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ',
        G s c = ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 := sorry

-- A1 [H3 v4: orbit confinement to the AGREEMENT ball ρ' (where the cutoff field G = the genuine field F),
--  not merely the chart target — the round-3 fix. Tube argument; c4-* sub-nodes survive with target→ball ρ'.]
theorem chartflow_confined_to_agreementBall
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ ρ' T t₀ : ℝ} (hρ' : 0 < ρ') (hρ'_le : ρ' ≤ ρ)
    (hT : 0 < T)
    (hΦE_cont : ContinuousOn Φ_E
      (Metric.ball (extChartAt I p₀ p₀) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (hinit : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ, Φ_E (c, t₀) = c) :
    ∃ (ρ'' T' : ℝ), 0 < ρ'' ∧ 0 < T' ∧ ρ'' ≤ ρ' ∧ T' ≤ T ∧
      ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ' := sorry

-- A2 [H3 v4: G→F velocity swap + Icc→Ioo — the chart ODE of ΦE (flow of the CUTOFF field G) carries the
--  GENUINE field F on Ioo, since the orbit stays in the agreement ball ρ' (A1) where G=F. Template chartPhaseVFCutoff_eq_of_mem_closedBall (SmoothFlow.lean:236).]
theorem chartODE_genuineF_on_Ioo
    (p₀ : M) (G F : ℝ → E → E) (Φ_E : E × ℝ → E) {ρ'' ρ' T' t₀ : ℝ} (r : ℝ≥0) {tmin tmax : ℝ}
    (hρ''_le : ρ'' ≤ ρ')
    (hflow : IsLocalFlow G t₀ (extChartAt I p₀ p₀) r tmin tmax Φ_E)
    (hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc tmin tmax)
    (hball_sub : Metric.ball (extChartAt I p₀ p₀) ρ' ⊆ Metric.closedBall (extChartAt I p₀ p₀) (r : ℝ))
    (hGF : ∀ (s : ℝ), ∀ y ∈ Metric.ball (extChartAt I p₀ p₀) ρ', G s y = F s y)
    (hconf : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ') :
    ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
      HasDerivWithinAt (fun s => Φ_E (c, s)) (F t (Φ_E (c, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t := sorry

-- field-form-identity [H3 v5: the fixed-p₀-trivialization fibre reading EQUALS the chart-p₀ coordinate velocity
--  `tangentCoordChange I pt p₀ pt (X s pt)` (rfl-level via trivializationAt_apply + tangentCoordChange_def +
--  extChartAt = (chartAt).extend I). Supplies C6's `hF` hypothesis.]
theorem field_form_identity_trivreading_eq_chartvelocity
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M) (s : ℝ) (c : E) :
    ((trivializationAt E (TangentSpace I) p₀)
        (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2
      = tangentCoordChange I ((extChartAt I p₀).symm c) p₀ ((extChartAt I p₀).symm c)
          (X s ((extChartAt I p₀).symm c)) := sorry

-- chart→intrinsic bridge [H3 v5: OFF the H3 critical path. Documents the chart-coordinate hSmoothX_chart ⇒ the
--  intrinsic section hX gap — precisely the project TangentSpace:=E frame diamond. A user holding only chart data
--  discharges H3's `hX` through this. NOT a child/ancestor of h3.]
theorem chart_field_smooth_to_intrinsic_section
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) := sorry

-- [H3 corrected decomposition: new pending child 7 — bare-velocity recovery via the pushforward chain rule]
theorem chartflow_eq_bareflow_on_U
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M)
    (F : ℝ → E → E) (ΦE : E × ℝ → E) (U : Set M) {a b : ℝ}
    (hchartODE : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
        (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo a b) t)
    (hF : ∀ (s : ℝ) (c : E), F s c =
        tangentCoordChange I ((extChartAt I p₀).symm c) p₀
          ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))
    (hconf : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target)
    (hUsrc : U ⊆ (extChartAt I p₀).source) :
    ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
        (Set.Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) := sorry

-- [H3: pushforward→bare velocity cancellation (under chartflow-eq-bareflow-on-U)]
theorem pushforward_velocity_cancellation (p₀ q : M)
    (hq : q ∈ (extChartAt I p₀).source) (v : E) :
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (extChartAt I p₀ q))
        (tangentCoordChange I q p₀ q v) = v := sorry

end Manifold

end DifferentialGeometry.PDE.RicciFlow.ODE
