import DifferentialGeometry.Analysis.ODE.FlowCkVariational
import DifferentialGeometry.Analysis.ODE.FlowCk
import DifferentialGeometry.Analysis.ODE.FlowC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal ContDiff
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

/-! ## H2 — variational-equation characterization of `∂Φ/∂x₀` (headline) -/

theorem h2_variationalEquation_spatialDerivative_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ∃ (r : ℝ≥0) (ε : ℝ) (_ : 0 < (r : ℝ)) (_ : 0 < ε) (Φ : E × ℝ → E),
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) Φ ∧
      ∃ (T : ℝ) (ρ : ℝ≥0) (_ : 0 < T) (_ : 0 < (ρ : ℝ))
        (W : E × ℝ → (E →L[ℝ] E)),
        (∀ q ∈ (Metric.ball x₀ (ρ : ℝ)) ×ˢ Set.Ioo (t₀ - T) (t₀ + T),
          fderiv ℝ Φ q = (W q).coprod (timePieceFn f Φ q)) ∧
        (∀ x ∈ Metric.ball x₀ (ρ : ℝ), W (x, t₀) = ContinuousLinearMap.id ℝ E) ∧
        (∀ x ∈ Metric.ball x₀ (ρ : ℝ), ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
          HasDerivAt (fun s => W (x, s))
            ((fderiv ℝ (f t) (Φ (x, t))).comp (W (x, t))) t) := sorry

/-! ## H2 — coprod-block reconstruction and supporting slices -/

theorem fderiv_flow_eq_spatialBlock_coprod_timePiece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E} {t : ℝ}
    (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) (ht : t ∈ Set.Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, t)) :
    fderiv ℝ Φ (x, t)
      = (fderiv ℝ (fun y => Φ (y, t)) x).coprod (timePieceFn f Φ (x, t)) := sorry

theorem fderiv_spatialSlice_initial_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E}
    (hx : x ∈ Metric.ball x₀ (r : ℝ)) :
    fderiv ℝ (fun y => Φ (y, t₀)) x = ContinuousLinearMap.id ℝ E := by
  have hball : Metric.ball x₀ (r : ℝ) ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
  have heqon : Set.EqOn (fun y => Φ (y, t₀)) (fun y => y) (Metric.ball x₀ (r : ℝ)) :=
    fun y hy => hΦ.apply_initial y (Metric.ball_subset_closedBall hy)
  have heq : (fun y => Φ (y, t₀)) =ᶠ[𝓝 x] (fun y => y) :=
    Filter.eventuallyEq_of_mem hball heqon
  rw [heq.fderiv_eq, fderiv_id']

theorem time_block_eq_comp_inr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0}
    {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) {x : E} {t : ℝ}
    (hx : x ∈ Metric.closedBall x₀ (r : ℝ)) (ht : t ∈ Set.Ioo tmin tmax)
    (hΦdiff : DifferentiableAt ℝ Φ (x, t)) :
    (fderiv ℝ Φ (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)
      = timePieceFn f Φ (x, t) := by
  -- Both sides are CLMs `ℝ →L[ℝ] E`; reduce equality to agreement at the scalar `1`.
  refine ContinuousLinearMap.ext_ring ?_
  -- LHS at `1`: `fderiv ℝ Φ (x, t) (inr ℝ E ℝ 1)`; RHS at `1`: `(1 : ℝ) • f t (Φ (x, t))`.
  simp only [ContinuousLinearMap.comp_apply, timePieceFn_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
  -- The remaining goal is the verified applied-at-1 flow-ODE identity.
  exact flow_joint_fderiv_inr_eq hΦ hx ht hΦdiff

end DifferentialGeometry.PDE.RicciFlow.ODE
