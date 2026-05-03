import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RiemannEvolution
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Ricci
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Gradient
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Laplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Flow Calculus

`RicciFlowData` bundles the geometric data and hypotheses.
Evolution equations for the connection, curvature, and scalar curvature.
-/

open SyntheticTensor

-- ============================================================
-- Bundled Ricci Flow Data
-- ============================================================

section RicciFlowData

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Bundled Ricci flow data: geometric structures and connecting
    properties needed for the evolution equations.

    Smoothness fields bundle the families of scalar smoothness conditions
    that the downstream evolution theorems need:

    * `h_met` — scalar slices of the metric family.
    * `h_Rc_smooth` — scalar slices of the Ricci form family.
    * `h_emb_met` — spatial derivative of scalar metric slices along a vector.
    * `h_conn_smooth` / `h_g_conn_smooth` — scalar covariantly-paired
      connection slices (needed by `conn_var_eq_A_rf` and related theorems). -/
structure RicciFlowData where
  emb : DerivationEmbedding k R V
  td : TimeDerivativeData R A Time
  [td_regular : TimeRegularFam td]
  atr : AbstractTrace R V
  g_fam : Time → MetricDuality R V
  h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)
  conn_fam : Time → V → V → V
  ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z
  hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z
  hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z
  hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y
  h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam
  h_st : SpatialTemporalComm emb td
  h_mvp : MetricBilinProductRule td g_fam h_met
  h_mfp : MetricFullProductRule td g_fam h_met
  h_Rc_smooth : ∀ vs αs, td.isSmoothFam
    (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) atr vs αs)
  h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth

attribute [instance] RicciFlowData.td_regular

end RicciFlowData

-- ============================================================
-- Evolution Equations from RicciFlowData
-- ============================================================

section Equations

variable {k R V Time A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Scalar curvature evolution under Ricci flow:
    ∂_t R = 2|Rc|² + metric_trace_g(t)(∂_t Rc).

    Extracted from `scalar_curvature_evolution` using the bundled data. -/
theorem RicciFlowData.dt_R (D : RicciFlowData k R V Time A) (t : Time) :
    D.td.dt_apply (fun s => ScalarCurvature D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr (D.g_fam s)) t =
    2 * ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) +
    metric_trace (D.g_fam t) D.atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor D.td t (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr)
        D.h_Rc_smooth) ![] ![] :=
  scalar_curvature_evolution D.emb D.td D.atr D.g_fam D.h_met D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth D.h_rf D.h_sc_prod t

/-- Closed scalar curvature evolution from a supplied Ricci-evolution RHS and its trace:
    `∂ₜ R = trace_g(rhs) + 2|Rc|²`.

This is not yet the classical `ΔR + 2|Rc|²` statement unless `rhs_trace` has
separately been identified with the scalar Laplacian. -/
theorem RicciFlowData.dt_R_full_from_rhs (D : RicciFlowData k R V Time A)
    (rhs : Time -> TensorData R V 0 2)
    (rhs_trace : Time -> R)
    (h_evol : forall t,
      dt_tensor D.td t
        (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s)
          (D.hsl_fam s) (D.hl_fam s) D.atr)
        D.h_Rc_smooth = rhs t)
    (h_trace : RicciTraceIdentityForRHS D.atr D.g_fam rhs rhs_trace)
    (t : Time) :
    D.td.dt_apply (fun s =>
      ScalarCurvature D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s)
        (D.hsl_fam s) (D.hl_fam s) D.atr (D.g_fam s)) t =
    rhs_trace t +
      2 * ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) :=
  scalar_curvature_evolution_full_from_rhs D.emb D.td D.atr D.g_fam D.h_met
    D.conn_fam D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth D.h_rf
    D.h_sc_prod rhs rhs_trace h_evol h_trace t

/-- Scalar evolution from a Lichnerowicz-form Ricci evolution equation.

This is still interface plumbing: the caller supplies the trace of the
Lichnerowicz RHS. A later theorem should identify that trace with the scalar
Laplacian using the actual rough-laplacian/reaction formulas and Bianchi
identities. -/
theorem RicciFlowData.dt_R_full_from_laplace_reaction (D : RicciFlowData k R V Time A)
    (rough reaction : Time -> TensorData R V 0 2)
    (rhs_trace : Time -> R)
    (h_evol : RicciLichnerowiczEvolutionEquation D.emb D.td D.atr D.conn_fam
      D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth rough reaction)
    (h_trace : RicciTraceIdentityForRHS D.atr D.g_fam
      (ricci_laplace_reaction_rhs rough reaction) rhs_trace)
    (t : Time) :
    D.td.dt_apply (fun s =>
      ScalarCurvature D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s)
        (D.hsl_fam s) (D.hl_fam s) D.atr (D.g_fam s)) t =
    rhs_trace t +
      2 * ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) :=
  RicciFlowData.dt_R_full_from_rhs D (ricci_laplace_reaction_rhs rough reaction)
    rhs_trace h_evol h_trace t

/-- Gradient evolution under Ricci flow for a time-independent scalar:
    ∂_t[g(t)(grad_s u, Y)] = 2 Rc(grad_t u, Y). -/
theorem RicciFlowData.dt_grad (D : RicciFlowData k R V Time A)
    (u : R) (Y : V) (t : Time) :
    D.td.dt_apply (fun s => (D.g_fam t).g (grad D.emb (D.g_fam s) u) Y) t =
    2 * ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr
      ![grad D.emb (D.g_fam t) u, Y] ![] :=
  gradient_evolution D.emb D.td D.atr D.g_fam D.h_met D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf D.h_mvp u Y t

/-- Gradient squared evolution under Ricci flow:
    ∂_t|∇u|² = 2 Rc(∇u,∇u) + 2 g(∇u, ∇(∂_t u)).
    Requires smoothness of the time-dependent function `u`. -/
theorem RicciFlowData.dt_grad_sq (D : RicciFlowData k R V Time A)
    (u : Time → R) (hu : D.td.isSmoothFam u) (t : Time) :
    D.td.dt_apply (fun s => (D.g_fam s).g
      (grad D.emb (D.g_fam s) (u s))
      (grad D.emb (D.g_fam s) (u s))) t =
    2 * ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr
      ![grad D.emb (D.g_fam t) (u t), grad D.emb (D.g_fam t) (u t)] ![] +
    2 * (D.g_fam t).g (grad D.emb (D.g_fam t) (u t))
                      (grad D.emb (D.g_fam t) (D.td.dt_apply u t)) :=
  gradient_squared_evolution D.emb D.td D.atr D.g_fam D.h_met D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf D.h_mfp D.h_st u hu t

/-- Laplacian evolution under Ricci flow:
    ∂_t(Δu) = 2⟨Rc, Hess(u)⟩ + metric_trace_t(∂_t Hess). -/
theorem RicciFlowData.dt_laplacian (D : RicciFlowData k R V Time A)
    (hessian_fam : Time → TensorData R V 0 2)
    (h_hess_smooth : ∀ vs αs, D.td.isSmoothFam (fun τ => hessian_fam τ vs αs))
    (h_lap_prod : LaplacianProductRule D.emb D.td D.atr D.g_fam D.h_met hessian_fam h_hess_smooth)
    (t : Time) :
    D.td.dt_apply (fun s =>
      metric_trace (D.g_fam s) D.atr (0 : Fin 2) (0 : Fin 1) (hessian_fam s) ![] ![]) t =
    2 * tensor_inner_02 (D.g_fam t) D.atr
      (ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr)
      (hessian_fam t) +
    metric_trace (D.g_fam t) D.atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor D.td t hessian_fam h_hess_smooth) ![] ![] :=
  laplacian_evolution D.emb D.td D.atr D.g_fam D.h_met D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf hessian_fam h_hess_smooth h_lap_prod t

/-- Ricci tensor evolution (pointwise extraction):
    ∂_t of Rc evaluated at constant X, Y equals the scalar ∂_t of Rc(X,Y). -/
theorem RicciFlowData.dt_Rc (D : RicciFlowData k R V Time A) (t : Time) (X Y : V) :
    tensor_eval (dt_tensor D.td t (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr)
      D.h_Rc_smooth) ![X, Y] ![] =
    D.td.dt_apply (fun s => tensor_eval (ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr) ![X, Y] ![]) t :=
  ricci_evolution_pointwise_extraction D.emb D.td D.atr D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth t X Y

/-- Ricci tensor evolution in Lichnerowicz form, extracted from a bundled equation hypothesis. -/
theorem RicciFlowData.dt_Rc_laplace_reaction (D : RicciFlowData k R V Time A)
    (rough reaction : Time -> TensorData R V 0 2)
    (h_evol : RicciLichnerowiczEvolutionEquation D.emb D.td D.atr D.conn_fam
      D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth rough reaction)
    (t : Time) (X Y : V) :
    tensor_eval (dt_tensor D.td t
      (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s)
        (D.hsl_fam s) (D.hl_fam s) D.atr)
      D.h_Rc_smooth) ![X, Y] ![] =
    rough t ![X, Y] ![] + reaction t ![X, Y] ![] :=
  ricci_evolution_from_lichnerowicz_equation_eval D.emb D.td D.atr D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_Rc_smooth rough reaction h_evol t X Y

end Equations
