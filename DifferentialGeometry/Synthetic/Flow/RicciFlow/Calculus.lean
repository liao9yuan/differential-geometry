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

variable (k R V Time : Type*)
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Bundled Ricci flow data: geometric structures and connecting
    properties needed for the evolution equations. -/
structure RicciFlowData where
  emb : DerivationEmbedding k R V
  td : TimeDerivativeData R Time
  atr : AbstractTrace R V
  g_fam : Time → MetricDuality R V
  conn_fam : Time → V → V → V
  ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z
  hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z
  hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z
  hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y
  h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
  h_st : SpatialTemporalComm emb td
  h_mvp : MetricBilinProductRule td g_fam
  h_mfp : MetricFullProductRule td g_fam
  h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam

end RicciFlowData

-- ============================================================
-- Evolution Equations from RicciFlowData
-- ============================================================

section Equations

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Scalar curvature evolution under Ricci flow:
    ∂_t R = 2|Rc|² + metric_trace_g(t)(∂_t Rc).

    Extracted from `scalar_curvature_evolution` using the bundled data. -/
theorem RicciFlowData.dt_R (D : RicciFlowData k R V Time) (t : Time) :
    (D.td.dt (fun s => ScalarCurvature D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr (D.g_fam s))) t =
    2 * ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) +
    metric_trace (D.g_fam t) D.atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor D.td t (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr)) ![] ![] :=
  scalar_curvature_evolution D.emb D.td D.atr D.g_fam D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf D.h_sc_prod t

/-- Gradient evolution under Ricci flow for a time-independent scalar:
    ∂_t[g(t)(grad_s u, Y)] = 2 Rc(grad_t u, Y). -/
theorem RicciFlowData.dt_grad (D : RicciFlowData k R V Time)
    (u : R) (Y : V) (t : Time) :
    (D.td.dt (fun s => (D.g_fam t).g (grad D.emb (D.g_fam s) u) Y)) t =
    2 * ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr
      ![grad D.emb (D.g_fam t) u, Y] ![] :=
  gradient_evolution D.emb D.td D.atr D.g_fam D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf D.h_mvp u Y t

/-- Gradient squared evolution under Ricci flow:
    ∂_t|∇u|² = 2 Rc(∇u,∇u) + 2 g(∇u, ∇(∂_t u)). -/
theorem RicciFlowData.dt_grad_sq (D : RicciFlowData k R V Time)
    (u : Time → R) (t : Time) :
    (D.td.dt (fun s => (D.g_fam s).g
      (grad D.emb (D.g_fam s) (u s))
      (grad D.emb (D.g_fam s) (u s)))) t =
    2 * ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr
      ![grad D.emb (D.g_fam t) (u t), grad D.emb (D.g_fam t) (u t)] ![] +
    2 * (D.g_fam t).g (grad D.emb (D.g_fam t) (u t))
                      (grad D.emb (D.g_fam t) ((D.td.dt u) t)) :=
  gradient_squared_evolution D.emb D.td D.atr D.g_fam D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf D.h_mfp D.h_st u t

/-- Laplacian evolution under Ricci flow:
    ∂_t(Δu) = 2⟨Rc, Hess(u)⟩ + metric_trace_t(∂_t Hess). -/
theorem RicciFlowData.dt_laplacian (D : RicciFlowData k R V Time)
    (hessian_fam : Time → TensorData R V 0 2)
    (h_lap_prod : LaplacianProductRule D.emb D.td D.atr D.g_fam hessian_fam)
    (t : Time) :
    (D.td.dt (fun s =>
      metric_trace (D.g_fam s) D.atr (0 : Fin 2) (0 : Fin 1) (hessian_fam s) ![] ![])) t =
    2 * tensor_inner_02 (D.g_fam t) D.atr
      (ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr)
      (hessian_fam t) +
    metric_trace (D.g_fam t) D.atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor D.td t hessian_fam) ![] ![] :=
  laplacian_evolution D.emb D.td D.atr D.g_fam D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam D.h_rf hessian_fam h_lap_prod t

/-- Ricci tensor evolution (pointwise extraction):
    ∂_t of Rc evaluated at constant X, Y equals the scalar ∂_t of Rc(X,Y). -/
theorem RicciFlowData.dt_Rc (D : RicciFlowData k R V Time) (t : Time) (X Y : V) :
    tensor_eval (dt_tensor D.td t (fun s => ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr)) ![X, Y] ![] =
    (D.td.dt (fun s => tensor_eval (ricciForm_tensor D.emb (D.conn_fam s) (D.ha_fam s) (D.hal_fam s) (D.hsl_fam s) (D.hl_fam s) D.atr) ![X, Y] ![])) t :=
  ricci_evolution_pointwise_extraction D.emb D.td D.atr D.conn_fam
    D.ha_fam D.hal_fam D.hsl_fam D.hl_fam t X Y

end Equations
