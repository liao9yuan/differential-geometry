import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Synthetic.Operator.Gradient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Evolution of the Gradient under Ricci Flow

- `gradient_evolution`: ∂_t[g(t)(grad u, Y)] = 2 Rc(grad u, Y)
- `gradient_squared_evolution`: ∂_t|∇u|² = 2 Rc(∇u,∇u) + 2 g(∇u, ∇(∂_t u))
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Gradient evolution
-- ============================================================

section GradEvolution

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Gradient evolution under Ricci flow for a time-independent scalar u.

    g(s)(grad_s u, Y) = Y(u) is constant in s, so its total derivative is 0.
    By the metric product rule, 0 = (∂_t g)(grad_t u, Y) + ∂_t[g(t)(grad_s u, Y)].
    Under Ricci flow (∂_t g = -2Rc):
      ∂_t[g(t)(grad_s u, Y)] = 2 Rc(grad_t u, Y). -/
theorem gradient_evolution
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V) 
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_mvp : MetricBilinProductRule td g_fam)
    (u : R) (Y : V) (t : Time) :
    td.dt_apply (fun s => (g_fam t).g (grad emb (g_fam s) u) Y) t =
    2 * ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
      ![grad emb (g_fam t) u, Y] ![] := by
  -- g(s)(grad_s u, Y) = Y(u) is constant in s
  have h_const : (fun s => (g_fam s).g (grad emb (g_fam s) u) Y) =
      (fun _ => action emb Y u) :=
    funext (fun s => g_grad emb (g_fam s) u Y)
  -- ∂_t of constant = 0
  have h_zero : td.dt_apply (fun s => (g_fam s).g (grad emb (g_fam s) u) Y) t = 0 := by
    rw [h_const]; exact td.dt_apply_const (action emb Y u) t
  -- Product rule: 0 = metric_var(grad_t u, Y) + ∂_t[g(t)(grad_s u, Y)]
  have h_prod := h_mvp (fun s => grad emb (g_fam s) u) Y t
  rw [h_zero] at h_prod
  -- ∂_t[g(t)(grad_s u, Y)] = -metric_var(grad_t u, Y)
  have h_neg : td.dt_apply (fun s => (g_fam t).g (grad emb (g_fam s) u) Y) t =
    -metric_var_form td g_fam t ![grad emb (g_fam t) u, Y] ![] :=
    (neg_eq_of_add_eq_zero_right h_prod.symm).symm
  -- Substitute Ricci flow: metric_var = -2 • Rc
  rw [h_neg, h_rf.evolution t]; simp only [MultilinearMap.smul_apply, smul_eq_mul]; ring

end GradEvolution

-- ============================================================
-- Section 2: Gradient squared evolution
-- ============================================================

section GradSquaredEvolution

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Full metric product rule: both arguments varying.

    ∂_t[g(s)(A(s), B(s))] = metric_var(A(t), B(t))
      + ∂_t[g(t)(A(s), B(t))] + ∂_t[g(t)(A(t), B(s))] -/
def MetricFullProductRule
    (td : TimeDerivativeData R A Time)
    (g_fam : Time → MetricDuality R V) : Prop :=
  ∀ (A B : Time → V) (t : Time),
    td.dt_apply (fun s => (g_fam s).g (A s) (B s)) t =
    metric_var_form td g_fam t ![A t, B t] ![] +
    td.dt_apply (fun s => (g_fam t).g (A s) (B t)) t +
    td.dt_apply (fun s => (g_fam t).g (A t) (B s)) t

/-- Gradient squared evolution under Ricci flow:

    ∂_t|∇u|² = 2 Rc(∇u, ∇u) + 2 g(∇u, ∇(∂_t u)). -/
theorem gradient_squared_evolution
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V) 
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_mfp : MetricFullProductRule td g_fam)
    (h_st : SpatialTemporalComm emb td)
    (u : Time → R) (t : Time) :
    td.dt_apply (fun s => (g_fam s).g
      (grad emb (g_fam s) (u s))
      (grad emb (g_fam s) (u s))) t =
    2 * ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
      ![grad emb (g_fam t) (u t), grad emb (g_fam t) (u t)] ![] +
    2 * (g_fam t).g (grad emb (g_fam t) (u t))
                    (grad emb (g_fam t) (td.dt_apply u t)) := by
  set G := fun s => grad emb (g_fam s) (u s)
  set Z := G t
  -- Full product rule: ∂_t[g(G,G)] = metric_var(Z,Z) + 2*dt[g(t)(G(s),Z)]
  have h_prod := h_mfp G G t
  -- The two variation terms are equal by g-symmetry
  have h_sym : td.dt_apply (fun s => (g_fam t).g Z (G s)) t =
      td.dt_apply (fun s => (g_fam t).g (G s) Z) t := by
    show td.dt_apply (fun s => (g_fam t).g Z (G s)) t = _
    rw [show (fun s => (g_fam t).g Z (G s)) = (fun s => (g_fam t).g (G s) Z) from
      funext (fun s => (g_fam t).g_symm Z (G s))]
  have h_prod2 : td.dt_apply (fun s => (g_fam s).g (G s) (G s)) t =
      metric_var_form td g_fam t ![Z, Z] ![] +
      2 * td.dt_apply (fun s => (g_fam t).g (G s) Z) t := by
    rw [h_prod, h_sym]; ring
  -- dt[g(s)(G(s), Z)] = metric_var(Z,Z) + dt[g(t)(G(s),Z)] (from full product rule with const Z)
  have h_bprod : td.dt_apply (fun s => (g_fam s).g (G s) Z) t =
      metric_var_form td g_fam t ![Z, Z] ![] +
      td.dt_apply (fun s => (g_fam t).g (G s) Z) t := by
    have h := h_mfp G (fun _ => Z) t
    have h0 : td.dt_apply (fun s => (g_fam t).g Z ((fun _ => Z) s)) t = 0 :=
      td.dt_apply_const ((g_fam t).g Z Z) t
    rw [h0] at h; rw [h]; ring
  -- g(s)(G(s), Z) = action(Z, u(s)) by gradient identity
  have h_gyz : (fun s => (g_fam s).g (G s) Z) = (fun s => action emb Z (u s)) :=
    funext (fun s => g_grad emb (g_fam s) (u s) Z)
  -- dt[g(s)(G(s),Z)] = action(Z, dt(u)) by SpatialTemporalComm
  have h_dt_action : td.dt_apply (fun s => (g_fam s).g (G s) Z) t =
      action emb Z (td.dt_apply u t) := by
    rw [h_gyz]; exact h_st Z u t
  -- dt[g(t)(G(s), Z)] = action(Z, dt(u)) - metric_var(Z,Z)
  have h_var : td.dt_apply (fun s => (g_fam t).g (G s) Z) t =
      action emb Z (td.dt_apply u t) - metric_var_form td g_fam t ![Z, Z] ![] := by
    have h := h_bprod; rw [h_dt_action] at h
    rw [add_comm] at h; exact (sub_eq_of_eq_add h).symm
  -- Substitute into h_prod2
  have h_combined : td.dt_apply (fun s => (g_fam s).g (G s) (G s)) t =
      2 * action emb Z (td.dt_apply u t) - metric_var_form td g_fam t ![Z, Z] ![] := by
    rw [h_prod2, h_var]; ring
  -- action(Z, dt(u)) = g(t)(grad_t(dt(u)), Z) = g(t)(Z, grad_t(dt(u)))
  have h_action_grad : action emb Z (td.dt_apply u t) =
      (g_fam t).g Z (grad emb (g_fam t) (td.dt_apply u t)) := by
    rw [(g_fam t).g_symm]; exact (g_grad emb (g_fam t) (td.dt_apply u t) Z).symm
  -- Under Ricci flow: metric_var = -2 • Rc
  rw [h_combined, h_action_grad, h_rf.evolution t]
  simp only [MultilinearMap.smul_apply, smul_eq_mul]; ring

end GradSquaredEvolution
