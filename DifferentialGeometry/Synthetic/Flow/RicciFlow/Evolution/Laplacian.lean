import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Synthetic.Operator.Hessian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Evolution of the Laplacian under Ricci Flow

- `hessian_raise_variation`: variation of the raised Hessian
- `laplacian_evolution`: ∂_t(Δu) = 2⟨Rc, Hess(u)⟩ + metric_trace(∂_t Hess)
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Hessian raise variation
-- ============================================================

section HessianRaise

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Hessian raise variation: the scalar time derivative of the raised Hessian
    observed through g(t).

    Same structure as ricci_raise_variation but for the Hessian form:
    ∂_t[g(t)(sharp_s(Hess_s(X,·)), Y)] = dt_tensor(Hess)(X,Y) - metric_var(sharp_t(Hess_t(X,·)), Y)

    Proof uses: g(s)(sharp_s(Hess_s(X,·)), Y) = Hess_s(X,Y) is the Hessian evaluation,
    which depends on s through the metric and connection. By the metric product rule,
    the time derivative decomposes into the metric variation and the g(t)-variation. -/
theorem hessian_raise_variation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (_atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V) 
    (conn_fam : Time → V → V → V)
    (_ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (_hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (_hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (_hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_mvp : MetricBilinProductRule td g_fam)
    (hessian_fam : Time → TensorData R V 0 2)
    (h_sharp_fam : Time → V → V)
    (h_sharp_spec : ∀ s X Y, (g_fam s).g (h_sharp_fam s X) Y = hessian_fam s ![X, Y] ![])
    (t : Time) (X Y : V) :
    td.dt_apply (fun s => (g_fam t).g (h_sharp_fam s X) Y) t =
    dt_tensor td t hessian_fam ![X, Y] ![] -
    metric_var_form td g_fam t ![h_sharp_fam t X, Y] ![] := by
  -- g(s)(sharp_s(Hess_s(X,·)), Y) = Hess_s(X, Y) for all s
  have h_feq : (fun s => (g_fam s).g (h_sharp_fam s X) Y) =
      (fun s => hessian_fam s ![X, Y] ![]) :=
    funext (fun s => h_sharp_spec s X Y)
  -- dt of LHS = dt of RHS
  have h_dt_eq : td.dt_apply (fun s => (g_fam s).g (h_sharp_fam s X) Y) t =
      td.dt_apply (fun s => hessian_fam s ![X, Y] ![]) t :=
    congr_arg (fun f => td.dt_apply f t) h_feq
  -- Product rule
  have h_prod := h_mvp (fun s => h_sharp_fam s X) Y t
  -- dt of hessian evaluations = dt_tensor(Hess) by definition
  change _ = td.dt_apply (fun s => hessian_fam s ![X, Y] ![]) t - _
  rw [h_dt_eq] at h_prod; rw [add_comm] at h_prod
  exact (sub_eq_of_eq_add h_prod).symm

end HessianRaise

-- ============================================================
-- Section 2: Laplacian evolution
-- ============================================================

section LaplacianEvolution

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The Laplacian product rule: ∂_t[metric_trace_s(Hess_s)] decomposes into
    a metric variation term and a Hessian variation term.

    Analogous to ScalarCurvatureProductRule but for the Hessian instead of Ricci.
    Combines TimeTrComm + metric product rule + trace-endomorphism relationship. -/
def LaplacianProductRule
    (_emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V) 
    (hessian_fam : Time → TensorData R V 0 2) : Prop :=
  ∀ t,
    td.dt_apply (fun s =>
      metric_trace (g_fam s) atr (0 : Fin 2) (0 : Fin 1) (hessian_fam s) ![] ![]) t =
    -tensor_inner_02 (g_fam t) atr
      (metric_var_form td g_fam t) (hessian_fam t) +
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor td t hessian_fam) ![] ![]

/-- Laplacian evolution under Ricci flow:

    ∂_t(Δu) = 2⟨Rc, Hess(u)⟩ + metric_trace_t(∂_t Hess)

    where ⟨Rc, Hess(u)⟩ = tr(Rc♯ ∘ Hess♯) is the tensor inner product,
    and the second term is the metric trace of the time derivative of the Hessian.

    The proof substitutes the Ricci flow equation (∂_t g = -2Rc) into the
    product rule and simplifies -⟨-2Rc, Hess(u)⟩ = 2⟨Rc, Hess(u)⟩. -/
theorem laplacian_evolution
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
    (hessian_fam : Time → TensorData R V 0 2)
    (h_lap_prod : LaplacianProductRule emb td atr g_fam hessian_fam)
    (t : Time) :
    td.dt_apply (fun s =>
      metric_trace (g_fam s) atr (0 : Fin 2) (0 : Fin 1) (hessian_fam s) ![] ![]) t =
    2 * tensor_inner_02 (g_fam t) atr
      (ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr)
      (hessian_fam t) +
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor td t hessian_fam) ![] ![] := by
  -- Apply the product rule
  have h_prod := h_lap_prod t
  -- Ricci flow: metric_var = -2 • Rc
  have h_rf_eq := h_rf.evolution t
  -- Compute -inner(-2•Rc, Hess) = 2*inner(Rc, Hess)
  have h_inner : -tensor_inner_02 (g_fam t) atr
      (metric_var_form td g_fam t) (hessian_fam t) =
    2 * tensor_inner_02 (g_fam t) atr
      (ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr)
      (hessian_fam t) := by
    rw [h_rf_eq, tensor_inner_02_smul_left]; ring
  rw [h_prod, h_inner]

end LaplacianEvolution
