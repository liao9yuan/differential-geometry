import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Analysis.TimeOnTensors
import DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Derivatives and Variation

Metric variation form, covariant derivative of the variation,
and the Palatini identity.
-/

open SyntheticTensor

-- ============================================================
-- Metric helpers
-- ============================================================

section MetricZero
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

lemma metric_zero_right (met : MetricDuality R V) (X : V) : met.g X 0 = 0 := by
  have h := met.g_smul_right (0 : R) X (0 : V); simp only [zero_smul, zero_mul] at h; exact h

lemma metric_zero_left (met : MetricDuality R V) (X : V) : met.g 0 X = 0 := by
  rw [met.g_symm]; exact metric_zero_right met X

end MetricZero

-- ============================================================
-- Metric variation form
-- ============================================================

section MetricVariation

variable {R V Time : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Metric variation form: ∂_t(g_tensor). -/
noncomputable def metric_var_form
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (t : Time) : TensorData R V 0 2 :=
  dt_tensor td t (fun s => (g_fam s).g_tensor)

lemma metric_var_form_eval
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (t : Time) (X Y : V) :
    metric_var_form td g_fam t ![X, Y] ![] =
    (td.dt (fun s => (g_fam s).g X Y)) t :=
  rfl

/-- Symmetry of the metric variation. -/
lemma metric_var_form_symm
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (t : Time) (A B : V) :
    metric_var_form td g_fam t ![A, B] ![] =
    metric_var_form td g_fam t ![B, A] ![] := by
  change (td.dt (fun s => (g_fam s).g A B)) t = (td.dt (fun s => (g_fam s).g B A)) t
  have : (fun s => (g_fam s).g A B) = (fun s => (g_fam s).g B A) :=
    funext (fun s => (g_fam s).g_symm A B)
  rw [this]

end MetricVariation

-- ============================================================
-- h_cov_deriv
-- ============================================================

section CovDerivH

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The covariant derivative of h = ∂_t g:
    (∇_X h)(Y, Z) = X(h(Y, Z)) - h(∇_X Y, Z) - h(Y, ∇_X Z). -/
noncomputable def h_cov_deriv
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (conn : V → V → V)
    (t : Time) (X Y Z : V) : R :=
  action emb X (metric_var_form td g_fam t ![Y, Z] ![])
  - metric_var_form td g_fam t ![conn X Y, Z] ![]
  - metric_var_form td g_fam t ![Y, conn X Z] ![]

end CovDerivH

-- ============================================================
-- Palatini identity (connection_variation)
-- ============================================================

section Palatini

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Helper: metric_var_form is additive in second slot. -/
private lemma mvf_sub_right
    (td : TimeDerivativeData R Time) (g_fam : Time → MetricDuality R V) (t : Time)
    (A B C : V) :
    metric_var_form td g_fam t ![A, B - C] ![] =
    metric_var_form td g_fam t ![A, B] ![] - metric_var_form td g_fam t ![A, C] ![] := by
  change (td.dt (fun s => (g_fam s).g A (B - C))) t =
       (td.dt (fun s => (g_fam s).g A B)) t - (td.dt (fun s => (g_fam s).g A C)) t
  have h_eq : (fun s => (g_fam s).g A (B - C)) =
      (fun s => (g_fam s).g A B) - (fun s => (g_fam s).g A C) := by
    funext s; change (g_fam s).g A (B - C) = (g_fam s).g A B - (g_fam s).g A C
    rw [show B - C = B + (-1 : R) • C from by rw [neg_one_smul, sub_eq_add_neg]]
    rw [(g_fam s).g_add_right, (g_fam s).g_smul_right]; ring
  rw [h_eq]; exact congr_fun (map_sub td.dt _ _) t

/-- Palatini identity: differentiate the Koszul formula with respect to time.

    Statement: for a family of Levi-Civita connections conn_fam(s) of g_fam(s),

    2 * dt(s ↦ g(s)(conn(s) X Y, Z))(t) =
      h_cov(X,Y,Z) + h_cov(Y,X,Z) - h_cov(Z,X,Y) + 2 * h(conn(t) X Y, Z)

    where h = metric_var_form(t) and h_cov is its covariant derivative.

    Equivalently (solving for the "pure connection variation"):
    2 * [dt(g(s)(conn(s) X Y, Z)) - h(conn(t) X Y, Z)] = h_cov_sum. -/
theorem connection_variation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (h_st : SpatialTemporalComm emb td)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z : V, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z : V, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_mc : ∀ s, IsMetricCompatible emb (conn_fam s) (g_fam s))
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (X Y Z : V) (t : Time) :
    2 * (td.dt (fun s => (g_fam s).g (conn_fam s X Y) Z)) t =
    h_cov_deriv emb td g_fam (conn_fam t) t X Y Z +
    h_cov_deriv emb td g_fam (conn_fam t) t Y X Z -
    h_cov_deriv emb td g_fam (conn_fam t) t Z X Y +
    2 * metric_var_form td g_fam t ![conn_fam t X Y, Z] ![] := by
  -- Abbreviations
  let h (A B : V) := metric_var_form td g_fam t ![A, B] ![]
  let n := conn_fam t

  -- Koszul formula at each time s
  have koszul_eq : ∀ s,
      2 * (g_fam s).g (conn_fam s X Y) Z =
        (emb.embed X) ((g_fam s).g Y Z) + (emb.embed Y) ((g_fam s).g Z X)
        - (emb.embed Z) ((g_fam s).g X Y)
        - (g_fam s).g X (bracket emb Y Z)
        + (g_fam s).g Y (bracket emb Z X)
        + (g_fam s).g Z (bracket emb X Y) :=
    fun s => levi_civita_uniqueness emb (conn_fam s) (ha_fam s) (hal_fam s) (hl_fam s)
      (g_fam s) (h_mc s) (h_tf s) X Y Z

  -- Step 1: dt of LHS = dt of RHS (by functional equality)
  have h_base :
      (td.dt (fun s => 2 * (g_fam s).g (conn_fam s X Y) Z)) t =
      (td.dt (fun s =>
        (emb.embed X) ((g_fam s).g Y Z) + (emb.embed Y) ((g_fam s).g Z X)
        - (emb.embed Z) ((g_fam s).g X Y)
        - (g_fam s).g X (bracket emb Y Z)
        + (g_fam s).g Y (bracket emb Z X)
        + (g_fam s).g Z (bracket emb X Y))) t := by
    have : (fun s => 2 * (g_fam s).g (conn_fam s X Y) Z) = (fun s =>
        (emb.embed X) ((g_fam s).g Y Z) + (emb.embed Y) ((g_fam s).g Z X)
        - (emb.embed Z) ((g_fam s).g X Y)
        - (g_fam s).g X (bracket emb Y Z)
        + (g_fam s).g Y (bracket emb Z X)
        + (g_fam s).g Z (bracket emb X Y)) :=
      funext (fun s => koszul_eq s)
    rw [this]

  -- Step 2: Pull 2 out of LHS
  have hLHS_smul :
      (td.dt (fun s => 2 * (g_fam s).g (conn_fam s X Y) Z)) t =
      2 * (td.dt (fun s => (g_fam s).g (conn_fam s X Y) Z)) t := by
    have h_eq : (fun s => 2 * (g_fam s).g (conn_fam s X Y) Z) =
        algebraMap R (Time → R) 2 * (fun s => (g_fam s).g (conn_fam s X Y) Z) := rfl
    rw [h_eq]; exact congr_fun (dt_smul_const td 2 _) t

  -- Step 3: Differentiate RHS using SpatialTemporalComm and dt linearity
  -- ∂_t(X(g(s)(A,B))) = X(∂_t(g(s)(A,B))) = X(h(A,B))
  have pt_action : ∀ (W A B : V),
      (td.dt (fun s => (emb.embed W) ((g_fam s).g A B))) t =
      (emb.embed W) (h A B) := by
    intro W A B; exact h_st W (fun s => (g_fam s).g A B) t

  -- ∂_t(g(s)(A, constant)) for constant A, constant B = h(A, B) by definition
  have h_eval : ∀ (A B : V),
      (td.dt (fun s => (g_fam s).g A B)) t = h A B := fun A B => rfl

  -- Differentiate each of the 6 Koszul terms
  have hRHS :
      (td.dt (fun s =>
        (emb.embed X) ((g_fam s).g Y Z) + (emb.embed Y) ((g_fam s).g Z X)
        - (emb.embed Z) ((g_fam s).g X Y)
        - (g_fam s).g X (bracket emb Y Z)
        + (g_fam s).g Y (bracket emb Z X)
        + (g_fam s).g Z (bracket emb X Y))) t =
      (emb.embed X) (h Y Z) + (emb.embed Y) (h Z X) - (emb.embed Z) (h X Y)
      - h X (bracket emb Y Z) + h Y (bracket emb Z X) + h Z (bracket emb X Y) := by
    have h_fun : (fun s =>
        (emb.embed X) ((g_fam s).g Y Z) + (emb.embed Y) ((g_fam s).g Z X)
        - (emb.embed Z) ((g_fam s).g X Y)
        - (g_fam s).g X (bracket emb Y Z)
        + (g_fam s).g Y (bracket emb Z X)
        + (g_fam s).g Z (bracket emb X Y)) =
        (fun s => (emb.embed X) ((g_fam s).g Y Z))
        + (fun s => (emb.embed Y) ((g_fam s).g Z X))
        - (fun s => (emb.embed Z) ((g_fam s).g X Y))
        - (fun s => (g_fam s).g X (bracket emb Y Z))
        + (fun s => (g_fam s).g Y (bracket emb Z X))
        + (fun s => (g_fam s).g Z (bracket emb X Y)) := by
      funext s; simp only [Pi.add_apply, Pi.sub_apply]
    rw [h_fun, map_add, map_add, map_sub, map_sub, map_add]
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [pt_action X Y Z, pt_action Y Z X, pt_action Z X Y,
        h_eval X (bracket emb Y Z), h_eval Y (bracket emb Z X),
        h_eval Z (bracket emb X Y)]

  -- Combine: 2 * dt(g(s)(conn(s) X Y, Z)) = differentiated Koszul
  rw [hLHS_smul] at h_base; rw [h_base, hRHS]

  -- Step 4: Rewrite differentiated Koszul in terms of h_cov_deriv
  -- Using torsion-free to decompose brackets
  have torsion_free : ∀ A B : V, n A B - n B A = bracket emb A B := h_tf t

  have b1 : h X (bracket emb Y Z) = h X (n Y Z) - h X (n Z Y) := by
    rw [← torsion_free Y Z]; exact mvf_sub_right td g_fam t X (n Y Z) (n Z Y)
  have b2 : h Y (bracket emb Z X) = h Y (n Z X) - h Y (n X Z) := by
    rw [← torsion_free Z X]; exact mvf_sub_right td g_fam t Y (n Z X) (n X Z)
  have b3 : h Z (bracket emb X Y) = h Z (n X Y) - h Z (n Y X) := by
    rw [← torsion_free X Y]; exact mvf_sub_right td g_fam t Z (n X Y) (n Y X)

  -- h_cov_deriv sum expands
  have eq_cov :
      h_cov_deriv emb td g_fam n t X Y Z +
      h_cov_deriv emb td g_fam n t Y X Z -
      h_cov_deriv emb td g_fam n t Z X Y =
        (emb.embed X) (h Y Z) - h (n X Y) Z - h Y (n X Z) +
        ((emb.embed Y) (h X Z) - h (n Y X) Z - h X (n Y Z)) -
        ((emb.embed Z) (h X Y) - h (n Z X) Y - h X (n Z Y)) := by
    dsimp [h_cov_deriv, action]

  -- Symmetry
  have a1 : h (n X Y) Z = h Z (n X Y) := metric_var_form_symm td g_fam t _ _
  have a2 : h (n Y X) Z = h Z (n Y X) := metric_var_form_symm td g_fam t _ _
  have a3 : h (n Z X) Y = h Y (n Z X) := metric_var_form_symm td g_fam t _ _

  -- h symmetry to align Koszul argument order with eq_cov
  have hZX_eq : h Z X = h X Z := metric_var_form_symm td g_fam t Z X

  -- Rewrite eq_cov to use h(Z,X) instead of h(X,Z) so it matches Koszul
  have eq_cov' :
      h_cov_deriv emb td g_fam n t X Y Z +
      h_cov_deriv emb td g_fam n t Y X Z -
      h_cov_deriv emb td g_fam n t Z X Y =
        (emb.embed X) (h Y Z) - h (n X Y) Z - h Y (n X Z) +
        ((emb.embed Y) (h Z X) - h (n Y X) Z - h X (n Y Z)) -
        ((emb.embed Z) (h X Y) - h (n Z X) Y - h X (n Z Y)) := by
    rw [eq_cov, ← hZX_eq]

  -- Key algebraic step
  have step_rhs :
      (emb.embed X) (h Y Z) + (emb.embed Y) (h Z X) - (emb.embed Z) (h X Y)
      - h X (bracket emb Y Z) + h Y (bracket emb Z X) + h Z (bracket emb X Y) =
      h_cov_deriv emb td g_fam n t X Y Z +
      h_cov_deriv emb td g_fam n t Y X Z -
      h_cov_deriv emb td g_fam n t Z X Y + 2 * h Z (n X Y) := by
    rw [eq_cov', b1, b2, b3, a1, a2, a3]; ring

  -- Note: in the Koszul formula, the second argument of (emb.embed Y) is g(Z, X),
  -- but h(Z, X) matches because h_eval gives ∂_t(g(s)(Z, X)) = h(Z, X).
  rw [step_rhs]
  -- Goal: 2 * ∂_t(g(s)(conn(s) X Y, Z)) = h_cov_sum + 2 * h(Z, nXY)
  -- We need to add 2 * h(n X Y, Z) = 2 * h(Z, n X Y) to both sides.
  -- Actually the goal already matches with the "+2*h(conn_fam t X Y, Z)" term!
  rw [show h Z (n X Y) = metric_var_form td g_fam t ![conn_fam t X Y, Z] ![] from
    metric_var_form_symm td g_fam t Z (conn_fam t X Y)]

end Palatini

-- ============================================================
-- nabla_fam abbreviation
-- ============================================================

section NablaFam

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The Levi-Civita connection of a time-dependent metric family at time t. -/
noncomputable abbrev nabla_fam
    (emb : DerivationEmbedding k R V)
    (g_fam : Time → MetricDuality R V)
    [Invertible (2 : R)] (t : Time) : V → V → V :=
  koszul_connection emb (g_fam t)

end NablaFam

-- ============================================================
-- raise_variation
-- ============================================================

section RaiseVariation

variable {R V Time : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Key identity: g(s)(sharp_s(α), Y) is constant in s when α is time-independent.
    Therefore its time derivative is zero. -/
theorem raise_variation_const
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (T : TensorData R V 0 2) (X Y : V) (t : Time) :
    (td.dt (fun s => (g_fam s).g ((g_fam s).sharp (flat_covector T X)) Y)) t = 0 := by
  have h_const : (fun s => (g_fam s).g ((g_fam s).sharp (flat_covector T X)) Y) =
      algebraMap R (Time → R) (T ![X, Y] ![]) := by
    funext s; exact (g_fam s).g_sharp (flat_covector T X) Y
  rw [h_const]; exact congr_fun (t_const_R td (T ![X, Y] ![])) t

/-- Raise variation: g(t)(∂_t(raise T X), Y) = -(∂_t g)(raise_t T X, Y).

    From raise_variation_const, ∂_t[g(s)(sharp_s(T X), Y)] = 0.
    Given a decomposition hypothesis (product rule for varying metric + varying vector),
    we obtain the standard raise variation identity. -/
theorem raise_variation
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (T : TensorData R V 0 2) (X Y : V) (t : Time)
    (h_decomp : (td.dt (fun s => (g_fam s).g ((g_fam s).sharp (flat_covector T X)) Y)) t =
      metric_var_form td g_fam t ![((g_fam t).sharp (flat_covector T X)), Y] ![] +
      (td.dt (fun s => (g_fam t).flat Y ((g_fam s).sharp (flat_covector T X)))) t) :
    (td.dt (fun s => (g_fam t).flat Y ((g_fam s).sharp (flat_covector T X)))) t =
    - metric_var_form td g_fam t ![((g_fam t).sharp (flat_covector T X)), Y] ![] := by
  have h0 := raise_variation_const td g_fam T X Y t
  rw [h0] at h_decomp
  -- h_decomp : 0 = A + B, so B + A = 0, giving -A = B, i.e. B = -A
  exact (neg_eq_of_add_eq_zero_left ((add_comm _ _).trans h_decomp.symm)).symm

end RaiseVariation

-- ============================================================
-- tr_g_variation
-- ============================================================

section TrGVariation

variable {R V Time : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Time derivative of metric trace for a FIXED (0,2)-tensor T.
    Since metric_trace involves raise_index (which uses g_inv),
    when g varies, the trace varies through g_inv.

    For a fixed T, ∂_t(g^{ij}(s) T_{ij}) depends on ∂_t(g^{ij}).
    This is recorded as a definitional equality when metric_trace
    is expanded via raise_index + contract_general. -/
theorem tr_g_variation
    (td : TimeDerivativeData R Time)
    (g_fam : Time → MetricDuality R V)
    (atr : AbstractTrace R V)
    (T : TensorData R V 0 2)
    (idx₁ : Fin 2) (idx₂ : Fin 1)
    (t : Time) :
    (td.dt (fun s =>
      (metric_trace (g_fam s) atr idx₁ idx₂ T) ![] ![])) t =
    dt_tensor td t (fun s =>
      metric_trace (g_fam s) atr idx₁ idx₂ T) ![] ![] := by
  rfl

end TrGVariation
