import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Evolution of the Connection under Ricci Flow
-/

open SyntheticTensor

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The covariant derivative of the Ricci form at time t:
    (∇_X Ric)(Y, Z) = X(Ric(Y,Z)) - Ric(∇_X Y, Z) - Ric(Y, ∇_X Z). -/
noncomputable def ricci_cov_deriv
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Y Z : V) : R :=
  action emb X (Rc emb conn ha hal hsl hl atr Y Z)
  - Rc emb conn ha hal hsl hl atr (conn X Y) Z
  - Rc emb conn ha hal hsl hl atr Y (conn X Z)

/-- Helper: smul evaluation for ricciForm_tensor. -/
private lemma ricciForm_smul_eval
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (c : R) (P Q : V) :
    (c • ricciForm_tensor emb conn ha hal hsl hl atr) ![P, Q] ![] =
    c * Rc emb conn ha hal hsl hl atr P Q := by
  simp [MultilinearMap.smul_apply, smul_eq_mul, ricciForm_tensor_eval]

/-- Connection evolution under Ricci flow (combined metric + connection variation):

    dt(s → g(s)(conn(s)_X Y, Z))(t) =
      -(∇_X Ric)(Y,Z) - (∇_Y Ric)(X,Z) + (∇_Z Ric)(X,Y) + mvf(conn(t)_X Y, Z)

    This follows directly from the Palatini identity and the Ricci flow equation. -/
theorem connection_evolution_combined
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (h_emb_met : ∀ (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_lc : ∀ s, IsLeviCivita emb (conn_fam s) (g_fam s))
    [Invertible (2 : R)]
    (X Y Z : V) (t : Time)
    (h_conn_smooth : td.isSmoothFam (fun s => (g_fam s).g (conn_fam s X Y) Z)) :
    td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t =
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr X Y Z
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Y X Z
    + ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Z X Y
    + metric_var_form td g_fam h_met t ![conn_fam t X Y, Z] ![] := by
  -- Abbreviations
  set rcd := ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
  set n := conn_fam t
  -- Step 1: Get evolution equation
  have evol := h_rf.evolution t
  -- Step 2: Evaluate metric_var_form at specific vectors via the evolution equation
  have eval_eq : ∀ P Q : V,
    metric_var_form td g_fam h_met t ![P, Q] ![] =
    (-2 : R) * Rc emb n (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr P Q := by
    intro P Q
    have h1 : metric_var_form td g_fam h_met t ![P, Q] ![] =
      ((-2 : R) • ricciForm_tensor emb n (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr) ![P, Q] ![] := by
      show (metric_var_form td g_fam h_met t) ![P, Q] ![] =
        ((-2 : R) • ricciForm_tensor emb n (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr) ![P, Q] ![]
      rw [← evol]
    rw [h1, ricciForm_smul_eval]
  -- Step 3: h_cov_deriv = -2 * rcd
  have h_eq : ∀ A B C : V,
    h_cov_deriv emb td g_fam h_met n t A B C = (-2 : R) * rcd A B C := by
    intro A B C
    simp only [h_cov_deriv, rcd, ricci_cov_deriv]
    rw [eval_eq B C, eval_eq (n A B) C, eval_eq B (n A C)]
    -- Show X(-2 * f) = -2 * X(f) using Leibniz + X(const) = 0
    set rc_val := Rc emb n (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr B C
    have hact : (emb.embed A) ((-2 : R) * rc_val) = (-2 : R) * (emb.embed A) rc_val := by
      have := (emb.embed A).leibniz (-2 : R) rc_val
      simp only [smul_eq_mul] at this
      rw [this]
      have h0 : (emb.embed A) (-2 : R) = 0 := by
        rw [show (-2 : R) = -(2 : R) from by ring, map_neg]
        have h2 : (emb.embed A) (2 : R) = 0 := by
          rw [show (2 : R) = algebraMap k R (2 : k) from by simp [map_ofNat]]
          exact Derivation.map_algebraMap (emb.embed A) (2 : k)
        rw [h2, neg_zero]
      rw [h0, mul_zero, add_zero]
    simp only [action]; rw [hact]; ring
  -- Step 4: Apply Palatini identity
  have palatini := connection_variation emb td h_st g_fam h_met h_emb_met conn_fam
    ha_fam hal_fam hl_fam
    (fun s => (h_lc s).1) (fun s => (h_lc s).2) X Y Z t h_conn_smooth
  rw [h_eq X Y Z, h_eq Y X Z, h_eq Z X Y] at palatini
  -- Step 5: Factor algebra and cancel 2
  have algebra :
    (-2 : R) * rcd X Y Z + (-2 : R) * rcd Y X Z - (-2 : R) * rcd Z X Y +
    2 * metric_var_form td g_fam h_met t ![n X Y, Z] ![] =
    2 * (-rcd X Y Z - rcd Y X Z + rcd Z X Y +
         metric_var_form td g_fam h_met t ![n X Y, Z] ![]) := by ring
  rw [algebra] at palatini
  suffices h : td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t -
    (-rcd X Y Z - rcd Y X Z + rcd Z X Y + metric_var_form td g_fam h_met t ![n X Y, Z] ![]) = 0 from
    eq_of_sub_eq_zero h
  apply char_ne_2_of_invertible_two
  calc 2 * (td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t -
    (-rcd X Y Z - rcd Y X Z + rcd Z X Y + metric_var_form td g_fam h_met t ![n X Y, Z] ![]))
      = 2 * td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t -
        2 * (-rcd X Y Z - rcd Y X Z + rcd Z X Y + metric_var_form td g_fam h_met t ![n X Y, Z] ![]) := by ring
    _ = 0 := by rw [palatini]; ring

/-- Connection evolution (pure connection variation, using metric product rule):
    dt(s → g(t)(conn(s)_X Y, Z))(t) = -(∇_X Ric)(Y,Z) - (∇_Y Ric)(X,Z) + (∇_Z Ric)(X,Y).

    The hypothesis `h_decomp` is the metric product rule, which splits the time
    derivative of g(s)(V(s), W) into a metric-variation term and a pure-vector term. -/
theorem connection_evolution
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (h_emb_met : ∀ (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_lc : ∀ s, IsLeviCivita emb (conn_fam s) (g_fam s))
    [Invertible (2 : R)]
    (t : Time)
    -- Metric product rule: splitting dt(g(s)(V(s), W)) into metric and vector parts
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam h_met t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (X Y Z : V)
    (h_conn_smooth : td.isSmoothFam (fun s => (g_fam s).g (conn_fam s X Y) Z)) :
    td.dt_apply (fun s => (g_fam t).g (conn_fam s X Y) Z) t =
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr X Y Z
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Y X Z
    + ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Z X Y := by
  have h_combined := connection_evolution_combined emb td h_st atr g_fam h_met h_emb_met
    conn_fam ha_fam hal_fam hsl_fam hl_fam h_rf h_lc X Y Z t h_conn_smooth
  have h_split := h_decomp (fun s => conn_fam s X Y) Z
  -- h_combined: dt_apply(g(s)(conn(s)XY, Z)) = -rcd_X - rcd_Y + rcd_Z + mvf
  -- h_split:    dt_apply(g(s)(conn(s)XY, Z)) = mvf(conn(t)XY, Z) + dt_apply(g(t)(conn(s)XY, Z))
  -- Therefore:  dt_apply(g(t)(conn(s)XY, Z)) = -rcd_X - rcd_Y + rcd_Z
  calc td.dt_apply (fun s => (g_fam t).g (conn_fam s X Y) Z) t
      = td.dt_apply (fun s => (g_fam s).g (conn_fam s X Y) Z) t -
        metric_var_form td g_fam h_met t ![conn_fam t X Y, Z] ![] := by rw [h_split]; ring
    _ = (-ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr X Y Z -
         ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Y X Z +
         ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr Z X Y +
         metric_var_form td g_fam h_met t ![conn_fam t X Y, Z] ![]) -
        metric_var_form td g_fam h_met t ![conn_fam t X Y, Z] ![] := by rw [h_combined]
    _ = _ := by ring
