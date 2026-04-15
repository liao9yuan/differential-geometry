import DifferentialGeometry.Synthetic.Operator.Hessian
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.SecondCovariantDerivative
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Bochner-Weitzenböck Identity

Pointwise Bochner identity and supporting lemmas.
-/

open SyntheticTensor

section BochnerDefs

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

-- ============================================================
-- Metric helpers
-- ============================================================

private lemma g_sub_left (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C := by
  rw [sub_eq_add_neg, met.g_add_left,
      show -B = (-1 : R) • B from (neg_one_smul R B).symm, met.g_smul_left]; ring

-- ============================================================
-- 1. grad_norm_sq_deriv
-- ============================================================

/-- X(g(∇f, ∇f)) = 2g(∇_X∇f, ∇f). -/
lemma grad_norm_sq_deriv
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V) (met : MetricDuality R V) 
    (h_mc : IsMetricCompatible emb conn met)
    (f : R) (X : V) :
    action emb X (met.g (grad emb met f) (grad emb met f)) =
    met.g (conn X (grad emb met f)) (grad emb met f) +
    met.g (conn X (grad emb met f)) (grad emb met f) := by
  have h := h_mc X (grad emb met f) (grad emb met f)
  unfold action
  rw [h, met.g_symm (grad emb met f) (conn X (grad emb met f))]

-- ============================================================
-- 2. hessian_commute_ricci
-- ============================================================

/-- ∇_X(∇_Y(∇f)) = ∇_Y(∇_X(∇f)) + ∇_{[X,Y]}(∇f) + Rm(X,Y)(∇f). -/
lemma hessian_commute_ricci
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn) (met : MetricDuality R V) 
    (f : R) (X Y : V) :
    conn X (conn Y (grad emb met f)) =
    conn Y (conn X (grad emb met f)) +
    conn (bracket emb X Y) (grad emb met f) +
    Rm emb conn X Y (grad emb met f) := by
  set gf := grad emb met f
  have h := ricci_identity emb conn conn_add_left h_tf X Y gf
  simp only [secondCovDerivCommutator] at h
  rw [h_tf X Y] at h
  calc conn X (conn Y gf)
      = conn X (conn Y gf) - conn Y (conn X gf) - conn (bracket emb X Y) gf
        + conn Y (conn X gf) + conn (bracket emb X Y) gf := by abel
    _ = Rm emb conn X Y gf + conn Y (conn X gf) + conn (bracket emb X Y) gf := by rw [h]
    _ = conn Y (conn X gf) + conn (bracket emb X Y) gf + Rm emb conn X Y gf := by abel

-- ============================================================
-- 3. hessian_norm_sq_grad
-- ============================================================

/-- Hess(|∇f|², X, Y) = 2g(∇²_{X,Y}∇f, ∇f) + 2g(∇_X∇f, ∇_Y∇f). -/
lemma hessian_norm_sq_grad
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V) (met : MetricDuality R V) 
    (h_mc : IsMetricCompatible emb conn met)
    (f : R) (X Y : V) :
    Hess emb conn (met.g (grad emb met f) (grad emb met f)) X Y =
    2 * met.g (secondCovDeriv conn X Y (grad emb met f)) (grad emb met f) +
    2 * met.g (conn X (grad emb met f)) (conn Y (grad emb met f)) := by
  set gf := grad emb met f
  -- Metric compatibility instances
  have mc_Y := h_mc Y gf gf
  have mc_X := h_mc X (conn Y gf) gf
  have mc_XY := h_mc (conn X Y) gf gf
  -- Symmetry rewrites
  rw [met.g_symm gf (conn Y gf)] at mc_Y
  rw [met.g_symm gf (conn (conn X Y) gf)] at mc_XY
  rw [met.g_symm (conn Y gf) (conn X gf)] at mc_X
  -- X(Y(g(gf,gf))) via mc_Y + map_add
  have hXY : (emb.embed X) ((emb.embed Y) (met.g gf gf)) =
      (emb.embed X) (met.g (conn Y gf) gf) + (emb.embed X) (met.g (conn Y gf) gf) := by
    rw [mc_Y]; exact (emb.embed X).map_add _ _
  -- Proof by calc, staying at the Hess/secondCovDeriv level
  calc Hess emb conn (met.g gf gf) X Y
      = action emb X (action emb Y (met.g gf gf)) - action emb (conn X Y) (met.g gf gf) := rfl
    _ = (emb.embed X) ((emb.embed Y) (met.g gf gf)) - (emb.embed (conn X Y)) (met.g gf gf) := rfl
    _ = ((emb.embed X) (met.g (conn Y gf) gf) + (emb.embed X) (met.g (conn Y gf) gf)) -
        (met.g (conn (conn X Y) gf) gf + met.g (conn (conn X Y) gf) gf) := by rw [hXY, mc_XY]
    _ = (met.g (conn X (conn Y gf)) gf + met.g (conn X gf) (conn Y gf)) +
        (met.g (conn X (conn Y gf)) gf + met.g (conn X gf) (conn Y gf)) -
        (met.g (conn (conn X Y) gf) gf + met.g (conn (conn X Y) gf) gf) := by rw [mc_X]
    _ = 2 * (met.g (conn X (conn Y gf)) gf - met.g (conn (conn X Y) gf) gf) +
        2 * met.g (conn X gf) (conn Y gf) := by ring
    _ = 2 * met.g (secondCovDeriv conn X Y gf) gf +
        2 * met.g (conn X gf) (conn Y gf) := by
        congr 2; dsimp [secondCovDeriv]; rw [g_sub_left met]

-- ============================================================
-- 4. hessian_metric_symm
-- ============================================================

/-- g(∇_A ∇f, B) = g(∇_B ∇f, A) via Hess symmetry + metric compat. -/
private lemma hessian_metric_symm
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V) (met : MetricDuality R V) 
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (f : R) (A B : V) :
    met.g (conn A (grad emb met f)) B =
    met.g (conn B (grad emb met f)) A := by
  set gf := grad emb met f
  -- Helper: g(W, gf) = action W f for any W
  have g_gf : ∀ W : V, met.g W gf = action emb W f := by
    intro W; rw [met.g_symm]; exact g_grad emb met f W
  -- g(∇_A gf, B) = Hess(f)(A, B)
  -- Prove g(conn W gf, U) = Hess f W U for any W, U via metric compat
  have g_conn_hess : ∀ W U : V, met.g (conn W gf) U = Hess emb conn f W U := by
    intro W U
    have mc := h_mc W U gf
    rw [g_gf U, g_gf (conn W U)] at mc
    -- mc: (embed W)(action U f) = action (conn W U) f + g(U, conn W gf)
    -- Need: g(conn W gf, U) = Hess f W U = action W (action U f) - action (conn W U) f
    -- From mc: g(U, conn W gf) = (embed W)(action U f) - action (conn W U) f
    -- g(conn W gf, U) = g(U, conn W gf) by symm
    -- Hess f W U = action W (action U f) - action (conn W U) f by definition
    -- These are the same since action = embed applied.
    -- But mc has (emb.embed W) while Hess has action emb W. They're defeq.
    -- Let's just use: g(conn W gf, U) = g(U, conn W gf) and mc gives g(U, conn W gf) = X - Y.
    -- Hess f W U = X - Y by definition.
    rw [met.g_symm (conn W gf) U]
    -- goal: g(U, conn W gf) = Hess f W U
    -- Hess f W U = action W (action U f) - action (conn W U) f
    -- mc: (emb.embed W) (action U f) = action (conn W U) f + g(U, conn W gf)
    -- action W (...) = (emb.embed W) (...) definitionally
    -- So: g(U, conn W gf) = (emb.embed W)(action U f) - action (conn W U) f = Hess f W U
    dsimp [Hess, action]
    -- goal now: g(U, conn W gf) = (emb.embed W)((emb.embed U) f) - (emb.embed (conn W U)) f
    -- mc (after unfold action in rw): (emb.embed W)((emb.embed U) f) = (emb.embed (conn W U)) f + g(U, conn W gf)
    -- So g(U, conn W gf) = LHS - (emb.embed (conn W U)) f. QED by algebra.
    -- Since we can't use linarith, let's use sub_eq algebra:
    unfold action at mc
    -- mc: X = Y + Z, goal: Z = X - Y
    exact eq_sub_of_add_eq (by rw [add_comm]; exact mc.symm)
  rw [g_conn_hess A B, g_conn_hess B A, hessian_symm emb conn h_tf]

-- ============================================================
-- 5. secondCovDeriv_weitzenbock
-- ============================================================

/-- g(∇²_{X,Y}∇f, ∇f) = g(∇²_{∇f,X}∇f, Y) - g(Rm(X,∇f)Y, ∇f). -/
lemma secondCovDeriv_weitzenbock
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (_hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) 
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : ∀ (a : R), 2 * a = 0 → a = 0)
    (f : R) (X Y : V) :
    met.g (secondCovDeriv conn X Y (grad emb met f)) (grad emb met f) =
    met.g (secondCovDeriv conn (grad emb met f) X (grad emb met f)) Y -
    met.g (Rm emb conn X (grad emb met f) Y) (grad emb met f) := by
  set gf := grad emb met f
  have hms : ∀ A B : V, met.g (conn A gf) B = met.g (conn B gf) A :=
    hessian_metric_symm emb conn met h_mc h_tf f
  -- Expand secondCovDeriv's
  have lhs_expand : met.g (secondCovDeriv conn X Y gf) gf =
      met.g (conn X (conn Y gf)) gf - met.g (conn (conn X Y) gf) gf := by
    dsimp [secondCovDeriv]; exact g_sub_left met _ _ _
  have rhs_expand : met.g (secondCovDeriv conn X gf gf) Y =
      met.g (conn X (conn gf gf)) Y - met.g (conn (conn X gf) gf) Y := by
    dsimp [secondCovDeriv]; exact g_sub_left met _ _ _
  -- Metric compat
  have mc1 := h_mc X (conn Y gf) gf
  have mc2 := h_mc X (conn gf gf) Y
  -- Hessian symmetry instances
  have hsym1 : met.g (conn Y gf) gf = met.g (conn gf gf) Y := hms Y gf
  have hsym2 : met.g (conn (conn X Y) gf) gf = met.g (conn gf gf) (conn X Y) := hms (conn X Y) gf
  have hsym3 : met.g (conn (conn X gf) gf) Y = met.g (conn Y gf) (conn X gf) := hms (conn X gf) Y
  -- X acts on equal expressions
  have hsym1_action : (emb.embed X) (met.g (conn Y gf) gf) = (emb.embed X) (met.g (conn gf gf) Y) := by
    rw [hsym1]
  -- Step 1: g(∇²_{X,Y}gf, gf) = g(∇²_{X,gf}gf, Y)
  have step1 : met.g (secondCovDeriv conn X Y gf) gf = met.g (secondCovDeriv conn X gf gf) Y := by
    have key : met.g (conn X (conn Y gf)) gf + met.g (conn Y gf) (conn X gf) =
               met.g (conn X (conn gf gf)) Y + met.g (conn gf gf) (conn X Y) := by
      calc met.g (conn X (conn Y gf)) gf + met.g (conn Y gf) (conn X gf)
          = (emb.embed X) (met.g (conn Y gf) gf) := mc1.symm
        _ = (emb.embed X) (met.g (conn gf gf) Y) := hsym1_action
        _ = met.g (conn X (conn gf gf)) Y + met.g (conn gf gf) (conn X Y) := mc2
    rw [← hsym3, ← hsym2] at key
    -- key: a + b = c + f ⟹ a - f = c - b
    -- Use lhs_expand and rhs_expand as substitutions via calc
    calc met.g (secondCovDeriv conn X Y gf) gf
        = met.g (conn X (conn Y gf)) gf - met.g (conn (conn X Y) gf) gf := lhs_expand
      _ = met.g (conn X (conn gf gf)) Y - met.g (conn (conn X gf) gf) Y := by
          linear_combination key
      _ = met.g (secondCovDeriv conn X gf gf) Y := rhs_expand.symm
  -- Step 2: Ricci identity: ∇²_{X,gf} - ∇²_{gf,X} = Rm(X,gf)
  have ricci_id : secondCovDeriv conn X gf gf =
      secondCovDeriv conn gf X gf + Rm emb conn X gf gf := by
    have h_comm := ricci_identity emb conn conn_add_left h_tf X gf gf
    simp only [secondCovDerivCommutator] at h_comm
    rw [h_tf X gf] at h_comm
    dsimp [secondCovDeriv]
    -- h_comm: conn X (conn gf gf) - conn gf (conn X gf) - conn (bracket emb X gf) gf = Rm X gf gf
    -- Need: conn X (conn gf gf) - conn (conn X gf) gf =
    --   (conn gf (conn X gf) - conn (conn gf X) gf) + Rm X gf gf
    -- i.e. conn X (conn gf gf) - conn (conn X gf) gf =
    --   conn gf (conn X gf) - conn (conn gf X) gf + (conn X (conn gf gf) - conn gf (conn X gf) - conn (bracket emb X gf) gf)
    -- We need conn (conn X gf) gf - conn (conn gf X) gf = conn (bracket emb X gf) gf
    -- by conn_add_left + torsion free: conn X gf - conn gf X = bracket emb X gf
    have htf_Xgf := h_tf X gf -- conn X gf - conn gf X = bracket emb X gf
    -- conn (conn X gf) gf = conn (conn gf X + bracket emb X gf) gf
    --                      = conn (conn gf X) gf + conn (bracket emb X gf) gf
    have h_split : conn (conn X gf) gf = conn (conn gf X) gf + conn (bracket emb X gf) gf := by
      have : conn X gf = conn gf X + bracket emb X gf := by
        have := eq_add_of_sub_eq htf_Xgf; rwa [add_comm] at this
      rw [this, conn_add_left]
    -- h_comm: X(gf(gf)) - gf(X(gf)) - [X,gf](gf) = Rm(X,gf)gf (V-valued)
    -- h_split: (conn X gf)(gf) = (conn gf X)(gf) + (bracket X gf)(gf) (V-valued)
    -- Need: X(gf(gf)) - (conn X gf)(gf) = gf(X(gf)) - (conn gf X)(gf) + Rm(X,gf)(gf) (V-valued)
    -- Substitute h_split into the goal to eliminate (conn X gf)(gf)
    rw [h_split]
    -- h_comm: A - B - C = D (V-valued). Need: A = B + C + D, then A - (E + C) = (B - E) + D
    -- Direct proof via sub manipulation on h_comm
    have h_eq : conn X (conn gf gf) =
        conn gf (conn X gf) + conn (bracket emb X gf) gf + Rm emb conn X gf gf := by
      have h := h_comm
      -- h: conn X (conn gf gf) - conn gf (conn X gf) - conn (bracket emb X gf) gf = Rm emb conn X gf gf
      -- Rearrange: conn X (conn gf gf) = conn gf (conn X gf) + conn (bracket emb X gf) gf + Rm ...
      calc conn X (conn gf gf)
          = conn X (conn gf gf) - conn gf (conn X gf) - conn (bracket emb X gf) gf
            + conn gf (conn X gf) + conn (bracket emb X gf) gf := by abel
        _ = Rm emb conn X gf gf + conn gf (conn X gf) + conn (bracket emb X gf) gf := by rw [h]
        _ = conn gf (conn X gf) + conn (bracket emb X gf) gf + Rm emb conn X gf gf := by abel
    rw [h_eq]; abel
  -- Step 3: Rm block symmetry: g(Rm(X,gf)gf, Y) = -g(Rm(X,gf)Y, gf)
  have rm_flip : met.g (Rm emb conn X gf gf) Y = - met.g (Rm emb conn X gf Y) gf := by
    -- Block symmetry: g(Rm(X,gf)gf, Y) = g(Rm(gf,Y)X, gf)
    have h_block1 := Rm_symm_blocks emb conn ha conn_add_left met h_mc h_tf h2 X gf gf Y
    -- Antisymmetry: Rm(gf,Y) = -Rm(Y,gf)
    have h_anti : Rm emb conn gf Y X = -(Rm emb conn Y gf X) := Rm_antisymm emb conn conn_add_left gf Y X
    have h_neg : met.g (Rm emb conn gf Y X) gf = -met.g (Rm emb conn Y gf X) gf := by
      rw [h_anti, show -(Rm emb conn Y gf X) = (-1 : R) • Rm emb conn Y gf X
        from (neg_one_smul R _).symm, met.g_smul_left]; ring
    -- Block symmetry: g(Rm(Y,gf)X, gf) = g(Rm(X,gf)Y, gf)
    have h_block2 := Rm_symm_blocks emb conn ha conn_add_left met h_mc h_tf h2 Y gf X gf
    -- Chain: g(Rm(X,gf)gf, Y) = g(Rm(gf,Y)X, gf) [h_block1]
    --      = -g(Rm(Y,gf)X, gf) [h_neg]
    --      = -g(Rm(X,gf)Y, gf) [h_block2]
    calc met.g (Rm emb conn X gf gf) Y
        = met.g (Rm emb conn gf Y X) gf := h_block1
      _ = -met.g (Rm emb conn Y gf X) gf := h_neg
      _ = -met.g (Rm emb conn X gf Y) gf := by rw [h_block2]
  -- Combine
  calc met.g (secondCovDeriv conn X Y gf) gf
    _ = met.g (secondCovDeriv conn X gf gf) Y := step1
    _ = met.g (secondCovDeriv conn gf X gf + Rm emb conn X gf gf) Y := by rw [ricci_id]
    _ = met.g (secondCovDeriv conn gf X gf) Y + met.g (Rm emb conn X gf gf) Y :=
        met.g_add_left _ _ _
    _ = met.g (secondCovDeriv conn gf X gf) Y - met.g (Rm emb conn X gf Y) gf := by
        rw [rm_flip]; ring

-- ============================================================
-- 6. Bochner pointwise identity
-- ============================================================

/-- Pointwise Bochner-Weitzenböck identity:
    Hess(|∇f|², X, Y) = 2g(∇²_{∇f,X}∇f, Y) - 2g(Rm(X,∇f)Y, ∇f) + 2g(∇_X∇f, ∇_Y∇f).

    The trace of the first term gives g(∇f, ∇(Δf)) + Rc(∇f, ∇f),
    the trace of the second gives -Rc(∇f, ∇f) (absorbed),
    and the trace of the third gives |∇²f|².
    Combined: Δ|∇f|² = 2|∇²f|² + 2Rc(∇f, ∇f) + 2g(∇f, ∇(Δf)). -/
theorem bochner_pointwise
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) 
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : ∀ (a : R), 2 * a = 0 → a = 0)
    (f : R) (X Y : V) :
    Hess emb conn (met.g (grad emb met f) (grad emb met f)) X Y =
    2 * met.g (secondCovDeriv conn (grad emb met f) X (grad emb met f)) Y -
    2 * met.g (Rm emb conn X (grad emb met f) Y) (grad emb met f) +
    2 * met.g (conn X (grad emb met f)) (conn Y (grad emb met f)) := by
  have h_norm := hessian_norm_sq_grad emb conn met h_mc f X Y
  have h_wb := secondCovDeriv_weitzenbock emb conn ha conn_add_left hl met h_mc h_tf h2 f X Y
  rw [h_norm, h_wb]; ring

end BochnerDefs
