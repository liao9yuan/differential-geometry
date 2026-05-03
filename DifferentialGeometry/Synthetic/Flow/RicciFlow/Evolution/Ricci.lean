import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Evolution of Ricci Curvature
-/

open SyntheticTensor

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The time derivative of the Ricci tensor evaluated at constant vectors X, Y
    equals the scalar time derivative of Rc(X,Y).

    In the transparent tensor framework, this is immediate from `dt_tensor_eval`
    which holds by `rfl`. -/
theorem ricci_evolution_pointwise_extraction
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) atr vs αs))
    (t : Time) (X Y : V) :
    tensor_eval (dt_tensor td t
      (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr)
      h_Rc_smooth) ![X, Y] ![] =
    td.dt_apply (fun s => tensor_eval (ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr) ![X, Y] ![]) t := by
  rfl

-- ============================================================
-- Section 2: Full Ricci evolution interface
-- ============================================================

section RicciEvolutionInterface

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Interface for the full Ricci evolution equation.

The intended `rhs` is the Lichnerowicz/heat expression appearing in
`RicciFlow/main.tex`. Keeping this as a named interface lets downstream scalar
and pinching modules depend on the equation before the contraction proof is
completed. -/
def RicciEvolutionEquation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (rhs : Time -> TensorData R V 0 2) : Prop :=
  forall t,
    dt_tensor td t
      (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr)
      h_Rc_smooth = rhs t

theorem ricci_evolution_from_equation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (rhs : Time -> TensorData R V 0 2)
    (h_evol : RicciEvolutionEquation emb td atr conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth rhs)
    (t : Time) :
    dt_tensor td t
      (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr)
      h_Rc_smooth = rhs t :=
  h_evol t

theorem ricci_evolution_from_equation_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (rhs : Time -> TensorData R V 0 2)
    (h_evol : RicciEvolutionEquation emb td atr conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth rhs)
    (t : Time) (X Y : V) :
    tensor_eval
      (dt_tensor td t
        (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s) atr)
        h_Rc_smooth) ![X, Y] ![] =
    tensor_eval (rhs t) ![X, Y] ![] := by
  rw [h_evol t]

end RicciEvolutionInterface
