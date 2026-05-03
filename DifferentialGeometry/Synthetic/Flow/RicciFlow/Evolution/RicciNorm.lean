import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Norm and Trace-Free Ricci Interfaces

This module collects the algebraic objects needed for the pinching part of
`RicciFlow/main.tex`: the trace-free Ricci tensor, its squared norm, and named
evolution-equation interfaces.
-/

open SyntheticTensor

section TracefreeRicci

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Trace-free Ricci tensor, with `nInv` standing for `1 / n`. -/
noncomputable def tracefree_ricci_tensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    TensorData R V 0 2 :=
  ricciForm_tensor emb conn ha hal hsl hl atr -
    ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)

theorem tracefree_ricci_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) (X Y : V) :
    tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv ![X, Y] ![] =
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Y] ![] -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * met.g X Y := by
  simp [tracefree_ricci_tensor, MetricDuality.g, smul_eq_mul]

/-- Squared norm of trace-free Ricci. -/
noncomputable def tracefree_ricci_norm_sq
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) : R :=
  tensor_inner_02 met atr
    (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv)
    (tracefree_ricci_tensor emb conn ha hal hsl hl atr met nInv)

end TracefreeRicci

section NormEvolutionInterfaces

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Interface for the Ricci norm evolution equation. -/
def RicciNormEvolutionEquation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (rhs : Time -> R) : Prop :=
  forall t,
    td.dt_apply (fun s =>
      ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
        atr (g_fam s)) t = rhs t

theorem ricci_norm_evolution_from_interface
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (rhs : Time -> R)
    (h : RicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam rhs)
    (t : Time) :
    td.dt_apply (fun s =>
      ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
        atr (g_fam s)) t = rhs t :=
  h t

/-- Interface for the trace-free Ricci norm evolution equation. -/
def TracefreeRicciNormEvolutionEquation
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) (rhs : Time -> R) : Prop :=
  forall t,
    td.dt_apply (fun s =>
      tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s) nInv) t = rhs t

theorem tracefree_ricci_norm_evolution_from_interface
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (nInv : R) (rhs : Time -> R)
    (h : TracefreeRicciNormEvolutionEquation emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam nInv rhs)
    (t : Time) :
    td.dt_apply (fun s =>
      tracefree_ricci_norm_sq emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s) nInv) t = rhs t :=
  h t

end NormEvolutionInterfaces

