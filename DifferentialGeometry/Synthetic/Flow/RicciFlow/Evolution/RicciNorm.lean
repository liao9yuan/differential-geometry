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

/-- Expansion of `|Rc - (R/n)g|^2` into the four bilinear terms. -/
theorem tracefree_ricci_norm_sq_expand
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ricciForm_tensor emb conn ha hal hsl hl atr) -
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor) -
      tensor_inner_02 met atr
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)
        (ricciForm_tensor emb conn ha hal hsl hl atr) +
      tensor_inner_02 met atr
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor)
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) • met.g_tensor) := by
  unfold tracefree_ricci_norm_sq tracefree_ricci_tensor
  rw [tensor_inner_02_sub_sub]

/-- Expansion of `|Rc - (R/n)g|^2` with scalar multiples pulled out. -/
theorem tracefree_ricci_norm_sq_expand_scalar
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        tensor_inner_02 met atr
          (ricciForm_tensor emb conn ha hal hsl hl atr) met.g_tensor -
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        tensor_inner_02 met atr met.g_tensor
          (ricciForm_tensor emb conn ha hal hsl hl atr) +
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
          tensor_inner_02 met atr met.g_tensor met.g_tensor) := by
  rw [tracefree_ricci_norm_sq_expand, tensor_inner_02_ricciForm]
  repeat rw [tensor_inner_02_smul_right]
  repeat rw [tensor_inner_02_smul_left]

/-- Closed trace-free Ricci norm expansion, assuming the missing metric-contraction bridge.

The hypotheses are exactly the remaining realization/contraction facts needed
to turn the algebraic expansion into the classical identity:
`<Rc,g> = R`, `<g,g> = dim`, and `nInv * dim = 1`. -/
theorem tracefree_ricci_norm_sq_expand_closed
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv dim : R)
    (h_Rc_g :
      tensor_inner_02 met atr
        (ricciForm_tensor emb conn ha hal hsl hl atr) met.g_tensor =
      ScalarCurvature emb conn ha hal hsl hl atr met)
    (h_g_g : tensor_inner_02 met atr met.g_tensor met.g_tensor = dim)
    (h_nInv_dim : nInv * dim = 1) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
        nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
          ScalarCurvature emb conn ha hal hsl hl atr met := by
  rw [tracefree_ricci_norm_sq_expand_scalar, h_Rc_g,
    tensor_inner_02_symm met atr met.g_tensor
      (ricciForm_tensor emb conn ha hal hsl hl atr),
    h_Rc_g, h_g_g]
  have h_last :
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
        ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * dim) =
      nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
        ScalarCurvature emb conn ha hal hsl hl atr met := by
    calc
      (nInv * ScalarCurvature emb conn ha hal hsl hl atr met) *
          ((nInv * ScalarCurvature emb conn ha hal hsl hl atr met) * dim)
          = (nInv * dim) *
              (nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
                ScalarCurvature emb conn ha hal hsl hl atr met) := by ring
      _ = 1 *
              (nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
                ScalarCurvature emb conn ha hal hsl hl atr met) := by rw [h_nInv_dim]
      _ = nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
            ScalarCurvature emb conn ha hal hsl hl atr met := by ring
  rw [h_last]
  ring

/-- Closed trace-free Ricci norm expansion using the abstract trace dimension `tr(id)`.

This removes the previously separate contraction bridge hypotheses:
`<Rc,g> = R` and `<g,g> = tr(id)` are now proved in `ScalarCurvature.lean`.
The only remaining dimension normalization is `nInv * tr(id) = 1`. -/
theorem tracefree_ricci_norm_sq_expand_abstractTraceDimension
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (nInv : R)
    (h_nInv_dim : nInv * abstractTraceDimension atr = 1) :
    tracefree_ricci_norm_sq emb conn ha hal hsl hl atr met nInv =
      ricci_norm_sq emb conn ha hal hsl hl atr met -
        nInv * ScalarCurvature emb conn ha hal hsl hl atr met *
          ScalarCurvature emb conn ha hal hsl hl atr met :=
  tracefree_ricci_norm_sq_expand_closed emb conn ha hal hsl hl atr met nInv
    (abstractTraceDimension atr)
    (tensor_inner_02_ricciForm_metric emb conn ha hal hsl hl atr met)
    (tensor_inner_02_metric_metric met atr)
    h_nInv_dim

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

