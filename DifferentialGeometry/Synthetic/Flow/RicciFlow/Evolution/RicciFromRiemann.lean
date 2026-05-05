import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciTraceCoordinate

/-!
# Ricci Evolution from Riemann Evolution

This file contains the constructors which contract Riemann evolution,
commute the Ricci-slot trace through time differentiation, and produce the
explicit Ricci evolution equation.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open SyntheticTensor

section RicciEvolutionInterface

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Lemma 6.3 from the Riemann evolution equation plus the three necessary
trace reductions.

Mathematically this is the standard proof:
trace `∂ₜ Rm = ΔRm + Q(Rm)` in the Ricci slots, commute the trace through
`∂ₜ`, identify the traced rough Laplacian with `Δ Ric`, and reduce the traced
Hamilton quadratic to `2 R_{ikjℓ} Ric^{kℓ} - 2 Ric_i{}^k Ric_{kj}`. -/
theorem ricci_pointwise_explicit_evolution_from_riemann_trace
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
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_dt_trace : forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
            (hl_fam s)) h_Rm_smooth) ![X, Y] ![])
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare := by
  intro t X Y
  let roughRm :=
    rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
      (hsl_fam t) atr (g_fam t)
  let qRm :=
    Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
      (hl_fam t) atr (g_fam t)
  rw [h_dt_trace t X Y]
  have hRm_eval :
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
            (hl_fam s)) h_Rm_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr (roughRm + qRm) ![X, Y] ![] := by
    simpa [roughRm, qRm] using
      congr_arg (fun T => riemann_to_ricci_trace atr T ![X, Y] ![]) (h_riemann t)
  rw [hRm_eval]
  have h_add_eval :
      riemann_to_ricci_trace atr (roughRm + qRm) ![X, Y] ![] =
        (riemann_to_ricci_trace atr roughRm +
          riemann_to_ricci_trace atr qRm) ![X, Y] ![] := by
    exact congr_arg (fun T : TensorData R V 0 2 => T ![X, Y] ![]) (by
      simpa [riemann_to_ricci_trace] using
        (contract_general_add atr (0 : Fin 1) (1 : Fin 3) roughRm qRm))
  rw [h_add_eval]
  simp only [MultilinearMap.add_apply]
  rw [show riemann_to_ricci_trace atr roughRm ![X, Y] ![] = rough t ![X, Y] ![] by
      simpa [roughRm] using h_rough_trace t X Y,
    show riemann_to_ricci_trace atr qRm ![X, Y] ![] =
        2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![] by
      simpa [qRm] using h_quadratic_trace t X Y]
  ring

/-- Pointwise explicit Ricci evolution from Riemann evolution, with the
`h_dt_trace` step discharged by the coordinate Ricci-slot trace constructor
above. The remaining trace reductions are the rough-Laplacian trace and the
quadratic reaction trace. -/
theorem ricci_pointwise_explicit_evolution_from_riemann_trace_coordinate_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α])
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare :=
  ricci_pointwise_explicit_evolution_from_riemann_trace emb td atr g_fam conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
    rough riemannRicci ricciSquare h_riemann
    (ricci_dt_trace_from_coordinate_trace emb td atr h_eval h_tt conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
      dRmEndo h_dRmEndo_eval)
    h_rough_trace h_quadratic_trace

/-- Pointwise explicit Ricci evolution from Riemann evolution, with the
time-derivative trace step supplied by the named Riemann derivative slice. -/
theorem ricci_pointwise_explicit_evolution_from_riemann_trace_slice_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth)
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare :=
  ricci_pointwise_explicit_evolution_from_riemann_trace_coordinate_dt emb td atr
    h_eval h_tt g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_Rc_smooth h_Rm_smooth D.endo D.eval_endo
    rough riemannRicci ricciSquare h_riemann h_rough_trace h_quadratic_trace

/-- The Hamilton-form Riemann evolution theorem packaged in exactly the shape
needed as the `h_riemann` input of the Ricci trace bridge. -/
theorem ricci_riemann_evolution_hamilton_input
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs alphas, td.isSmoothFam (fun tau => (g_fam tau).g_tensor vs alphas))
    (h_emb_met : forall (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : forall (A : V) (f : Time -> R),
      td.isSmoothFam f -> td.isSmoothFam (fun tau => (emb.embed A) (f tau)))
    (h_tf : forall s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : forall (a : R), (2 : R) * a = 0 -> a = 0)
    (h_decomp : forall t (F : Time -> V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
        metric_var_form td g_fam h_met t ![F t, W] ![] +
        td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (h_conn_smooth : forall (U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau U W)))
    (h_g_conn_smooth : forall (U W : V) (psi : V),
      td.isSmoothFam (fun s => (g_fam s).g (conn_fam s U W) psi))
    (h_nested_smooth : forall (P U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau P (conn_fam tau U W))))
    (h_Rm_smooth : forall vs alphas, td.isSmoothFam
      (fun tau => Rm_tensor emb (conn_fam tau) (ha_fam tau) (hal_fam tau)
        (hsl_fam tau) (hl_fam tau) vs alphas))
    (h_nabla_Ttau_YZ : forall (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam tau Y Z)) vs alphas))
    (h_nabla_Tt_YZ : forall (t' : Time) (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam t' Y Z)) vs alphas))
    (h_nabla_Tconst : forall (X Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) Z) vs alphas)) :
    forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t) := by
  intro t
  exact riemann_tensor_evolution_hamilton emb td h_st atr g_fam h_met h_emb_met conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_pr h_emb_closure h_tf h_rf h2 t
    (h_decomp t) h_conn_smooth h_g_conn_smooth h_nested_smooth h_Rm_smooth
    h_nabla_Ttau_YZ h_nabla_Tt_YZ h_nabla_Tconst

/-- Pointwise explicit Ricci evolution with the Riemann evolution and rough
trace inputs discharged by named constructors.

The only remaining geometric algebra input is
`RiemannToRicciQuadraticTraceDecomposition`, i.e. the traced Hamilton
quadratic reduction to `2 Rm*Ric - 2 Ric^2`. -/
theorem ricci_pointwise_explicit_evolution_from_hamilton_riemann_trace
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs alphas, td.isSmoothFam (fun tau => (g_fam tau).g_tensor vs alphas))
    (h_emb_met : forall (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs alphas, td.isSmoothFam
      (fun tau => ricciForm_tensor emb (conn_fam tau) (ha_fam tau) (hal_fam tau)
        (hsl_fam tau) (hl_fam tau) atr vs alphas))
    (h_Rm_smooth : forall vs alphas, td.isSmoothFam
      (fun tau => Rm_tensor emb (conn_fam tau) (ha_fam tau) (hal_fam tau)
        (hsl_fam tau) (hl_fam tau) vs alphas))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth)
    (Qd : RiemannToRicciQuadraticTraceDecomposition emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : forall (A : V) (f : Time -> R),
      td.isSmoothFam f -> td.isSmoothFam (fun tau => (emb.embed A) (f tau)))
    (h_tf : forall s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : forall (a : R), (2 : R) * a = 0 -> a = 0)
    (h_decomp : forall t (F : Time -> V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
        metric_var_form td g_fam h_met t ![F t, W] ![] +
        td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (h_conn_smooth : forall (U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau U W)))
    (h_g_conn_smooth : forall (U W : V) (psi : V),
      td.isSmoothFam (fun s => (g_fam s).g (conn_fam s U W) psi))
    (h_nested_smooth : forall (P U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau P (conn_fam tau U W))))
    (h_nabla_Ttau_YZ : forall (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam tau Y Z)) vs alphas))
    (h_nabla_Tt_YZ : forall (t' : Time) (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam t' Y Z)) vs alphas))
    (h_nabla_Tconst : forall (X Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) Z) vs alphas)) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth
      (riemann_to_ricci_rough_trace emb atr g_fam conn_fam
        ha_fam hal_fam hsl_fam hl_fam)
      Qd.riemannRicci Qd.ricciSquare :=
  ricci_pointwise_explicit_evolution_from_riemann_trace_slice_dt emb td atr
    h_eval h_tt g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_Rc_smooth h_Rm_smooth D
    (riemann_to_ricci_rough_trace emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam)
    Qd.riemannRicci Qd.ricciSquare
    (ricci_riemann_evolution_hamilton_input emb td h_st atr g_fam h_met h_emb_met
      conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_emb_closure h_tf h_rf h2
      h_decomp h_conn_smooth h_g_conn_smooth h_nested_smooth h_Rm_smooth
      h_nabla_Ttau_YZ h_nabla_Tt_YZ h_nabla_Tconst)
    (riemann_to_ricci_rough_trace_eval emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam)
    (riemann_to_ricci_quadratic_trace_of_decomposition emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam Qd)

/-- Pointwise explicit Ricci evolution from Hamilton's Riemann evolution,
specialized to the canonical Lemma 6.3 reaction tensors.

After the time-derivative trace and rough trace bridges, the remaining input is
the single canonical quadratic trace identity
`RiemannToRicciCanonicalQuadraticTrace` at each time. -/
theorem ricci_pointwise_explicit_evolution_from_hamilton_riemann_canonical_trace
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs alphas, td.isSmoothFam (fun tau => (g_fam tau).g_tensor vs alphas))
    (h_emb_met : forall (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs alphas, td.isSmoothFam
      (fun tau => ricciForm_tensor emb (conn_fam tau) (ha_fam tau) (hal_fam tau)
        (hsl_fam tau) (hl_fam tau) atr vs alphas))
    (h_Rm_smooth : forall vs alphas, td.isSmoothFam
      (fun tau => Rm_tensor emb (conn_fam tau) (ha_fam tau) (hal_fam tau)
        (hsl_fam tau) (hl_fam tau) vs alphas))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth)
    (h_trace : forall t,
      RiemannToRicciCanonicalQuadraticTrace emb (conn_fam t) (ha_fam t)
        (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t))
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : forall (A : V) (f : Time -> R),
      td.isSmoothFam f -> td.isSmoothFam (fun tau => (emb.embed A) (f tau)))
    (h_tf : forall s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : forall (a : R), (2 : R) * a = 0 -> a = 0)
    (h_decomp : forall t (F : Time -> V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
        metric_var_form td g_fam h_met t ![F t, W] ![] +
        td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (h_conn_smooth : forall (U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau U W)))
    (h_g_conn_smooth : forall (U W : V) (psi : V),
      td.isSmoothFam (fun s => (g_fam s).g (conn_fam s U W) psi))
    (h_nested_smooth : forall (P U W : V) (beta : V →ₗ[R] R),
      td.isSmoothFam (fun tau => beta (conn_fam tau P (conn_fam tau U W))))
    (h_nabla_Ttau_YZ : forall (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam tau Y Z)) vs alphas))
    (h_nabla_Tt_YZ : forall (t' : Time) (X Y Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) (conn_fam t' Y Z)) vs alphas))
    (h_nabla_Tconst : forall (X Z : V) (vs : Fin 0 -> V)
        (alphas : Fin 1 -> V →ₗ[R] R),
      td.isSmoothFam (fun tau => nabla_tensor emb (conn_fam tau) (ha_fam tau)
        (hl_fam tau) X (vectorToData (R := R) Z) vs alphas)) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth
      (riemann_to_ricci_rough_trace emb atr g_fam conn_fam
        ha_fam hal_fam hsl_fam hl_fam)
      (fun t => riemannRicciReactionTensor emb (conn_fam t) (ha_fam t)
        (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t))
      (fun t => ricciSquareTensor emb (conn_fam t) (ha_fam t)
        (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t)) :=
  ricci_pointwise_explicit_evolution_from_hamilton_riemann_trace emb td h_st atr
    h_eval h_tt g_fam h_met h_emb_met conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_Rc_smooth h_Rm_smooth D
    (riemannToRicciQuadraticTraceDecomposition_of_canonical emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_trace)
    h_pr h_emb_closure h_tf h_rf h2 h_decomp h_conn_smooth h_g_conn_smooth
    h_nested_smooth h_nabla_Ttau_YZ h_nabla_Tt_YZ h_nabla_Tconst

/-- Upgrade the pointwise Lemma 6.3 calculation to the tensor-level explicit
Ricci evolution equation. -/
theorem ricci_explicit_evolution_from_pointwise
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
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_pointwise :
      RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
        hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare) :
    RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare := by
  intro t
  ext vs αs
  have hvs : ![vs 0, vs 1] = vs := by
    ext i
    fin_cases i <;> rfl
  have hαs : (![] : Fin 0 -> V →ₗ[R] R) = αs := by
    ext i
    exact i.elim0
  rw [← hvs, ← hαs]
  rw [ricci_lichnerowicz_laplacian_rhs_eval]
  exact h_pointwise t (vs 0) (vs 1)

/-- Tensor-level Lemma 6.3 from Riemann evolution plus the trace reductions. -/
theorem ricci_explicit_evolution_from_riemann_trace
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
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_dt_trace : forall t X Y,
      tensor_eval
        (dt_tensor td t
          (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
            (hsl_fam s) (hl_fam s) atr)
          h_Rc_smooth) ![X, Y] ![] =
      riemann_to_ricci_trace atr
        (dt_tensor td t
          (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
            (hl_fam s)) h_Rm_smooth) ![X, Y] ![])
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare := by
  exact ricci_explicit_evolution_from_pointwise emb td atr conn_fam ha_fam hal_fam hsl_fam
    hl_fam h_Rc_smooth rough riemannRicci ricciSquare
    (ricci_pointwise_explicit_evolution_from_riemann_trace emb td atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth h_Rm_smooth
      rough riemannRicci ricciSquare h_riemann h_dt_trace h_rough_trace h_quadratic_trace)

/-- Tensor-level explicit Ricci evolution from Riemann evolution, with the
time-derivative trace step supplied by `ricci_dt_trace_from_coordinate_trace`. -/
theorem ricci_explicit_evolution_from_riemann_trace_coordinate_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (dRmEndo : Time -> V -> V -> V →ₗ[R] V)
    (h_dRmEndo_eval : forall t X Y Z (α : V →ₗ[R] R),
      α (dRmEndo t X Y Z) =
        tensor_eval
          (dt_tensor td t
            (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
              (hsl_fam s) (hl_fam s))
            h_Rm_smooth) ![X, Z, Y] ![α])
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare :=
  ricci_explicit_evolution_from_pointwise emb td atr conn_fam ha_fam hal_fam hsl_fam
    hl_fam h_Rc_smooth rough riemannRicci ricciSquare
    (ricci_pointwise_explicit_evolution_from_riemann_trace_coordinate_dt emb td atr
      h_eval h_tt g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth h_Rm_smooth dRmEndo h_dRmEndo_eval
      rough riemannRicci ricciSquare h_riemann h_rough_trace h_quadratic_trace)

/-- Tensor-level explicit Ricci evolution from Riemann evolution, with the
time-derivative trace step supplied by the named Riemann derivative slice. -/
theorem ricci_explicit_evolution_from_riemann_trace_slice_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (h_tt : TimeTrComm atr td)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_Rm_smooth : forall vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) vs αs))
    (D : RiemannTimeDerivativeSliceEndomorphism emb td conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rm_smooth)
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_riemann : forall t,
      dt_tensor td t
        (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s)) h_Rm_smooth =
      rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
        (hsl_fam t) atr (g_fam t) +
      Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t))
    (h_rough_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t)
          (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
      rough t ![X, Y] ![])
    (h_quadratic_trace : forall t X Y,
      riemann_to_ricci_trace atr
        (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
          (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
      2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]) :
    RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
      hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare :=
  ricci_explicit_evolution_from_pointwise emb td atr conn_fam ha_fam hal_fam hsl_fam
    hl_fam h_Rc_smooth rough riemannRicci ricciSquare
    (ricci_pointwise_explicit_evolution_from_riemann_trace_slice_dt emb td atr
      h_eval h_tt g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth h_Rm_smooth D
      rough riemannRicci ricciSquare h_riemann h_rough_trace h_quadratic_trace)

/-- Tensor-level explicit Ricci evolution gives the pointwise Lemma 6.3
equation by evaluation. -/
theorem ricci_pointwise_explicit_evolution_of_explicit
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
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_explicit :
      RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
        hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare) :
    RicciPointwiseExplicitEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare := by
  intro t X Y
  rw [h_explicit t]
  exact ricci_lichnerowicz_laplacian_rhs_eval
    (rough t) (riemannRicci t) (ricciSquare t) X Y

/-- The explicit Ricci evolution equation implies the ordinary Lichnerowicz
interface with reaction tensor `2 Rm*Ric - 2 Ric^2`. This is Corollary 6.5 in
the same named-component form. -/
theorem ricci_lichnerowicz_evolution_from_explicit
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
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_evol :
      RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
        hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare) :
    RicciLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rough
      (fun t => ricci_lichnerowicz_reaction_02
        (riemannRicci t) (ricciSquare t)) := by
  intro t
  exact h_evol t

theorem ricci_evolution_from_explicit_lichnerowicz_equation_eval
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
    (rough riemannRicci ricciSquare : Time -> TensorData R V 0 2)
    (h_evol :
      RicciExplicitLichnerowiczEvolutionEquation emb td atr conn_fam ha_fam
        hal_fam hsl_fam hl_fam h_Rc_smooth rough riemannRicci ricciSquare)
    (t : Time) (X Y : V) :
    tensor_eval
      (dt_tensor td t
        (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s) atr)
        h_Rc_smooth) ![X, Y] ![] =
      rough t ![X, Y] ![] +
        2 * riemannRicci t ![X, Y] ![] -
          2 * ricciSquare t ![X, Y] ![] := by
  rw [h_evol t]
  exact ricci_lichnerowicz_laplacian_rhs_eval
    (rough t) (riemannRicci t) (ricciSquare t) X Y

end RicciEvolutionInterface
