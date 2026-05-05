import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciCore

/-!
# Ricci-Slot Traces and Reaction Algebra

This file contains the algebraic trace and reaction tensors used when
contracting the Riemann evolution equation to Ricci evolution.
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

/-- Trace a Riemann-type `(1,3)` tensor in the Ricci slot convention used by
`RcEndo`: for `Rm(X, -, Y)`, trace the output against the middle vector slot,
leaving the exterior slots `(X,Y)`.

The concrete realization still has to prove that this abstract
`tensor_contract` agrees with the endomorphism trace defining `Rc`. -/
noncomputable def riemann_to_ricci_trace
    (atr : AbstractTrace R V) (T : TensorData R V 1 3) :
    TensorData R V 0 2 :=
  contract_general atr (0 : Fin 1) (1 : Fin 3) T

/-- Ricci-specific coordinate evaluation law for `riemann_to_ricci_trace`.

For fixed exterior vector slots `X` and `Y`, if the slice `Z |-> T(X,Z,Y)`
is represented by an endomorphism `L`, then the Ricci-slot contraction
evaluates to `tr L`. Concrete coordinate trace realizations prove this once
from their local-frame summation formula. -/
def RicciSlotTraceEval (atr : AbstractTrace R V) : Prop :=
  forall (T : TensorData R V 1 3) (X Y : V) (L : V →ₗ[R] V),
    (forall Z (α : V →ₗ[R] R), T ![X, Z, Y] ![α] = α (L Z)) ->
      riemann_to_ricci_trace atr T ![X, Y] ![] = atr.tr L

/-- Evaluate the Ricci-slot trace of a `(1,3)` tensor as the trace of a sliced
endomorphism.

In coordinates this is the formula
`contract T (X,Y) = sum_i theta^i (L e_i)` when
`theta(L Z) = T(X,Z,Y,theta)`. The coordinate/local-frame proof is supplied
once as `RicciSlotTraceEval atr`; this theorem packages the evaluation shape
used by the Ricci computations. -/
theorem riemann_to_ricci_trace_eq_trace_of_slice
    (atr : AbstractTrace R V) (h_eval : RicciSlotTraceEval atr)
    (T : TensorData R V 1 3) (X Y : V) (L : V →ₗ[R] V)
    (hL : forall Z (α : V →ₗ[R] R), T ![X, Z, Y] ![α] = α (L Z)) :
    riemann_to_ricci_trace atr T ![X, Y] ![] = atr.tr L :=
  h_eval T X Y L hL

/-- Coordinate evaluation of Ricci as the middle-slot trace of Riemann.

This is the reusable bridge from the curvature tensor convention
`Rm_tensor(X,Z,Y,alpha) = alpha (Rm(X,Z)Y)` to the Ricci tensor convention
`Rc(X,Y) = tr (Z |-> Rm(X,Z)Y)`. -/
theorem riemann_to_ricci_trace_Rm_tensor_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (h_eval : RicciSlotTraceEval atr)
    (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) :
    riemann_to_ricci_trace atr (Rm_tensor emb conn ha hal hsl hl) ![X, Y] ![] =
      ricciForm_tensor emb conn ha hal hsl hl atr ![X, Y] ![] := by
  calc
    riemann_to_ricci_trace atr (Rm_tensor emb conn ha hal hsl hl) ![X, Y] ![] =
        atr.tr (RcEndo emb conn ha hal hsl hl X Y) := by
      exact riemann_to_ricci_trace_eq_trace_of_slice atr h_eval
        (Rm_tensor emb conn ha hal hsl hl) X Y
        (RcEndo emb conn ha hal hsl hl X Y)
        (by
          intro Z α
          simp [Rm_tensor_eval, RcEndo])
    _ = ricciForm_tensor emb conn ha hal hsl hl atr ![X, Y] ![] := by
      rw [ricciForm_tensor_eval]
      rfl

/-- The rough-Laplacian part of the Ricci evolution obtained by tracing the
Riemann rough Laplacian in the Ricci slots.

This is deliberately definitional: the nontrivial geometric content is the
choice to use this tensor as the `rough` input in the explicit Ricci evolution
interface. -/
noncomputable def riemann_to_ricci_rough_trace
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y) :
    Time -> TensorData R V 0 2 :=
  fun t =>
    riemann_to_ricci_trace atr
      (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t)
        (hal_fam t) (hsl_fam t) atr (g_fam t))

/-- Evaluation form of `riemann_to_ricci_rough_trace`, matching the
`h_rough_trace` input of the Ricci evolution bridge. -/
theorem riemann_to_ricci_rough_trace_eval
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) (X Y : V) :
    riemann_to_ricci_trace atr
      (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t)
        (hal_fam t) (hsl_fam t) atr (g_fam t)) ![X, Y] ![] =
    riemann_to_ricci_rough_trace emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam t ![X, Y] ![] := rfl

/-- Named package for the algebraic reduction of the Hamilton quadratic term
after tracing the Riemann evolution in the Ricci slots.

The fields `riemannRicci` and `ricciSquare` are the two tensors appearing in
the Lichnerowicz-form Ricci evolution. The `trace_eq` field is the remaining
coordinate/curvature-algebra calculation: it identifies the Ricci-slot trace
of `Q_rm_independent` with `2 Rm*Ric - 2 Ric^2`. -/
structure RiemannToRicciQuadraticTraceDecomposition
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y) where
  riemannRicci : Time -> TensorData R V 0 2
  ricciSquare : Time -> TensorData R V 0 2
  trace_eq : forall t X Y,
    riemann_to_ricci_trace atr
      (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
    2 * riemannRicci t ![X, Y] ![] - 2 * ricciSquare t ![X, Y] ![]

/-- Projection from the named Hamilton-quadratic trace package, matching the
`h_quadratic_trace` input of the Ricci evolution bridge. -/
theorem riemann_to_ricci_quadratic_trace_of_decomposition
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (Qd : RiemannToRicciQuadraticTraceDecomposition emb atr g_fam conn_fam
      ha_fam hal_fam hsl_fam hl_fam)
    (t : Time) (X Y : V) :
    riemann_to_ricci_trace atr
      (Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t)) ![X, Y] ![] =
    2 * Qd.riemannRicci t ![X, Y] ![] -
      2 * Qd.ricciSquare t ![X, Y] ![] :=
  Qd.trace_eq t X Y

/-- The `R_{ikj\ell} Ric^{k\ell}` tensor appearing in the explicit Ricci
evolution formula.

For fixed `X,Y`, this is the trace of the endomorphism
`Z |-> Rm(X, Ric# Z) Y`, where `Ric#` is the Ricci endomorphism obtained by
raising one index with the metric. -/
noncomputable def riemannRicciReactionTensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : TensorData R V 0 2 where
  toFun vs := MultilinearMap.constOfIsEmpty _ _
    (atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) (vs 1)).comp
      (RicciEndomorphism emb conn ha hal hsl hl atr met)))
  map_update_add' := by
    intro inst vs idx X₁ X₂
    ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.add_apply,
      MultilinearMap.coe_mk]
    fin_cases idx
    · simp
      change atr.tr ((RcEndo emb conn ha hal hsl hl (X₁ + X₂) (vs 1)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
        atr.tr ((RcEndo emb conn ha hal hsl hl X₁ (vs 1)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) +
        atr.tr ((RcEndo emb conn ha hal hsl hl X₂ (vs 1)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met))
      rw [show RcEndo emb conn ha hal hsl hl (X₁ + X₂) (vs 1) =
          RcEndo emb conn ha hal hsl hl X₁ (vs 1) +
            RcEndo emb conn ha hal hsl hl X₂ (vs 1) from
        LinearMap.ext (fun Z => Rm_add_X emb conn ha hal X₁ X₂ Z (vs 1))]
      have hcomp :
          ((RcEndo emb conn ha hal hsl hl X₁ (vs 1) +
              RcEndo emb conn ha hal hsl hl X₂ (vs 1)).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
          (RcEndo emb conn ha hal hsl hl X₁ (vs 1)).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) +
          (RcEndo emb conn ha hal hsl hl X₂ (vs 1)).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) := by
        ext Z
        simp [LinearMap.comp_apply, LinearMap.add_apply]
      rw [hcomp]
      exact map_add atr.tr _ _
    · simp
      change atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) (X₁ + X₂)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
        atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) X₁).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) +
        atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) X₂).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met))
      rw [show RcEndo emb conn ha hal hsl hl (vs 0) (X₁ + X₂) =
          RcEndo emb conn ha hal hsl hl (vs 0) X₁ +
            RcEndo emb conn ha hal hsl hl (vs 0) X₂ from
        LinearMap.ext (fun Z => Rm_add_Z emb conn ha hal (vs 0) Z X₁ X₂)]
      have hcomp :
          ((RcEndo emb conn ha hal hsl hl (vs 0) X₁ +
              RcEndo emb conn ha hal hsl hl (vs 0) X₂).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
          (RcEndo emb conn ha hal hsl hl (vs 0) X₁).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) +
          (RcEndo emb conn ha hal hsl hl (vs 0) X₂).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) := by
        ext Z
        simp [LinearMap.comp_apply, LinearMap.add_apply]
      rw [hcomp]
      exact map_add atr.tr _ _
  map_update_smul' := by
    intro inst vs idx c X
    ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.smul_apply,
      MultilinearMap.coe_mk, smul_eq_mul]
    fin_cases idx
    · simp
      change atr.tr ((RcEndo emb conn ha hal hsl hl (c • X) (vs 1)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
        c * atr.tr ((RcEndo emb conn ha hal hsl hl X (vs 1)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met))
      rw [show RcEndo emb conn ha hal hsl hl (c • X) (vs 1) =
          c • RcEndo emb conn ha hal hsl hl X (vs 1) from
        LinearMap.ext (fun Z => Rm_smul_X emb conn hal hsl hl c X Z (vs 1))]
      have hcomp :
          ((c • RcEndo emb conn ha hal hsl hl X (vs 1)).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
          c • (RcEndo emb conn ha hal hsl hl X (vs 1)).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) := by
        ext Z
        simp [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hcomp, map_smul]
      rfl
    · simp
      change atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) (c • X)).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
        c * atr.tr ((RcEndo emb conn ha hal hsl hl (vs 0) X).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met))
      rw [show RcEndo emb conn ha hal hsl hl (vs 0) (c • X) =
          c • RcEndo emb conn ha hal hsl hl (vs 0) X from
        LinearMap.ext (fun Z => Rm_smul_Z emb conn ha hsl hl c (vs 0) Z X)]
      have hcomp :
          ((c • RcEndo emb conn ha hal hsl hl (vs 0) X).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met)) =
          c • (RcEndo emb conn ha hal hsl hl (vs 0) X).comp
            (RicciEndomorphism emb conn ha hal hsl hl atr met) := by
        ext Z
        simp [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hcomp, map_smul]
      rfl

theorem riemannRicciReactionTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X Y : V) :
    riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] =
      atr.tr ((RcEndo emb conn ha hal hsl hl X Y).comp
        (RicciEndomorphism emb conn ha hal hsl hl atr met)) := by
  rfl

/-- Metric evaluation of the opposite-composition reaction endomorphism.

After commuting the second covariant derivatives in the Riemann evolution, the
first exposed reaction term has the form `Rc(Rm X Z Y, E)`. This lemma packages
that term as the metric pairing of `Ric# ∘ RcEndo X Y`, the composition whose
trace is then converted to the canonical Hamilton reaction tensor by trace
cyclicity. -/
theorem ricci_comp_RcEndo_metric_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X Y Z E : V) :
    met.g
        (((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
          (RcEndo emb conn ha hal hsl hl X Y)) Z) E =
      Rc emb conn ha hal hsl hl atr (Rm emb conn X Z Y) E := by
  rw [LinearMap.comp_apply]
  exact RicciEndomorphism_spec emb conn ha hal hsl hl atr met
    (Rm emb conn X Z Y) E

/-- Trace-cyclicity form of `riemannRicciReactionTensor`.

The canonical tensor is defined as `tr (RcEndo X Y ∘ Ric#)`, while the forward
trace of the commuted Riemann formula naturally produces
`tr (Ric# ∘ RcEndo X Y)`. This is the small trace-cyclicity bridge between the
two forms. -/
theorem riemannRicciReactionTensor_eq_trace_ricci_comp_RcEndo
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X Y : V) :
    atr.tr ((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
        (RcEndo emb conn ha hal hsl hl X Y)) =
      riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] := by
  rw [riemannRicciReactionTensor_eval]
  exact atr.trace_comm
    (RicciEndomorphism emb conn ha hal hsl hl atr met)
    (RcEndo emb conn ha hal hsl hl X Y)

/-- Metric evaluation of the second commuted reaction term.

The term `Rc(Y, Rm(X,Z)E)` is the metric pairing of the endomorphism
`- RcEndo X (Ric# Y)`. This is the pointwise skew-adjoint curvature step used
when the Ricci-slot trace of Hamilton's quadratic term is reduced to the
canonical `-Ric^2` contribution. -/
theorem neg_RcEndo_ricciEndomorphism_metric_apply_eq_second_reaction
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X Y Z E : V) :
    met.g
        ((-(RcEndo emb conn ha hal hsl hl X
          (RicciEndomorphism emb conn ha hal hsl hl atr met Y))) Z) E =
      Rc emb conn ha hal hsl hl atr Y (Rm emb conn X Z E) := by
  rw [LinearMap.neg_apply, RcEndo]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [met.g_neg_left]
  rw [Rm_metric_antisymm emb conn met h_mc X Z
    (RicciEndomorphism emb conn ha hal hsl hl atr met Y) E]
  rw [neg_neg]
  rw [met.g_symm (Rm emb conn X Z E)
    (RicciEndomorphism emb conn ha hal hsl hl atr met Y)]
  exact RicciEndomorphism_spec emb conn ha hal hsl hl atr met Y (Rm emb conn X Z E)

/-- The `Ric_i{}^k Ric_{kj}` tensor appearing in the explicit Ricci evolution
formula. In endomorphism notation this is `g(Ric#(Ric# X), Y)`. -/
noncomputable def ricciSquareTensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : TensorData R V 0 2 where
  toFun vs := MultilinearMap.constOfIsEmpty _ _
    (met.g
      (RicciEndomorphism emb conn ha hal hsl hl atr met
        (RicciEndomorphism emb conn ha hal hsl hl atr met (vs 0)))
      (vs 1))
  map_update_add' := by
    intro inst vs idx X₁ X₂
    ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.add_apply,
      MultilinearMap.coe_mk]
    set Ric := RicciEndomorphism emb conn ha hal hsl hl atr met
    fin_cases idx
    · simp
      rw [met.g_add_left]
    · simp
      change met.g (Ric (Ric (vs 0))) (X₁ + X₂) =
        met.g (Ric (Ric (vs 0))) X₁ + met.g (Ric (Ric (vs 0))) X₂
      rw [met.g_add_right]
  map_update_smul' := by
    intro inst vs idx c X
    ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.smul_apply,
      MultilinearMap.coe_mk, smul_eq_mul]
    set Ric := RicciEndomorphism emb conn ha hal hsl hl atr met
    fin_cases idx
    · simp
      rw [met.g_smul_left]
    · simp
      change met.g (Ric (Ric (vs 0))) (c • X) =
        c * met.g (Ric (Ric (vs 0))) X
      rw [met.g_smul_right]

theorem ricciSquareTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X Y : V) :
    ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] =
      met.g
        (RicciEndomorphism emb conn ha hal hsl hl atr met
          (RicciEndomorphism emb conn ha hal hsl hl atr met X))
        Y := by
  rfl

/-- Ricci-square written as `Rc(X, Ric# Y)`, assuming Ricci symmetry.

This is the scalar form needed to turn the trace of
`-RcEndo X (Ric# Y)` into the canonical `-Ric^2` reaction term. -/
theorem ricciSquareTensor_eq_Rc_ricciEndomorphism_of_Rc_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (X Y : V) :
    ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] =
      Rc emb conn ha hal hsl hl atr X
        (RicciEndomorphism emb conn ha hal hsl hl atr met Y) := by
  rw [ricciSquareTensor_eval]
  calc
    met.g
        (RicciEndomorphism emb conn ha hal hsl hl atr met
          (RicciEndomorphism emb conn ha hal hsl hl atr met X)) Y =
        Rc emb conn ha hal hsl hl atr
          (RicciEndomorphism emb conn ha hal hsl hl atr met X) Y := by
          exact RicciEndomorphism_spec emb conn ha hal hsl hl atr met
            (RicciEndomorphism emb conn ha hal hsl hl atr met X) Y
    _ = Rc emb conn ha hal hsl hl atr Y
          (RicciEndomorphism emb conn ha hal hsl hl atr met X) := by
          exact h_Rc_symm
            (RicciEndomorphism emb conn ha hal hsl hl atr met X) Y
    _ = met.g
          (RicciEndomorphism emb conn ha hal hsl hl atr met Y)
          (RicciEndomorphism emb conn ha hal hsl hl atr met X) := by
          exact (RicciEndomorphism_spec emb conn ha hal hsl hl atr met Y
            (RicciEndomorphism emb conn ha hal hsl hl atr met X)).symm
    _ = met.g
          (RicciEndomorphism emb conn ha hal hsl hl atr met X)
          (RicciEndomorphism emb conn ha hal hsl hl atr met Y) := by
          exact met.g_symm
            (RicciEndomorphism emb conn ha hal hsl hl atr met Y)
            (RicciEndomorphism emb conn ha hal hsl hl atr met X)
    _ = Rc emb conn ha hal hsl hl atr X
          (RicciEndomorphism emb conn ha hal hsl hl atr met Y) := by
          exact RicciEndomorphism_spec emb conn ha hal hsl hl atr met X
            (RicciEndomorphism emb conn ha hal hsl hl atr met Y)

/-- Trace form of the second commuted reaction term: after Ricci symmetry, the
trace of `-RcEndo X (Ric# Y)` is exactly `-Ric^2(X,Y)`. -/
theorem trace_neg_RcEndo_ricciEndomorphism_eq_neg_ricciSquare_of_Rc_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (X Y : V) :
    atr.tr (-(RcEndo emb conn ha hal hsl hl X
        (RicciEndomorphism emb conn ha hal hsl hl atr met Y))) =
      -ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] := by
  rw [map_neg]
  change -Rc emb conn ha hal hsl hl atr X
      (RicciEndomorphism emb conn ha hal hsl hl atr met Y) =
    -ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]
  rw [ricciSquareTensor_eq_Rc_ricciEndomorphism_of_Rc_symm
    emb conn ha hal hsl hl atr met h_Rc_symm X Y]

/-- The pair of curvature-reaction endomorphisms exposed after commuting the
first Hessian pair in the Ricci-slot Hamilton quadratic calculation. -/
noncomputable def commutedReactionPairEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (X Y : V) : V →ₗ[R] V :=
  ((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
    (RcEndo emb conn ha hal hsl hl X Y)) +
  (-(RcEndo emb conn ha hal hsl hl X
    (RicciEndomorphism emb conn ha hal hsl hl atr met Y)))

/-- Pointwise metric evaluation of the exposed commuted reaction pair. -/
theorem commutedReactionPairEndomorphism_metric_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X Y Z E : V) :
    met.g (commutedReactionPairEndomorphism emb conn ha hal hsl hl atr met X Y Z) E =
      Rc emb conn ha hal hsl hl atr (Rm emb conn X Z Y) E +
        Rc emb conn ha hal hsl hl atr Y (Rm emb conn X Z E) := by
  unfold commutedReactionPairEndomorphism
  rw [LinearMap.add_apply, met.g_add_left]
  rw [ricci_comp_RcEndo_metric_apply emb conn ha hal hsl hl atr met X Y Z E]
  rw [neg_RcEndo_ricciEndomorphism_metric_apply_eq_second_reaction
    emb conn ha hal hsl hl atr met h_mc X Y Z E]

/-- The two curvature-reaction endomorphisms already exposed by commuting the
first Hessian pair trace to `Rm*Ric - Ric^2`.

The remaining part of the Hamilton quadratic trace is therefore precisely the
trace of the still-uncommuted Hessian/rough-laplacian residual. -/
theorem trace_commuted_reaction_pair_eq_riemannRicci_sub_ricciSquare
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (X Y : V) :
    atr.tr
        (((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
          (RcEndo emb conn ha hal hsl hl X Y)) +
        (-(RcEndo emb conn ha hal hsl hl X
          (RicciEndomorphism emb conn ha hal hsl hl atr met Y)))) =
      riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
        ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] := by
  rw [map_add]
  rw [riemannRicciReactionTensor_eq_trace_ricci_comp_RcEndo
    emb conn ha hal hsl hl atr met X Y]
  rw [trace_neg_RcEndo_ricciEndomorphism_eq_neg_ricciSquare_of_Rc_symm
    emb conn ha hal hsl hl atr met h_Rc_symm X Y]
  ring

theorem trace_commutedReactionPairEndomorphism_eq_riemannRicci_sub_ricciSquare
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X)
    (X Y : V) :
    atr.tr (commutedReactionPairEndomorphism emb conn ha hal hsl hl atr met X Y) =
      riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
        ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![] := by
  simpa [commutedReactionPairEndomorphism] using
    trace_commuted_reaction_pair_eq_riemannRicci_sub_ricciSquare
      emb conn ha hal hsl hl atr met h_Rc_symm X Y

/-- The canonical quadratic-trace target for Lemma 6.3.

This isolates the remaining hard calculation: tracing `Q_rm_independent` in the
Ricci slots must equal `2 * Rm*Ric - 2 * Ric^2` for the canonical tensors above. -/
def RiemannToRicciCanonicalQuadraticTrace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop :=
  forall X Y,
    riemann_to_ricci_trace atr
      (Q_rm_independent emb conn ha hal hsl hl atr met) ![X, Y] ![] =
    2 * riemannRicciReactionTensor emb conn ha hal hsl hl atr met ![X, Y] ![] -
      2 * ricciSquareTensor emb conn ha hal hsl hl atr met ![X, Y] ![]


end RicciEvolutionInterface
