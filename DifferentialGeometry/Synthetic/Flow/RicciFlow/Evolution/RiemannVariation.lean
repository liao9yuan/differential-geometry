import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Riemann Curvature Variation

Connection variation and the Riemann variation formula
under torsion-free connections.
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Connection Variation at Tensor Level
-- ============================================================

section ConnVarTensor

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Connection variation as a (1,0) tensor:
    A(X,Y) = ∂_t(conn_s X Y) represented as dt_tensor of vectorToData.
    Evaluates as: conn_var_vector(t,X,Y) ![] ![ω] = dt_apply(s ↦ ω(conn_s X Y))(t).

    The smoothness hypothesis `h_conn_smooth` supplies the scalar smoothness
    of `τ ↦ ω(conn_fam τ X Y)` for every covector `ω`; this is exactly what
    `dt_tensor` needs for the (1,0) slice since `vectorToData v ![] ![ω] = ω v`. -/
noncomputable def conn_var_vector
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (t : Time) (X Y : V)
    (h_conn_smooth : ∀ (ω : V →ₗ[R] R),
      td.isSmoothFam (fun τ => ω (conn_fam τ X Y))) : TensorData R V 1 0 :=
  dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X Y))
    (fun _ αs => h_conn_smooth (αs 0))

theorem conn_var_vector_eval
    (td : TimeDerivativeData R A Time) (conn_fam : Time → V → V → V)
    (t : Time) (X Y : V) (ω : V →ₗ[R] R)
    (h_conn_smooth : ∀ (ω : V →ₗ[R] R),
      td.isSmoothFam (fun τ => ω (conn_fam τ X Y))) :
    conn_var_vector td conn_fam t X Y h_conn_smooth ![] ![ω] =
    td.dt_apply (fun s => ω (conn_fam s X Y)) t := rfl

end ConnVarTensor

-- ============================================================
-- Section 2: Riemann Variation and Torsion-Free Simplification
-- ============================================================

section RiemannVariation

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The Riemann variation at the scalar level (5-term expansion).

    ∂_t[ω(Rm(s)(X,Y)Z)] = ω(conn_t X A(Y,Z)) + A(X, conn_t Y Z)(ω)
      − ω(conn_t Y A(X,Z)) − A(Y, conn_t X Z)(ω) − A([X,Y], Z)(ω)

    Proof uses NablaTimeProductRule to decompose ∂_t of each conn composition,
    then collects terms.

    Smoothness hypotheses:
    * `h_conn_smooth` — covectors composed with `conn_fam τ U W` are smooth;
    * `h_nested_smooth` — covectors composed with `conn_fam τ P (conn_fam τ U W)`
      are smooth (needed to split the Rm expression);
    * `h_nabla_Tτ` / `h_nabla_Tt` — the `hT_nabla` / `h_nabla_t` hypotheses of
      `NablaTimeProductRule`, provided explicitly for the three `T` families
      used in the decomposition (`YZ`, `XZ`, constant `Z`). -/
theorem riemann_variation_raw
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (_hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (_hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : ∀ (A : V) (f : Time → R),
      td.isSmoothFam f → td.isSmoothFam (fun τ => (emb.embed A) (f τ)))
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time)
    (h_conn_smooth : ∀ (U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ U W)))
    (h_nested_smooth : ∀ (P U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ P (conn_fam τ U W))))
    (h_nabla_T1τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam τ Y Z)) vs αs))
    (h_nabla_T1t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam t Y Z)) vs αs))
    (h_nabla_T2τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam τ X Z)) vs αs))
    (h_nabla_T2t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam t X Z)) vs αs))
    (h_nabla_T3τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs))
    (h_nabla_T3t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs)) :
    td.dt_apply (fun s => ω (Rm emb (conn_fam s) X Y Z)) t =
    nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
      (conn_var_vector td conn_fam t Y Z (h_conn_smooth Y Z)) ![] ![ω]
    + conn_var_vector td conn_fam t X (conn_fam t Y Z) (h_conn_smooth X _) ![] ![ω]
    - nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
        (conn_var_vector td conn_fam t X Z (h_conn_smooth X Z)) ![] ![ω]
    - conn_var_vector td conn_fam t Y (conn_fam t X Z) (h_conn_smooth Y _) ![] ![ω]
    - conn_var_vector td conn_fam t (bracket emb X Y) Z (h_conn_smooth _ Z) ![] ![ω] := by
  -- Expand Rm and split dt over subtraction
  have h_eq : (fun s => ω (Rm emb (conn_fam s) X Y Z)) =
      (fun s => ω (conn_fam s X (conn_fam s Y Z))) -
      (fun s => ω (conn_fam s Y (conn_fam s X Z))) -
      (fun s => ω (conn_fam s (bracket emb X Y) Z)) := by
    funext s; simp [Rm, map_sub]
  -- Smoothness for the three pieces of the difference.
  have hS1 : td.isSmoothFam (fun s => ω (conn_fam s X (conn_fam s Y Z))) :=
    h_nested_smooth X Y Z ω
  have hS2 : td.isSmoothFam (fun s => ω (conn_fam s Y (conn_fam s X Z))) :=
    h_nested_smooth Y X Z ω
  have hS3 : td.isSmoothFam (fun s => ω (conn_fam s (bracket emb X Y) Z)) :=
    h_conn_smooth (bracket emb X Y) Z ω
  have hS12 : td.isSmoothFam
      ((fun s => ω (conn_fam s X (conn_fam s Y Z))) -
       (fun s => ω (conn_fam s Y (conn_fam s X Z)))) :=
    td.isSmoothFam_sub _ _ hS1 hS2
  rw [h_eq,
      td.dt_apply_sub _ _ _ hS12 hS3,
      td.dt_apply_sub _ _ _ hS1 hS2]
  -- Now the goal has three separate dt_apply terms. Decompose each via NablaTimeProductRule.
  -- TERM 1: dt_apply(s ↦ ω(conn_s X (conn_s Y Z))) t
  -- Use NablaTimeProductRule with T(s) = vectorToData(conn_s Y Z)
  have h_nv1 : ∀ s, vectorToData (R := R) (conn_fam s X (conn_fam s Y Z)) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) X
        (vectorToData (R := R) (conn_fam s Y Z)) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) X (conn_fam s Y Z)).symm
  have hT1 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => (vectorToData (R := R) (conn_fam τ Y Z)) vs αs) :=
    fun _ αs => h_conn_smooth Y Z (αs 0)
  -- Call 1: smoothness witnesses for T(s) = vectorToData(conn_fam s Y Z), vector-field arg X.
  have hXT1 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam
        (fun τ => (emb.embed X) ((vectorToData (R := R) (conn_fam τ Y Z)) vs αs)) := by
    intro vs αs
    have h_eq : (fun τ => (emb.embed X) ((vectorToData (R := R) (conn_fam τ Y Z)) vs αs)) =
        (fun τ => (emb.embed X) ((αs 0) (conn_fam τ Y Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton]
    rw [h_eq]
    exact h_emb_closure X (fun τ => (αs 0) (conn_fam τ Y Z)) (h_conn_smooth Y Z (αs 0))
  have h_conn_v_var_1 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam τ Y Z))
          (Function.update vs i (conn_fam τ X (vs i))) αs) := fun i _ _ => i.elim0
  have h_conn_c_var_1 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam τ Y Z)) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) (conn_fam τ Y Z)) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs 0)))) =
        (fun τ => (emb.embed X) ((αs 0) (conn_fam τ Y Z)) -
          (αs 0) (conn_fam τ X (conn_fam τ Y Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (h_emb_closure X (fun τ => (αs 0) (conn_fam τ Y Z)) (h_conn_smooth Y Z (αs 0)))
      (h_nested_smooth X Y Z (αs 0))
  have h_conn_v_at_1 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam t Y Z))
          (Function.update vs i (conn_fam τ X (vs i))) αs) := fun i _ _ => i.elim0
  have h_conn_c_at_1 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam t Y Z)) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) (conn_fam t Y Z)) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs 0)))) =
        (fun τ => (emb.embed X) ((αs 0) (conn_fam t Y Z)) -
          (αs 0) (conn_fam τ X (conn_fam t Y Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (td.isSmoothFam_const ((emb.embed X) ((αs 0) (conn_fam t Y Z))))
      (h_conn_smooth X (conn_fam t Y Z) (αs 0))
  have h_pr1 := h_pr X (fun s => vectorToData (R := R) (conn_fam s Y Z)) t hT1
    hXT1 h_conn_v_var_1 h_conn_c_var_1 h_nabla_T1τ h_conn_v_at_1 h_conn_c_at_1 h_nabla_T1t
  -- h_pr1 is a tensor equality. Rewrite the LHS function to match.
  have h_pr1_T1τ_compat :
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam τ Y Z))) =
      (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z))) :=
    funext (fun s => (h_nv1 s).symm)
  -- Evaluate term 1 at ![] ![ω]
  have h_t1 : td.dt_apply (fun s => ω (conn_fam s X (conn_fam s Y Z))) t =
      conn_var_vector td conn_fam t X (conn_fam t Y Z)
        (h_conn_smooth X (conn_fam t Y Z)) ![] ![ω] +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
        (conn_var_vector td conn_fam t Y Z (h_conn_smooth Y Z)) ![] ![ω] := by
    -- Reduce both sides to dt_tensor evaluations.
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z)))
      (fun _ αs => h_nested_smooth X Y Z (αs 0))) ![] ![ω] = _
    -- Apply product rule and simplify.
    have h_pr1' := h_pr1
    -- Interpret the LHS of h_pr1 as the dt_tensor on the nested form; rewrite to match
    have := congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω]) h_pr1'
    simp only [MultilinearMap.add_apply] at this
    -- RHS₁ of this: conn_var_tensor evaluated on a constant vector tensor = conn_var_vector
    have h_conn_var_eq : conn_var_tensor emb td conn_fam ha_fam hl_fam t X
        (vectorToData (R := R) (conn_fam t Y Z)) h_nabla_T1t ![] ![ω] =
        conn_var_vector td conn_fam t X (conn_fam t Y Z)
          (h_conn_smooth X (conn_fam t Y Z)) ![] ![ω] := by
      simp only [conn_var_tensor, conn_var_vector, dt_tensor_eval]
      congr 1; funext τ
      exact congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω])
        (nabla_vector emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (conn_fam t Y Z))
    rw [show dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z)))
          (fun _ αs => h_nested_smooth X Y Z (αs 0)) ![] ![ω] =
        dt_tensor td t
          (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
            (vectorToData (R := R) (conn_fam τ Y Z))) h_nabla_T1τ ![] ![ω] from by
      simp only [dt_tensor_eval]
      exact congr_arg (fun f => td.dt_apply f t)
        (funext (fun s => by rw [h_nv1 s]))]
    rw [this, h_conn_var_eq]
    -- Remaining: nabla_tensor X (dt_tensor (fun s => vectorToData(conn_fam s Y Z))) ![] ![ω]
    --         = nabla_tensor X (conn_var_vector Y Z) ![] ![ω]
    -- These are literally equal by definition of conn_var_vector.
    rfl
  -- TERM 2: same structure with X↔Y
  have h_nv2 : ∀ s, vectorToData (R := R) (conn_fam s Y (conn_fam s X Z)) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) Y
        (vectorToData (R := R) (conn_fam s X Z)) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) Y (conn_fam s X Z)).symm
  have hT2 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => (vectorToData (R := R) (conn_fam τ X Z)) vs αs) :=
    fun _ αs => h_conn_smooth X Z (αs 0)
  -- Call 2: smoothness witnesses for T(s) = vectorToData(conn_fam s X Z), vector-field arg Y.
  have hXT2 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam
        (fun τ => (emb.embed Y) ((vectorToData (R := R) (conn_fam τ X Z)) vs αs)) := by
    intro vs αs
    have h_eq : (fun τ => (emb.embed Y) ((vectorToData (R := R) (conn_fam τ X Z)) vs αs)) =
        (fun τ => (emb.embed Y) ((αs 0) (conn_fam τ X Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton]
    rw [h_eq]
    exact h_emb_closure Y (fun τ => (αs 0) (conn_fam τ X Z)) (h_conn_smooth X Z (αs 0))
  have h_conn_v_var_2 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam τ X Z))
          (Function.update vs i (conn_fam τ Y (vs i))) αs) := fun i _ _ => i.elim0
  have h_conn_c_var_2 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam τ X Z)) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) (conn_fam τ X Z)) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y (αs 0)))) =
        (fun τ => (emb.embed Y) ((αs 0) (conn_fam τ X Z)) -
          (αs 0) (conn_fam τ Y (conn_fam τ X Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (h_emb_closure Y (fun τ => (αs 0) (conn_fam τ X Z)) (h_conn_smooth X Z (αs 0)))
      (h_nested_smooth Y X Z (αs 0))
  have h_conn_v_at_2 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam t X Z))
          (Function.update vs i (conn_fam τ Y (vs i))) αs) := fun i _ _ => i.elim0
  have h_conn_c_at_2 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) (conn_fam t X Z)) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) (conn_fam t X Z)) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y (αs 0)))) =
        (fun τ => (emb.embed Y) ((αs 0) (conn_fam t X Z)) -
          (αs 0) (conn_fam τ Y (conn_fam t X Z))) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (td.isSmoothFam_const ((emb.embed Y) ((αs 0) (conn_fam t X Z))))
      (h_conn_smooth Y (conn_fam t X Z) (αs 0))
  have h_pr2 := h_pr Y (fun s => vectorToData (R := R) (conn_fam s X Z)) t hT2
    hXT2 h_conn_v_var_2 h_conn_c_var_2 h_nabla_T2τ h_conn_v_at_2 h_conn_c_at_2 h_nabla_T2t
  have h_t2 : td.dt_apply (fun s => ω (conn_fam s Y (conn_fam s X Z))) t =
      conn_var_vector td conn_fam t Y (conn_fam t X Z)
        (h_conn_smooth Y (conn_fam t X Z)) ![] ![ω] +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
        (conn_var_vector td conn_fam t X Z (h_conn_smooth X Z)) ![] ![ω] := by
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s Y (conn_fam s X Z)))
      (fun _ αs => h_nested_smooth Y X Z (αs 0))) ![] ![ω] = _
    have := congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω]) h_pr2
    simp only [MultilinearMap.add_apply] at this
    have h_conn_var_eq : conn_var_tensor emb td conn_fam ha_fam hl_fam t Y
        (vectorToData (R := R) (conn_fam t X Z)) h_nabla_T2t ![] ![ω] =
        conn_var_vector td conn_fam t Y (conn_fam t X Z)
          (h_conn_smooth Y (conn_fam t X Z)) ![] ![ω] := by
      simp only [conn_var_tensor, conn_var_vector, dt_tensor_eval]
      congr 1; funext τ
      exact congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω])
        (nabla_vector emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y (conn_fam t X Z))
    rw [show dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s Y (conn_fam s X Z)))
          (fun _ αs => h_nested_smooth Y X Z (αs 0)) ![] ![ω] =
        dt_tensor td t
          (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
            (vectorToData (R := R) (conn_fam τ X Z))) h_nabla_T2τ ![] ![ω] from by
      simp only [dt_tensor_eval]
      exact congr_arg (fun f => td.dt_apply f t)
        (funext (fun s => by rw [h_nv2 s]))]
    rw [this, h_conn_var_eq]; rfl
  -- TERM 3: bracket term (bracket is time-independent)
  have h_nv3 : ∀ s, vectorToData (R := R) (conn_fam s (bracket emb X Y) Z) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y)
        (vectorToData (R := R) Z) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y) Z).symm
  have hT3 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun _ => (vectorToData (R := R) Z) vs αs) :=
    fun _ _ => td.isSmoothFam_const _
  -- Call 3: smoothness witnesses for T = constant vectorToData Z,
  -- vector-field arg bracket emb X Y.
  have hXT3 : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam
        (fun τ => (emb.embed (bracket emb X Y)) ((vectorToData (R := R) Z) vs αs)) :=
    fun _ _ => td.isSmoothFam_const _
  have h_conn_v_var_3 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) Z)
          (Function.update vs i (conn_fam τ (bracket emb X Y) (vs i))) αs) :=
    fun i _ _ => i.elim0
  have h_conn_c_var_3 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) Z) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y) (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) Z) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y) (αs 0)))) =
        (fun τ => (emb.embed (bracket emb X Y)) ((αs 0) Z) -
          (αs 0) (conn_fam τ (bracket emb X Y) Z)) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (td.isSmoothFam_const ((emb.embed (bracket emb X Y)) ((αs 0) Z)))
      (h_conn_smooth (bracket emb X Y) Z (αs 0))
  have h_conn_v_at_3 : ∀ (i : Fin 0) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) Z)
          (Function.update vs i (conn_fam τ (bracket emb X Y) (vs i))) αs) :=
    fun i _ _ => i.elim0
  have h_conn_c_at_3 : ∀ (j : Fin 1) (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ =>
        (vectorToData (R := R) Z) vs
          (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y) (αs j)))) := by
    intro j vs αs
    have hj : j = 0 := Subsingleton.elim _ _; subst hj
    have h_eq : (fun τ => (vectorToData (R := R) Z) vs
        (Function.update αs 0
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y) (αs 0)))) =
        (fun τ => (emb.embed (bracket emb X Y)) ((αs 0) Z) -
          (αs 0) (conn_fam τ (bracket emb X Y) Z)) := by
      funext τ
      simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
        MultilinearMap.ofSubsingleton, nabla_dual]
    rw [h_eq]
    exact td.isSmoothFam_sub _ _
      (td.isSmoothFam_const ((emb.embed (bracket emb X Y)) ((αs 0) Z)))
      (h_conn_smooth (bracket emb X Y) Z (αs 0))
  have h_pr3 := h_pr (bracket emb X Y) (fun _ => vectorToData (R := R) Z) t hT3
    hXT3 h_conn_v_var_3 h_conn_c_var_3 h_nabla_T3τ h_conn_v_at_3 h_conn_c_at_3 h_nabla_T3t
  have h_const_z : dt_tensor td t (fun _ => vectorToData (R := R) Z) hT3 = 0 := by
    ext vs' αs'; simp only [dt_tensor_eval, MultilinearMap.zero_apply]
    exact td.dt_apply_const _ _
  have h_t3 : td.dt_apply (fun s => ω (conn_fam s (bracket emb X Y) Z)) t =
      conn_var_vector td conn_fam t (bracket emb X Y) Z
        (h_conn_smooth (bracket emb X Y) Z) ![] ![ω] := by
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s (bracket emb X Y) Z))
      (fun _ αs => h_conn_smooth (bracket emb X Y) Z (αs 0))) ![] ![ω] = _
    have := congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω]) h_pr3
    simp only [MultilinearMap.add_apply] at this
    have h_conn_var_eq : conn_var_tensor emb td conn_fam ha_fam hl_fam t (bracket emb X Y)
        (vectorToData (R := R) Z) h_nabla_T3t ![] ![ω] =
        conn_var_vector td conn_fam t (bracket emb X Y) Z
          (h_conn_smooth (bracket emb X Y) Z) ![] ![ω] := by
      simp only [conn_var_tensor, conn_var_vector, dt_tensor_eval]
      congr 1; funext τ
      exact congr_arg (fun (T : TensorData R V 1 0) => T ![] ![ω])
        (nabla_vector emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y) Z)
    have h_zero : nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) (bracket emb X Y)
        (dt_tensor td t (fun _ => vectorToData (R := R) Z) hT3) ![] ![ω] = 0 := by
      rw [h_const_z]
      simp only [nabla_tensor_eval, MultilinearMap.zero_apply]
      simp
    rw [show dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s (bracket emb X Y) Z))
          (fun _ αs => h_conn_smooth (bracket emb X Y) Z (αs 0)) ![] ![ω] =
        dt_tensor td t
          (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
            (vectorToData (R := R) Z)) h_nabla_T3τ ![] ![ω] from by
      simp only [dt_tensor_eval]
      exact congr_arg (fun f => td.dt_apply f t)
        (funext (fun s => by rw [h_nv3 s]))]
    rw [this, h_conn_var_eq, h_zero, add_zero]
  -- Combine all three terms
  rw [h_t1, h_t2, h_t3]; ring

/-- Connection variation is additive in its first argument:
    A(X₁ + X₂, Y) = A(X₁, Y) + A(X₂, Y). -/
theorem conn_var_add_left
    (td : TimeDerivativeData R A Time) (conn_fam : Time → V → V → V)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (t : Time) (X₁ X₂ Y : V)
    (h₁ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ X₁ Y)))
    (h₂ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ X₂ Y)))
    (h₁₂ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ (X₁ + X₂) Y))) :
    conn_var_vector td conn_fam t (X₁ + X₂) Y h₁₂ =
    conn_var_vector td conn_fam t X₁ Y h₁ + conn_var_vector td conn_fam t X₂ Y h₂ := by
  ext vs αs
  change td.dt_apply (fun s => (αs 0) (conn_fam s (X₁ + X₂) Y)) t =
       (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X₁ Y))
         (fun _ αs' => h₁ (αs' 0))
       + dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X₂ Y))
         (fun _ αs' => h₂ (αs' 0))) vs αs
  simp only [MultilinearMap.add_apply]
  change td.dt_apply (fun s => (αs 0) (conn_fam s (X₁ + X₂) Y)) t =
       td.dt_apply (fun s => (αs 0) (conn_fam s X₁ Y)) t +
       td.dt_apply (fun s => (αs 0) (conn_fam s X₂ Y)) t
  have h_fun : (fun s => (αs 0) (conn_fam s (X₁ + X₂) Y)) =
      (fun s => (αs 0) (conn_fam s X₁ Y)) + (fun s => (αs 0) (conn_fam s X₂ Y)) := by
    funext s; rw [hal_fam s X₁ X₂ Y, map_add]; rfl
  rw [h_fun, td.dt_apply_add _ _ _ (h₁ (αs 0)) (h₂ (αs 0))]

/-- Connection variation respects subtraction in the first argument:
    A(X₁ - X₂, Y) = A(X₁, Y) - A(X₂, Y). -/
theorem conn_var_sub_left
    (td : TimeDerivativeData R A Time) (conn_fam : Time → V → V → V)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (t : Time) (X₁ X₂ Y : V)
    (h₁ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ X₁ Y)))
    (h₂ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ X₂ Y)))
    (h₁₂ : ∀ (ω : V →ₗ[R] R), td.isSmoothFam (fun τ => ω (conn_fam τ (X₁ - X₂) Y))) :
    conn_var_vector td conn_fam t (X₁ - X₂) Y h₁₂ =
    conn_var_vector td conn_fam t X₁ Y h₁ - conn_var_vector td conn_fam t X₂ Y h₂ := by
  ext vs αs
  change td.dt_apply (fun s => (αs 0) (conn_fam s (X₁ - X₂) Y)) t =
       (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X₁ Y))
         (fun _ αs' => h₁ (αs' 0))
       - dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X₂ Y))
         (fun _ αs' => h₂ (αs' 0))) vs αs
  simp only [MultilinearMap.sub_apply]
  change td.dt_apply (fun s => (αs 0) (conn_fam s (X₁ - X₂) Y)) t =
       td.dt_apply (fun s => (αs 0) (conn_fam s X₁ Y)) t -
       td.dt_apply (fun s => (αs 0) (conn_fam s X₂ Y)) t
  have h_fun : (fun s => (αs 0) (conn_fam s (X₁ - X₂) Y)) =
      (fun s => (αs 0) (conn_fam s X₁ Y)) - (fun s => (αs 0) (conn_fam s X₂ Y)) := by
    funext s
    change (αs 0) (conn_fam s (X₁ - X₂) Y) = (αs 0) (conn_fam s X₁ Y) - (αs 0) (conn_fam s X₂ Y)
    rw [show X₁ - X₂ = X₁ + (-1 : R) • X₂ from by rw [neg_one_smul, sub_eq_add_neg],
      hal_fam s X₁ _ Y, hsl_fam s (-1) X₂ Y, map_add, map_smul, smul_eq_mul]
    ring
  rw [h_fun, td.dt_apply_sub _ _ _ (h₁ (αs 0)) (h₂ (αs 0))]

/-- The covariant derivative of the connection variation (∇A).
    (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z)
    at the scalar level (applied to ω).

    Takes smoothness hypotheses used to form the component `conn_var_vector`s. -/
noncomputable def nabla_conn_var_scalar
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) (X Y Z : V) (ω : V →ₗ[R] R)
    (h_YZ : ∀ (β : V →ₗ[R] R), td.isSmoothFam (fun τ => β (conn_fam τ Y Z)))
    (h_cXY_Z : ∀ (β : V →ₗ[R] R), td.isSmoothFam (fun τ => β (conn_fam τ (conn_fam t X Y) Z)))
    (h_Y_cXZ : ∀ (β : V →ₗ[R] R), td.isSmoothFam (fun τ => β (conn_fam τ Y (conn_fam t X Z)))) : R :=
  nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
    (conn_var_vector td conn_fam t Y Z h_YZ) ![] ![ω]
  - conn_var_vector td conn_fam t (conn_fam t X Y) Z h_cXY_Z ![] ![ω]
  - conn_var_vector td conn_fam t Y (conn_fam t X Z) h_Y_cXZ ![] ![ω]

/-- Torsion-free simplification of the Riemann variation.
    Under torsion-free connections, the 5-term variation simplifies to:
    ∂_t Rm(X,Y,Z)(ω) = (∇_X A)(Y,Z)(ω) − (∇_Y A)(X,Z)(ω)
    where (∇_X A)(Y,Z) is the tensor-level covariant derivative of A. -/
theorem riemann_variation_torsion_free
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : ∀ (A : V) (f : Time → R),
      td.isSmoothFam f → td.isSmoothFam (fun τ => (emb.embed A) (f τ)))
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time)
    (h_conn_smooth : ∀ (U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ U W)))
    (h_nested_smooth : ∀ (P U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ P (conn_fam τ U W))))
    (h_nabla_T1τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam τ Y Z)) vs αs))
    (h_nabla_T1t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam t Y Z)) vs αs))
    (h_nabla_T2τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam τ X Z)) vs αs))
    (h_nabla_T2t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam t X Z)) vs αs))
    (h_nabla_T3τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs))
    (h_nabla_T3t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs)) :
    td.dt_apply (fun s => ω (Rm emb (conn_fam s) X Y Z)) t =
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω
      (h_conn_smooth Y Z) (h_conn_smooth _ Z) (h_conn_smooth Y _) -
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t Y X Z ω
      (h_conn_smooth X Z) (h_conn_smooth _ Z) (h_conn_smooth X _) := by
  rw [riemann_variation_raw emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_emb_closure
        X Y Z ω t
        h_conn_smooth h_nested_smooth
        h_nabla_T1τ h_nabla_T1t h_nabla_T2τ h_nabla_T2t h_nabla_T3τ h_nabla_T3t]
  simp only [nabla_conn_var_scalar]
  -- Evaluate bracket term as difference using torsion_free.
  have h_tf_eq : bracket emb X Y = conn_fam t X Y - conn_fam t Y X := (h_tf t X Y).symm
  have h_sub := conn_var_sub_left td conn_fam hal_fam hsl_fam t
    (conn_fam t X Y) (conn_fam t Y X) Z
    (h_conn_smooth (conn_fam t X Y) Z) (h_conn_smooth (conn_fam t Y X) Z)
    (by rw [← h_tf_eq]; exact h_conn_smooth (bracket emb X Y) Z)
  -- Rewrite conn_var_vector of the bracket via the sub.
  have h_ev : conn_var_vector td conn_fam t (bracket emb X Y) Z
      (h_conn_smooth (bracket emb X Y) Z) ![] ![ω] =
      conn_var_vector td conn_fam t (conn_fam t X Y) Z
        (h_conn_smooth (conn_fam t X Y) Z) ![] ![ω] -
      conn_var_vector td conn_fam t (conn_fam t Y X) Z
        (h_conn_smooth (conn_fam t Y X) Z) ![] ![ω] := by
    -- We need to rewrite `conn_var_vector t (bracket) ...` to the sub form.
    -- Use `conn_var_sub_left` at X - Y = bracket emb X Y under torsion-free,
    -- but the subscript must align. Use function congruence on the first arg.
    have : conn_var_vector td conn_fam t (bracket emb X Y) Z
        (h_conn_smooth (bracket emb X Y) Z) =
      conn_var_vector td conn_fam t (conn_fam t X Y - conn_fam t Y X) Z
        (by rw [← h_tf_eq]; exact h_conn_smooth (bracket emb X Y) Z) := by
      -- Both sides are `dt_tensor` of propositionally equal tensor families, and
      -- smoothness proofs are propositions. We argue pointwise.
      ext vs' αs'
      simp only [conn_var_vector, dt_tensor_eval]
      congr 1
      funext s
      change (αs' 0) (conn_fam s (bracket emb X Y) Z) =
           (αs' 0) (conn_fam s (conn_fam t X Y - conn_fam t Y X) Z)
      rw [h_tf_eq]
    rw [this, h_sub]
    simp [MultilinearMap.sub_apply]
  rw [h_ev]; ring

/-- Connects scalar-level variation to tensor-level dt_tensor.
    dt_tensor(Rm)(X,Y,Z)(ω) = dt(s ↦ ω(Rm_s(X,Y)Z)) by dt_tensor_eval + Rm_tensor_eval. -/
theorem variation_eq_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time)
    (h_Rm_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) vs αs)) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s))
      h_Rm_smooth ![X, Y, Z] ![ω] =
    td.dt_apply (fun s => ω (Rm emb (conn_fam s) X Y Z)) t := by
  -- Both sides unfold to td.dt_apply of the same function
  simp only [dt_tensor_eval]
  congr 1

/-- The scalar-level Riemann variation formula value.
    This is the 5-term expression from `riemann_variation_raw`, defined
    independently of dt_tensor(Rm). -/
noncomputable def riemann_variation_scalar
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) (X Y Z : V) (ω : V →ₗ[R] R)
    (h_conn_smooth : ∀ (U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ U W))) : R :=
  nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
    (conn_var_vector td conn_fam t Y Z (h_conn_smooth Y Z)) ![] ![ω]
  + conn_var_vector td conn_fam t X (conn_fam t Y Z) (h_conn_smooth X _) ![] ![ω]
  - nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
      (conn_var_vector td conn_fam t X Z (h_conn_smooth X Z)) ![] ![ω]
  - conn_var_vector td conn_fam t Y (conn_fam t X Z) (h_conn_smooth Y _) ![] ![ω]
  - conn_var_vector td conn_fam t (bracket emb X Y) Z (h_conn_smooth _ Z) ![] ![ω]

/-- The scalar variation formula equals dt_tensor(Rm) evaluation.
    This is the bridge between the geometric formula and the tensor-level object. -/
theorem variation_scalar_eq_dt_tensor
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_emb_closure : ∀ (A : V) (f : Time → R),
      td.isSmoothFam f → td.isSmoothFam (fun τ => (emb.embed A) (f τ)))
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time)
    (h_conn_smooth : ∀ (U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ U W)))
    (h_nested_smooth : ∀ (P U W : V) (β : V →ₗ[R] R),
      td.isSmoothFam (fun τ => β (conn_fam τ P (conn_fam τ U W))))
    (h_Rm_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => Rm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) vs αs))
    (h_nabla_T1τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam τ Y Z)) vs αs))
    (h_nabla_T1t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X
        (vectorToData (R := R) (conn_fam t Y Z)) vs αs))
    (h_nabla_T2τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam τ X Z)) vs αs))
    (h_nabla_T2t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) Y
        (vectorToData (R := R) (conn_fam t X Z)) vs αs))
    (h_nabla_T3τ : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs))
    (h_nabla_T3t : ∀ (vs : Fin 0 → V) (αs : Fin 1 → V →ₗ[R] R),
      td.isSmoothFam (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) (bracket emb X Y)
        (vectorToData (R := R) Z) vs αs)) :
    riemann_variation_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω h_conn_smooth =
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s))
      h_Rm_smooth ![X, Y, Z] ![ω] := by
  simp only [riemann_variation_scalar]
  rw [variation_eq_dt emb td conn_fam ha_fam hal_fam hsl_fam hl_fam X Y Z ω t h_Rm_smooth]
  exact (riemann_variation_raw emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_emb_closure
    X Y Z ω t
    h_conn_smooth h_nested_smooth
    h_nabla_T1τ h_nabla_T1t h_nabla_T2τ h_nabla_T2t h_nabla_T3τ h_nabla_T3t).symm

end RiemannVariation
