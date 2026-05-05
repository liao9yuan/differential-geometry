import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import DifferentialGeometry.Synthetic.Analysis.TimeOnTensors
import DifferentialGeometry.Synthetic.Operator.Variation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Flow — Basic Definitions

`IsRicciFlow`, `Rm_tensor` (1,3), and `ricciForm_tensor` (0,2).
-/

open SyntheticTensor

-- ============================================================
-- Rm_tensor: the Riemann curvature as a (1,3) tensor
-- ============================================================

section RmTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Riemann curvature as a (1,3) tensor:
    Rm_tensor ![X, Y, Z] ![ω] = ω(Rm emb conn X Y Z). -/
noncomputable def Rm_tensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    : TensorData R V 1 3 where
  toFun vs :=
    { toFun := fun αs => (αs 0) (Rm emb conn (vs 0) (vs 1) (vs 2))
      map_update_add' := by
        intro inst αs idx α₁ α₂
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp [Function.update, LinearMap.add_apply]
      map_update_smul' := by
        intro inst αs idx c α
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp [Function.update, LinearMap.smul_apply, smul_eq_mul] }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    fin_cases idx
    · -- idx = 0: Rm(v₁+v₂, Y, Z) = Rm(v₁, Y, Z) + Rm(v₂, Y, Z)
      change (αs 0) (Rm emb conn (Function.update vs 0 (v₁ + v₂) 0) (Function.update vs 0 (v₁ + v₂) 1) (Function.update vs 0 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 0 v₁ 0) (Function.update vs 0 v₁ 1) (Function.update vs 0 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 0 v₂ 0) (Function.update vs 0 v₂ 1) (Function.update vs 0 v₂ 2))
      simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Fin.reduceEq]
      rw [Rm_add_X emb conn ha hal, map_add]
    · -- idx = 1: Rm(X, v₁+v₂, Z) = Rm(X, v₁, Z) + Rm(X, v₂, Z)
      change (αs 0) (Rm emb conn (Function.update vs 1 (v₁ + v₂) 0) (Function.update vs 1 (v₁ + v₂) 1) (Function.update vs 1 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 1 v₁ 0) (Function.update vs 1 v₁ 1) (Function.update vs 1 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 1 v₂ 0) (Function.update vs 1 v₂ 1) (Function.update vs 1 v₂ 2))
      simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Fin.reduceEq]
      rw [Rm_add_Y emb conn ha hal, map_add]
    · -- idx = 2: Rm(X, Y, v₁+v₂) = Rm(X, Y, v₁) + Rm(X, Y, v₂)
      change (αs 0) (Rm emb conn (Function.update vs 2 (v₁ + v₂) 0) (Function.update vs 2 (v₁ + v₂) 1) (Function.update vs 2 (v₁ + v₂) 2)) =
           (αs 0) (Rm emb conn (Function.update vs 2 v₁ 0) (Function.update vs 2 v₁ 1) (Function.update vs 2 v₁ 2)) +
           (αs 0) (Rm emb conn (Function.update vs 2 v₂ 0) (Function.update vs 2 v₂ 1) (Function.update vs 2 v₂ 2))
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_self]
      rw [Rm_add_Z emb conn ha hal, map_add]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    fin_cases idx
    · change (αs 0) (Rm emb conn (Function.update vs 0 (c • v) 0) (Function.update vs 0 (c • v) 1) (Function.update vs 0 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 0 v 0) (Function.update vs 0 v 1) (Function.update vs 0 v 2))
      simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Fin.reduceEq]
      rw [Rm_smul_X emb conn hal hsl hl, map_smul, smul_eq_mul]
    · change (αs 0) (Rm emb conn (Function.update vs 1 (c • v) 0) (Function.update vs 1 (c • v) 1) (Function.update vs 1 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 1 v 0) (Function.update vs 1 v 1) (Function.update vs 1 v 2))
      simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Fin.reduceEq]
      rw [Rm_smul_Y emb conn hal hsl hl, map_smul, smul_eq_mul]
    · change (αs 0) (Rm emb conn (Function.update vs 2 (c • v) 0) (Function.update vs 2 (c • v) 1) (Function.update vs 2 (c • v) 2)) =
           c * (αs 0) (Rm emb conn (Function.update vs 2 v 0) (Function.update vs 2 v 1) (Function.update vs 2 v 2))
      simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_self]
      rw [Rm_smul_Z emb conn ha hsl hl, map_smul, smul_eq_mul]

/-- Evaluation of Rm_tensor. -/
theorem Rm_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    Rm_tensor emb conn ha hal hsl hl ![X, Y, Z] ![ω] = ω (Rm emb conn X Y Z) := by
  simp [Rm_tensor]

end RmTensor

-- ============================================================
-- ricciForm_tensor: the Ricci tensor as a (0,2) tensor
-- ============================================================

section RicciFormTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The Ricci tensor as a (0,2) TensorData:
    ricciForm_tensor ![X, Z] ![] = Rc emb conn ... atr X Z. -/
noncomputable def ricciForm_tensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) : TensorData R V 0 2 where
  toFun vs := MultilinearMap.constOfIsEmpty _ _
    (Rc emb conn ha hal hsl hl atr (vs 0) (vs 1))
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.add_apply, MultilinearMap.coe_mk]
    fin_cases idx
    · -- Rc(v₁ + v₂, Z) = Rc(v₁, Z) + Rc(v₂, Z)
      simp only [Fin.zero_eta, Fin.isValue, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, Function.const_apply]
      change Rc emb conn ha hal hsl hl atr (v₁ + v₂) (vs 1) =
           Rc emb conn ha hal hsl hl atr v₁ (vs 1) + Rc emb conn ha hal hsl hl atr v₂ (vs 1)
      unfold Rc
      rw [show RcEndo emb conn ha hal hsl hl (v₁ + v₂) (vs 1) =
          RcEndo emb conn ha hal hsl hl v₁ (vs 1) + RcEndo emb conn ha hal hsl hl v₂ (vs 1) from
        LinearMap.ext (fun Y => Rm_add_X emb conn ha hal v₁ v₂ Y (vs 1))]
      exact map_add atr.tr _ _
    · -- Rc(X, v₁ + v₂) = Rc(X, v₁) + Rc(X, v₂)
      simp only [Fin.mk_one, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, Function.update_self, Function.const_apply]
      change Rc emb conn ha hal hsl hl atr (vs 0) (v₁ + v₂) =
           Rc emb conn ha hal hsl hl atr (vs 0) v₁ + Rc emb conn ha hal hsl hl atr (vs 0) v₂
      exact (RcCovector emb conn ha hal hsl hl atr (vs 0)).map_add v₁ v₂
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 2 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.smul_apply, MultilinearMap.coe_mk, smul_eq_mul]
    fin_cases idx
    · simp only [Function.update]
      change Rc emb conn ha hal hsl hl atr (c • v) (vs 1) =
           c * Rc emb conn ha hal hsl hl atr v (vs 1)
      unfold Rc
      rw [show RcEndo emb conn ha hal hsl hl (c • v) (vs 1) =
          c • RcEndo emb conn ha hal hsl hl v (vs 1) from
        LinearMap.ext (fun Y => Rm_smul_X emb conn hal hsl hl c v Y (vs 1))]
      rw [atr.tr.map_smul, smul_eq_mul]
    · simp only [Function.update]
      change Rc emb conn ha hal hsl hl atr (vs 0) (c • v) =
           c * Rc emb conn ha hal hsl hl atr (vs 0) v
      have := (RcCovector emb conn ha hal hsl hl atr (vs 0)).map_smul c v
      rwa [smul_eq_mul] at this

/-- Evaluation of ricciForm_tensor. -/
theorem ricciForm_tensor_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Z : V) :
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Z] ![] =
    Rc emb conn ha hal hsl hl atr X Z := by
  simp [ricciForm_tensor, MultilinearMap.constOfIsEmpty]

/-- Scalar multiplication of ricciForm_tensor. -/
theorem ricciForm_tensor_smul_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (c : R) (X Z : V) :
    (c • ricciForm_tensor emb conn ha hal hsl hl atr) ![X, Z] ![] =
    c * Rc emb conn ha hal hsl hl atr X Z := by
  simp [MultilinearMap.smul_apply, smul_eq_mul, ricciForm_tensor_eval]

end RicciFormTensor

-- ============================================================
-- IsRicciFlow: def : Prop
-- ============================================================

section RicciFlowDef

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Ricci flow condition: the metric evolves by -2·Ric. (Levi-Civita is a separate bundle field.) -/
def IsRicciFlow
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    : Prop :=
  ∀ t, metric_var_form td g_fam h_met t =
    (-2 : R) • ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr

/-- Extract the evolution equation from IsRicciFlow. Trivial alias kept for
    readability at call sites. -/
theorem IsRicciFlow.evolution
    {emb : DerivationEmbedding k R V}
    {td : TimeDerivativeData R A Time} [TimeRegularFam td]
    {atr : AbstractTrace R V}
    {g_fam : Time → MetricDuality R V}
    {h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs)}
    {conn_fam : Time → V → V → V}
    {ha_fam hal_fam hsl_fam hl_fam}
    (h : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (t : Time) : metric_var_form td g_fam h_met t =
    (-2 : R) • ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr :=
  h t

end RicciFlowDef

-- ============================================================
-- NablaTimeProductRule: product rule for ∂_t and ∇
-- ============================================================

section ProductRule

-- `NablaTimeProductRule` introduces smoothness hypotheses that are not used in
-- the stated equation itself (they are supplied by every consumer of the rule
-- whenever it must be applied). Disable the unusedVariables linter in this
-- section so these consumer-facing hypotheses do not trigger warnings.
set_option linter.unusedVariables false

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Reconstruct the `nabla_tensor` aggregate smoothness witness for the
    time-varying family `fun τ => T τ` from the four primary smoothness
    hypotheses used by `NablaTimeProductRule`. The reconstruction unfolds
    `nabla_tensor` via `nabla_tensor_eval` (which holds by `rfl`) and then
    assembles the scalar family from the spatial-derivative term `hXT`,
    the vector-slot slice family (via `diag_isSmoothFam` applied to
    `h_2smooth_v`), and the covector-slot slice family (via
    `diag_isSmoothFam` applied to `h_2smooth_c`). -/
private theorem nablaTimeProductRule_hT_nabla_of_aux
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s)
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs) := by
  intro vs αs
  -- Unfold `nabla_tensor` via its evaluation formula (which holds by `rfl`).
  have h_eq : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs) =
      (fun τ => (emb.embed X) (T τ vs αs)
        - ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs
        - ∑ j : Fin r, T τ vs (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ
    exact nabla_tensor_eval emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs
  rw [h_eq]
  -- Smoothness of each per-slot slice via the diagonal projection of `h_2smooth_*`.
  have h_cs_v_var : ∀ (i : Fin s), td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := fun i =>
    TimeRegularFam2.diag_isSmoothFam (td := td)
      (fun p : Time × Time =>
        T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs)
      (h_2smooth_v i vs αs)
  have h_cs_c_var : ∀ (j : Fin r), td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := fun j =>
    TimeRegularFam2.diag_isSmoothFam (td := td)
      (fun p : Time × Time =>
        T p.1 vs (Function.update αs j
          (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))
      (h_2smooth_c j vs αs)
  -- Factor the lambda into three closed-under-∑ pieces.
  have h_split : (fun τ => (emb.embed X) (T τ vs αs)
      - ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs
      - ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      (fun τ => (emb.embed X) (T τ vs αs))
      - (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  have h_vec_sum : (fun τ => ∑ i : Fin s,
      T τ (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s, (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp [Finset.sum_apply]
  have h_cov_sum : (fun τ => ∑ j : Fin r,
      T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r, (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp [Finset.sum_apply]
  have hS_X : td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)) := hXT vs αs
  have hS_vec_sum : td.isSmoothFam
      (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    rw [h_vec_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun i _ => h_cs_v_var i)
  have hS_cov_sum : td.isSmoothFam
      (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    rw [h_cov_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun j _ => h_cs_c_var j)
  rw [h_split]
  exact td.isSmoothFam_sub _ _
    (td.isSmoothFam_sub _ _ hS_X hS_vec_sum) hS_cov_sum

/-- Reconstruct the `nabla_tensor` aggregate smoothness witness for the
    time-fixed tensor `T t` from the two 2-smoothness hypotheses used by
    `NablaTimeProductRule`. Because `T t` is constant in `τ`, the leading
    `(emb.embed X)(T t vs αs)` term is smooth by `isSmoothFam_const`; the
    per-slot slices come from `slice_right_isSmoothFam` applied at `τ₀ = t`
    (freezing the `.1` coordinate to `t`, so only `conn_fam p.2` / the
    `nabla_dual` varies in `τ`). -/
private theorem nablaTimeProductRule_h_nabla_t_of_aux
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T t) vs αs) := by
  intro vs αs
  -- Unfold `nabla_tensor` via its evaluation formula.
  have h_eq : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T t) vs αs) =
      (fun τ => (emb.embed X) (T t vs αs)
        - ∑ i : Fin s, T t (Function.update vs i (conn_fam τ X (vs i))) αs
        - ∑ j : Fin r, T t vs (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ
    exact nabla_tensor_eval emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T t) vs αs
  rw [h_eq]
  -- Per-slot slices: first coordinate frozen at `t`, so use `slice_right_isSmoothFam`.
  have h_cs_v_at : ∀ (i : Fin s), td.isSmoothFam
      (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) := fun i =>
    TimeRegularFam2.slice_right_isSmoothFam (td := td)
      (fun p : Time × Time =>
        T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs) t
      (h_2smooth_v i vs αs)
  have h_cs_c_at : ∀ (j : Fin r), td.isSmoothFam
      (fun τ => T t vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := fun j =>
    TimeRegularFam2.slice_right_isSmoothFam (td := td)
      (fun p : Time × Time =>
        T p.1 vs (Function.update αs j
          (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j)))) t
      (h_2smooth_c j vs αs)
  -- Factor the lambda into three closed-under-∑ pieces.
  have h_split : (fun τ => (emb.embed X) (T t vs αs)
      - ∑ i : Fin s, T t (Function.update vs i (conn_fam τ X (vs i))) αs
      - ∑ j : Fin r, T t vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      (fun _ => (emb.embed X) (T t vs αs))
      - (fun τ => ∑ i : Fin s, T t (Function.update vs i (conn_fam τ X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T t vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  have h_vec_sum : (fun τ => ∑ i : Fin s,
      T t (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s, (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp [Finset.sum_apply]
  have h_cov_sum : (fun τ => ∑ j : Fin r,
      T t vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r, (fun τ => T t vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp [Finset.sum_apply]
  have hS_const : td.isSmoothFam (fun _ : Time => (emb.embed X) (T t vs αs)) :=
    td.isSmoothFam_const _
  have hS_vec_sum : td.isSmoothFam
      (fun τ => ∑ i : Fin s, T t (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    rw [h_vec_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun i _ => h_cs_v_at i)
  have hS_cov_sum : td.isSmoothFam
      (fun τ => ∑ j : Fin r, T t vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    rw [h_cov_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun j _ => h_cs_c_at j)
  rw [h_split]
  exact td.isSmoothFam_sub _ _
    (td.isSmoothFam_sub _ _ hS_const hS_vec_sum) hS_cov_sum

/-- Product rule for time derivative and covariant derivative.
    This is the tensor-level analog of the old ConnectionTimeCalculus.t_conn_apply.
    States: ∂_t[∇(s)_X T(s)] = conn_var(t, X, T(t)) + ∇(t)_X(∂_t T).

    In the abstract synthetic setting (no coordinates, no FiniteDimensional),
    this is an independent property that connects time and spatial derivatives
    for varying connections acting on varying tensors.

    In concrete models (smooth manifolds), this follows from the product rule
    in local coordinates.

    The statement takes exactly four per-`T` smoothness hypotheses:
    * `hT` — smoothness of the scalar slices `τ ↦ T τ vs αs`;
    * `hXT` — smoothness of `τ ↦ (emb.embed X) (T τ vs αs)`;
    * `h_2smooth_v` — joint (2-time) smoothness of the vector-slot
      substitution family `p ↦ T p.1 (update vs i (conn_fam p.2 X (vs i))) αs`;
    * `h_2smooth_c` — joint (2-time) smoothness of the covector-slot
      substitution family `p ↦ T p.1 vs (update αs j (nabla_dual … p.2 … (αs j)))`.
    The aggregate `nabla_tensor` smoothness witnesses consumed by
    `dt_tensor`/`conn_var_tensor` are reconstructed internally from these four
    via `TimeRegularFam2.diag_isSmoothFam` and `slice_right_isSmoothFam` (see
    the helper theorems `nablaTimeProductRule_hT_nabla_of_aux` and
    `nablaTimeProductRule_h_nabla_t_of_aux`). -/
def NablaTimeProductRule
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y, conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    : Prop :=
  ∀ (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_2smooth_v : ∀ (i : Fin s) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs))
    (h_2smooth_c : ∀ (j : Fin r) vs αs,
      TimeRegularFam2.isSmoothFam2 (td := td)
        (fun p : Time × Time =>
          T p.1 vs (Function.update αs j
            (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))),
    dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ))
      (nablaTimeProductRule_hT_nabla_of_aux emb td conn_fam ha_fam hl_fam X T
        hXT h_2smooth_v h_2smooth_c) =
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (T t)
      (nablaTimeProductRule_h_nabla_t_of_aux emb td conn_fam ha_fam hl_fam X T t
        h_2smooth_v h_2smooth_c) +
    nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X (dt_tensor td t T hT)

end ProductRule
