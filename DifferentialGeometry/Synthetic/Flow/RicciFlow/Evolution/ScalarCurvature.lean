import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Evolution of Scalar Curvature

∂_t R = 2|Rc|² + metric_trace(∂_t Rc).
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Endomorphism from (0,2) tensor
-- ============================================================

section TensorEndo

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private lemma flat_covector_first_add (T : TensorData R V 0 2) (X₁ X₂ : V) :
    flat_covector T (X₁ + X₂) = flat_covector T X₁ + flat_covector T X₂ := by
  ext Z
  change T ![X₁ + X₂, Z] ![] = T ![X₁, Z] ![] + T ![X₂, Z] ![]
  have h := T.map_update_add ![X₁, Z] 0 X₁ X₂
  have hu : ∀ v, Function.update (![X₁, Z] : Fin 2 → V) 0 v = ![v, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [hu] at h; exact congr_arg (· ![]) h

private lemma flat_covector_first_smul (T : TensorData R V 0 2) (c : R) (X : V) :
    flat_covector T (c • X) = c • flat_covector T X := by
  ext Z
  change T ![c • X, Z] ![] = c * T ![X, Z] ![]
  have h := congr_arg (· ![]) (T.map_update_smul ![X, Z] 0 c X)
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h
  rwa [show Function.update (![X, Z] : Fin 2 → V) 0 (c • X) = ![c • X, Z] from by
        ext i; fin_cases i <;> simp [Function.update],
       show Function.update (![X, Z] : Fin 2 → V) 0 X = ![X, Z] from by
        ext i; fin_cases i <;> simp [Function.update]] at h

private lemma flat_covector_tensor_smul (c : R) (T : TensorData R V 0 2) (X : V) :
    flat_covector (c • T) X = c • flat_covector T X := by
  ext Z
  change (c • T) ![X, Z] ![] = c * T ![X, Z] ![]
  simp only [MultilinearMap.smul_apply, smul_eq_mul]

/-- Turn a (0,2) tensor into an endomorphism via the metric:
    T♯(X) = sharp(T(X, ·)). -/
noncomputable def tensor_02_endo (met : MetricDuality R V) 
    (T : TensorData R V 0 2) : V →ₗ[R] V where
  toFun X := met.sharp (flat_covector T X)
  map_add' X₁ X₂ := by
    rw [flat_covector_first_add]; exact met.sharp_add _ _
  map_smul' c X := by
    simp only [RingHom.id_apply]
    rw [flat_covector_first_smul]; exact met.sharp_smul c _

/-- Raising one index is additive in the tensor argument. -/
theorem tensor_02_endo_add (met : MetricDuality R V)
    (T S : TensorData R V 0 2) :
    tensor_02_endo met (T + S) = tensor_02_endo met T + tensor_02_endo met S := by
  ext X
  change met.sharp (flat_covector (T + S) X) =
    met.sharp (flat_covector T X) + met.sharp (flat_covector S X)
  have hflat : flat_covector (T + S) X = flat_covector T X + flat_covector S X := by
    ext Z
    simp [flat_covector_apply]
  rw [hflat, met.sharp_add]

/-- Raising one index is homogeneous in the tensor argument. -/
theorem tensor_02_endo_smul (met : MetricDuality R V) (c : R)
    (T : TensorData R V 0 2) :
    tensor_02_endo met (c • T) = c • tensor_02_endo met T := by
  ext X
  change met.sharp (flat_covector (c • T) X) = c • met.sharp (flat_covector T X)
  rw [flat_covector_tensor_smul]; exact met.sharp_smul c _

/-- Raising one index commutes with negation. -/
theorem tensor_02_endo_neg (met : MetricDuality R V)
    (T : TensorData R V 0 2) :
    tensor_02_endo met (-T) = -tensor_02_endo met T := by
  rw [← neg_one_smul R T, tensor_02_endo_smul, neg_one_smul]

/-- Raising one index commutes with subtraction. -/
theorem tensor_02_endo_sub (met : MetricDuality R V)
    (T S : TensorData R V 0 2) :
    tensor_02_endo met (T - S) = tensor_02_endo met T - tensor_02_endo met S := by
  rw [sub_eq_add_neg, tensor_02_endo_add, tensor_02_endo_neg]
  rw [sub_eq_add_neg]

/-- Raising one index of the metric tensor gives the identity endomorphism. -/
theorem tensor_02_endo_metric (met : MetricDuality R V) :
    tensor_02_endo met met.g_tensor = LinearMap.id := by
  ext X
  change met.sharp (flat_covector met.g_tensor X) = X
  exact met.sharp_flat X

/-- Abstract dimension associated with the trace functional: `tr(id)`. -/
noncomputable def abstractTraceDimension (atr : AbstractTrace R V) : R :=
  atr.tr (LinearMap.id : V →ₗ[R] V)

/-- Inner product of two (0,2) tensors: ⟨T, S⟩_g = tr(T♯ ∘ S♯). -/
noncomputable def tensor_inner_02 (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (T S : TensorData R V 0 2) : R :=
  atr.tr ((tensor_02_endo met T).comp (tensor_02_endo met S))

/-- Cubic trace of a `(0,2)` tensor after raising one index:
`tr(T♯ ∘ T♯ ∘ T♯)`.

This is the synthetic object needed to bridge Hamilton's eigenvalue expression
`λ₁^3 + λ₂^3 + λ₃^3` back to the Ricci tensor. -/
noncomputable def tensor_trace_cube_02 (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T : TensorData R V 0 2) : R :=
  atr.tr ((tensor_02_endo met T).comp ((tensor_02_endo met T).comp (tensor_02_endo met T)))

end TensorEndo

-- ============================================================
-- Section 2: Inner product properties
-- ============================================================

section InnerProps

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- tensor_inner_02(T + U, S) = tensor_inner_02(T, S) + tensor_inner_02(U, S). -/
theorem tensor_inner_02_add_left (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T U S : TensorData R V 0 2) :
    tensor_inner_02 met atr (T + U) S =
      tensor_inner_02 met atr T S + tensor_inner_02 met atr U S := by
  simp only [tensor_inner_02, tensor_02_endo_add]
  have h_comp :
      ((tensor_02_endo met T + tensor_02_endo met U).comp (tensor_02_endo met S)) =
        (tensor_02_endo met T).comp (tensor_02_endo met S) +
          (tensor_02_endo met U).comp (tensor_02_endo met S) := by
    ext X
    rfl
  rw [h_comp, map_add]

/-- tensor_inner_02(c•T, S) = c * tensor_inner_02(T, S). -/
theorem tensor_inner_02_smul_left (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (c : R) (T S : TensorData R V 0 2) :
    tensor_inner_02 met atr (c • T) S = c * tensor_inner_02 met atr T S := by
  simp only [tensor_inner_02]
  have h_comp : (tensor_02_endo met (c • T)).comp (tensor_02_endo met S) =
      c • (tensor_02_endo met T).comp (tensor_02_endo met S) := by
    rw [tensor_02_endo_smul]; ext v; simp [LinearMap.smul_apply]
  rw [h_comp, map_smul, smul_eq_mul]

/-- tensor_inner_02(-T, S) = -tensor_inner_02(T, S). -/
theorem tensor_inner_02_neg_left (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T S : TensorData R V 0 2) :
    tensor_inner_02 met atr (-T) S = -tensor_inner_02 met atr T S := by
  rw [← neg_one_smul R T, tensor_inner_02_smul_left]
  ring

/-- tensor_inner_02(T - U, S) = tensor_inner_02(T, S) - tensor_inner_02(U, S). -/
theorem tensor_inner_02_sub_left (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T U S : TensorData R V 0 2) :
    tensor_inner_02 met atr (T - U) S =
      tensor_inner_02 met atr T S - tensor_inner_02 met atr U S := by
  rw [sub_eq_add_neg, tensor_inner_02_add_left, tensor_inner_02_neg_left]
  rw [sub_eq_add_neg]

/-- tensor_inner_02(T, S + U) = tensor_inner_02(T, S) + tensor_inner_02(T, U). -/
theorem tensor_inner_02_add_right (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T S U : TensorData R V 0 2) :
    tensor_inner_02 met atr T (S + U) =
      tensor_inner_02 met atr T S + tensor_inner_02 met atr T U := by
  simp only [tensor_inner_02, tensor_02_endo_add]
  have h_comp :
      (tensor_02_endo met T).comp (tensor_02_endo met S + tensor_02_endo met U) =
        (tensor_02_endo met T).comp (tensor_02_endo met S) +
          (tensor_02_endo met T).comp (tensor_02_endo met U) := by
    ext X
    simp [LinearMap.comp_apply, LinearMap.add_apply]
  rw [h_comp, map_add]

/-- tensor_inner_02(T, c•S) = c * tensor_inner_02(T, S). -/
theorem tensor_inner_02_smul_right (met : MetricDuality R V)
    (atr : AbstractTrace R V) (c : R) (T S : TensorData R V 0 2) :
    tensor_inner_02 met atr T (c • S) = c * tensor_inner_02 met atr T S := by
  simp only [tensor_inner_02]
  have h_comp : (tensor_02_endo met T).comp (tensor_02_endo met (c • S)) =
      c • (tensor_02_endo met T).comp (tensor_02_endo met S) := by
    rw [tensor_02_endo_smul]
    ext v
    simp [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [h_comp, map_smul, smul_eq_mul]

/-- tensor_inner_02(T, -S) = -tensor_inner_02(T, S). -/
theorem tensor_inner_02_neg_right (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T S : TensorData R V 0 2) :
    tensor_inner_02 met atr T (-S) = -tensor_inner_02 met atr T S := by
  rw [← neg_one_smul R S, tensor_inner_02_smul_right]
  ring

/-- tensor_inner_02(T, S - U) = tensor_inner_02(T, S) - tensor_inner_02(T, U). -/
theorem tensor_inner_02_sub_right (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T S U : TensorData R V 0 2) :
    tensor_inner_02 met atr T (S - U) =
      tensor_inner_02 met atr T S - tensor_inner_02 met atr T U := by
  rw [sub_eq_add_neg, tensor_inner_02_add_right, tensor_inner_02_neg_right]
  rw [sub_eq_add_neg]

/-- Symmetry of the abstract trace inner product. -/
theorem tensor_inner_02_symm (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T S : TensorData R V 0 2) :
    tensor_inner_02 met atr T S = tensor_inner_02 met atr S T := by
  exact atr.trace_comm (tensor_02_endo met T) (tensor_02_endo met S)

/-- The metric has squared norm `tr(id)` for the abstract trace. -/
theorem tensor_inner_02_metric_metric (met : MetricDuality R V)
    (atr : AbstractTrace R V) :
    tensor_inner_02 met atr met.g_tensor met.g_tensor =
      abstractTraceDimension atr := by
  simp only [tensor_inner_02, abstractTraceDimension, tensor_02_endo_metric]
  rw [LinearMap.comp_id]

/-- Expand the inner product of two tensor differences. -/
theorem tensor_inner_02_sub_sub (met : MetricDuality R V)
    (atr : AbstractTrace R V) (T U S W : TensorData R V 0 2) :
    tensor_inner_02 met atr (T - U) (S - W) =
      tensor_inner_02 met atr T S - tensor_inner_02 met atr T W -
        tensor_inner_02 met atr U S + tensor_inner_02 met atr U W := by
  rw [tensor_inner_02_sub_left, tensor_inner_02_sub_right, tensor_inner_02_sub_right]
  ring

end InnerProps

-- ============================================================
-- Section 3: Ricci norm squared
-- ============================================================

section RicciNormSq

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Squared norm of the Ricci tensor: |Rc|² = tr(Rc♯ ∘ Rc♯). -/
noncomputable def ricci_norm_sq
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    : R :=
  atr.tr ((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
          (RicciEndomorphism emb conn ha hal hsl hl atr met))

/-- Cubic trace of the Ricci endomorphism: `tr(Ric♯ ∘ Ric♯ ∘ Ric♯)`. -/
noncomputable def ricci_trace_cube
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    : R :=
  atr.tr ((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
    ((RicciEndomorphism emb conn ha hal hsl hl atr met).comp
      (RicciEndomorphism emb conn ha hal hsl hl atr met)))

/-- tensor_02_endo of ricciForm_tensor equals RicciEndomorphism. -/
theorem tensor_02_endo_ricciForm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    tensor_02_endo met (ricciForm_tensor emb conn ha hal hsl hl atr) =
    RicciEndomorphism emb conn ha hal hsl hl atr met := by
  ext X; change met.sharp (flat_covector (ricciForm_tensor emb conn ha hal hsl hl atr) X) =
    met.sharp (RcCovector emb conn ha hal hsl hl atr X)
  congr 1

/-- tensor_inner_02(Rc, Rc) = ricci_norm_sq. -/
theorem tensor_inner_02_ricciForm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    tensor_inner_02 met atr
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ricciForm_tensor emb conn ha hal hsl hl atr) =
    ricci_norm_sq emb conn ha hal hsl hl atr met := by
  simp only [tensor_inner_02, ricci_norm_sq, tensor_02_endo_ricciForm]

/-- The synthetic cubic trace of `ricciForm_tensor` is the cubic trace of the
Ricci endomorphism. -/
theorem tensor_trace_cube_02_ricciForm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    tensor_trace_cube_02 met atr
      (ricciForm_tensor emb conn ha hal hsl hl atr) =
    ricci_trace_cube emb conn ha hal hsl hl atr met := by
  simp only [tensor_trace_cube_02, ricci_trace_cube, tensor_02_endo_ricciForm]

/-- The trace inner product of Ricci with the metric is scalar curvature. -/
theorem tensor_inner_02_ricciForm_metric
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    tensor_inner_02 met atr
      (ricciForm_tensor emb conn ha hal hsl hl atr) met.g_tensor =
    ScalarCurvature emb conn ha hal hsl hl atr met := by
  simp only [tensor_inner_02, tensor_02_endo_ricciForm, tensor_02_endo_metric,
    ScalarCurvature]
  rw [LinearMap.comp_id]

/-- The trace inner product of the metric with Ricci is scalar curvature. -/
theorem tensor_inner_02_metric_ricciForm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) :
    tensor_inner_02 met atr met.g_tensor
      (ricciForm_tensor emb conn ha hal hsl hl atr) =
    ScalarCurvature emb conn ha hal hsl hl atr met := by
  rw [tensor_inner_02_symm, tensor_inner_02_ricciForm_metric]

end RicciNormSq

-- ============================================================
-- Section 4: Ricci raise variation
-- ============================================================

section RicciRaise

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Product rule for the metric with a varying vector argument.

    ∂_t[g(s)(A(s), B)] = (∂_t g)(A(t), B) + ∂_t[g(t)(A(s), B)]

    In abstract settings this is an independent property connecting
    time derivatives of the metric with time derivatives of vector-valued
    functions observed through the metric. -/
def MetricBilinProductRule
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (g_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    : Prop :=
  ∀ (A : Time → V) (B : V) (t : Time),
    td.dt_apply (fun s => (g_fam s).g (A s) B) t =
    metric_var_form td g_fam h_met t ![A t, B] ![] +
    td.dt_apply (fun s => (g_fam t).g (A s) B) t

/-- Ricci raise variation: the time derivative of the raised Ricci tensor
    observed through the fixed metric g(t) equals the Ricci variation
    minus the metric variation.

    Formulated using scalar time derivatives only (no V-valued derivatives). -/
theorem ricci_raise_variation
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
    (h_mvp : MetricBilinProductRule td g_fam h_met)
    (h_Rc_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) atr vs αs))
    (t : Time) (X Y : V) :
    td.dt_apply (fun s => (g_fam t).g
      (RicciEndomorphism emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s) X) Y) t =
    dt_tensor td t (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr)
      h_Rc_smooth ![X, Y] ![] -
    metric_var_form td g_fam h_met t
      ![RicciEndomorphism emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t) X, Y] ![] := by
  -- Function equality: g(s)(RicciEndo_s(X), Y) = ricciForm_tensor_s ![X, Y] ![]
  have h_feq : (fun s => (g_fam s).g
      (RicciEndomorphism emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s) X) Y) =
    (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr ![X, Y] ![]) :=
    funext (fun s => (RicciEndomorphism_spec emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s) X Y).trans
      (ricciForm_tensor_eval emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr X Y).symm)
  -- Product rule: dt[g(s)(A(s), Y)] = metric_var(A(t), Y) + dt[g(t)(A(s), Y)]
  have h_prod := h_mvp
    (fun s => RicciEndomorphism emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s) X) Y t
  -- Rewrite LHS of h_prod: dt[g(s)(RicciEndo_s(X), Y)] = dt[Rc_s(X, Y)]
  rw [show td.dt_apply (fun s => (g_fam s).g
      (RicciEndomorphism emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s) X) Y) t =
    td.dt_apply (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr ![X, Y] ![]) t from
    congr_arg (fun f => td.dt_apply f t) h_feq] at h_prod
  -- h_prod now: dt[ricciForm(X,Y)] = metric_var + dt[g(t)(A(s), Y)]
  -- Goal: dt[g(t)(A(s), Y)] = dt_tensor(Rc)(X,Y) - metric_var
  rw [add_comm] at h_prod; exact (sub_eq_of_eq_add h_prod).symm

end RicciRaise

-- ============================================================
-- Section 5: Scalar curvature product rule (hypothesis)
-- ============================================================

section SCProductRule

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- The scalar curvature product rule: ∂_t(ScalarCurvature) decomposes
    into a metric variation term and a Ricci variation term.

    This combines TimeTrComm, the metric bilinear product rule, and the
    relationship between endomorphism trace and metric trace. It is the
    analog of the old MetricTimeDerivativeRules.t_metric_trace_varying. -/
def ScalarCurvatureProductRule
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
    (h_Rc_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) atr vs αs))
    : Prop :=
  ∀ t,
    td.dt_apply (fun s => ScalarCurvature emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s)) t =
    -tensor_inner_02 (g_fam t) atr
      (metric_var_form td g_fam h_met t)
      (ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr) +
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor td t (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr)
        h_Rc_smooth) ![] ![]

end SCProductRule

-- ============================================================
-- Section 6: Scalar curvature evolution
-- ============================================================

section SCEvolution

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Scalar curvature evolution under Ricci flow:

    ∂_t R = 2|Rc|² + metric_trace_g(t)(∂_t Rc)

    The first term arises from the metric variation (∂_t g = -2Rc induces
    ∂_t(g⁻¹) = 2Rc♯, contributing 2|Rc|² to the trace).
    The second term is the Ricci variation trace, identified with ΔR
    via the contracted second Bianchi identity (proved separately). -/
theorem scalar_curvature_evolution
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
    (h_Rc_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ) (hl_fam τ) atr vs αs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth)
    (t : Time) :
    td.dt_apply (fun s => ScalarCurvature emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr (g_fam s)) t =
    2 * ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t) +
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor td t (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s) atr)
        h_Rc_smooth) ![] ![] := by
  -- Step 1: Apply the product rule
  have h_prod := h_sc_prod t
  -- Step 2: Ricci flow equation: metric_var_form = -2 • Rc
  have h_rf_eq := h_rf.evolution t
  -- Step 3: Substitute and compute
  have h_inner : -tensor_inner_02 (g_fam t) atr
      (metric_var_form td g_fam h_met t)
      (ricciForm_tensor emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr) =
    2 * ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr (g_fam t) := by
    rw [h_rf_eq, tensor_inner_02_smul_left, tensor_inner_02_ricciForm]; ring
  rw [h_prod, h_inner]

end SCEvolution

-- ============================================================
-- Section 7: Closed scalar curvature evolution interface
-- ============================================================

section FullScalarEvolution

variable {k R V Time : Type*} {A : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Interface identifying `tr_g(d_t Rc)` with the scalar Laplacian term. -/
def RicciTraceIdentity
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
    (scalar_laplacian : Time -> R) : Prop :=
  forall t,
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1)
      (dt_tensor td t
        (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s) atr)
        h_Rc_smooth) ![] ![] = scalar_laplacian t

/-- Trace identity for a supplied Ricci-evolution RHS tensor. -/
def RicciTraceIdentityForRHS
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (rhs : Time -> TensorData R V 0 2)
    (rhs_trace : Time -> R) : Prop :=
  forall t,
    metric_trace (g_fam t) atr (0 : Fin 2) (0 : Fin 1) (rhs t) ![] ![] =
      rhs_trace t

/-- Build `RicciTraceIdentity` from a Ricci evolution RHS and the trace of that RHS. -/
theorem ricciTraceIdentity_from_rhs_evolution
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
    (rhs : Time -> TensorData R V 0 2)
    (rhs_trace : Time -> R)
    (h_evol : forall t,
      dt_tensor td t
        (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s) atr)
        h_Rc_smooth = rhs t)
    (h_trace : RicciTraceIdentityForRHS atr g_fam rhs rhs_trace) :
    RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_Rc_smooth rhs_trace := by
  intro t
  rw [h_evol t]
  exact h_trace t

/-- Closed scalar curvature evolution, once the Ricci trace identity is supplied. -/
theorem scalar_curvature_evolution_full
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (scalar_laplacian : Time -> R)
    (h_trace : RicciTraceIdentity emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam
      hl_fam h_Rc_smooth scalar_laplacian)
    (t : Time) :
    td.dt_apply
      (fun s => ScalarCurvature emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s)) t =
    scalar_laplacian t +
      2 * ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t) := by
  rw [scalar_curvature_evolution emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam
    hl_fam h_Rc_smooth h_rf h_sc_prod t]
  rw [h_trace t]
  ring

/-- Closed scalar curvature evolution from a supplied Ricci-evolution RHS and its trace. -/
theorem scalar_curvature_evolution_full_from_rhs
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_Rc_smooth : forall vs αs, td.isSmoothFam
      (fun τ => ricciForm_tensor emb (conn_fam τ) (ha_fam τ) (hal_fam τ) (hsl_fam τ)
        (hl_fam τ) atr vs αs))
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_sc_prod : ScalarCurvatureProductRule emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam h_Rc_smooth)
    (rhs : Time -> TensorData R V 0 2)
    (rhs_trace : Time -> R)
    (h_evol : forall t,
      dt_tensor td t
        (fun s => ricciForm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
          (hl_fam s) atr)
        h_Rc_smooth = rhs t)
    (h_trace : RicciTraceIdentityForRHS atr g_fam rhs rhs_trace)
    (t : Time) :
    td.dt_apply
      (fun s => ScalarCurvature emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s) atr (g_fam s)) t =
    rhs_trace t +
      2 * ricci_norm_sq emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t)
        (hl_fam t) atr (g_fam t) :=
  scalar_curvature_evolution_full emb td atr g_fam h_met conn_fam ha_fam hal_fam
    hsl_fam hl_fam h_Rc_smooth h_rf h_sc_prod rhs_trace
    (ricciTraceIdentity_from_rhs_evolution emb td atr g_fam conn_fam ha_fam hal_fam
      hsl_fam hl_fam h_Rc_smooth rhs rhs_trace h_evol h_trace) t

end FullScalarEvolution
