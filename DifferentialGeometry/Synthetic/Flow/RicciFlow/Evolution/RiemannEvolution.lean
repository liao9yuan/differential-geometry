import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RiemannVariation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RiemannLaplacian
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Evolution of the Riemann Curvature Tensor

∂_t Rm = ΔRm + Q(Rm, Rc, g, ∇).
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Riemann Variation Tensor, Q(Rm), Evolution
-- ============================================================

section RiemannEvolution

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- The Riemann variation tensor, defined through the geometric variation formula.

    INDEPENDENT of dt_tensor(Rm): the scalar value at each evaluation point is the
    5-term expression from NablaTimeProductRule involving conn_var_vector, nabla_tensor,
    and bracket. Multilinearity is proved via the substantive equivalence with
    dt_tensor(Rm) established by `variation_scalar_eq_dt_tensor`. -/
noncomputable def riemann_variation_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (_h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (t : Time) : TensorData R V 1 3 where
  toFun vs :=
    -- The inner MultilinearMap uses the variation scalar formula
    let dt_Rm := dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
      (hsl_fam s) (hl_fam s))
    -- Inherit multilinearity from dt_Rm, but evaluate through the variation formula
    { toFun := fun αs =>
        riemann_variation_scalar emb td conn_fam ha_fam hl_fam t (vs 0) (vs 1) (vs 2) (αs 0)
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        change _ = _ + _
        simp only [Function.update_self]
        -- Reduce to dt_Rm multilinearity via the scalar equivalence
        let he := fun ω => variation_scalar_eq_dt_tensor emb td conn_fam ha_fam hal_fam hsl_fam
          hl_fam h_pr (vs 0) (vs 1) (vs 2) ω t
        rw [he, he, he]; exact (dt_Rm vs).map_update_add ![β₁] 0 β₁ β₂
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp only [Function.update_self, smul_eq_mul]
        let he := fun ω => variation_scalar_eq_dt_tensor emb td conn_fam ha_fam hal_fam hsl_fam
          hl_fam h_pr (vs 0) (vs 1) (vs 2) ω t
        rw [he, he]
        have h := (dt_Rm vs).map_update_smul ![β] 0 c β
        simp only [smul_eq_mul] at h; exact h }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    let dt_Rm := dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
      (hsl_fam s) (hl_fam s))
    let he := fun X Y Z => variation_scalar_eq_dt_tensor emb td conn_fam ha_fam hal_fam hsl_fam
      hl_fam h_pr X Y Z (αs 0) t
    rw [he, he, he]
    exact congr_arg (· αs) (dt_Rm.map_update_add vs idx v₁ v₂)
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    let dt_Rm := dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
      (hsl_fam s) (hl_fam s))
    let he := fun X Y Z => variation_scalar_eq_dt_tensor emb td conn_fam ha_fam hal_fam hsl_fam
      hl_fam h_pr X Y Z (αs 0) t
    rw [he, he]
    exact congr_arg (· αs) (dt_Rm.map_update_smul vs idx c v)

/-- The Riemann variation formula: dt_tensor(Rm) equals the variation tensor. -/
theorem riemann_variation_formula
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (t : Time) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)) =
    riemann_variation_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t := by
  ext vs αs
  exact (variation_scalar_eq_dt_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr
    (vs 0) (vs 1) (vs 2) (αs 0) t).symm


/-- The quadratic curvature operator Q(Rm) = riemann_variation_tensor − ΔRm. -/
noncomputable def Q_rm
    (td : TimeDerivativeData R A Time)
    (emb : DerivationEmbedding k R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (atr : AbstractTrace R V)
    (met : MetricDuality R V) 
    (t : Time)
    : TensorData R V 1 3 :=
  riemann_variation_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t -
  rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t) atr met

/-- Evolution of the Riemann curvature tensor: ∂_t Rm = Δ(Rm) + Q(Rm). -/
theorem riemann_tensor_evolution
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (_h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (g_fam : Time → MetricDuality R V)
    
    (_h_mc : ∀ s, IsMetricCompatible emb (conn_fam s) (g_fam s))
    (_h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (_h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    (t : Time) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)) =
    rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t) atr (g_fam t) +
    Q_rm td emb conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf atr (g_fam t) t := by
  rw [riemann_variation_formula emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t]
  simp only [Q_rm]; abel

end RiemannEvolution

-- ============================================================
-- Section 2: Hamilton Quadratic — Independent Scalar-Level Definition
-- ============================================================

section HamiltonQuadratic

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable {A : Type*} [CommRing A] [Algebra R A]

-- ============================================================
-- 2.1  A_rf_scalar: connection variation under Ricci flow
-- ============================================================

/-- Connection variation under Ricci flow at the scalar level.
    **Purely spatial**: no ∂_t, no conn_var, no dt_tensor. -/
noncomputable def A_rf_scalar
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (U W : V) (ω : V →ₗ[R] R) : R :=
  - ricci_cov_deriv emb conn ha hal hsl hl atr U W (met.sharp ω)
  - ricci_cov_deriv emb conn ha hal hsl hl atr W U (met.sharp ω)
  + ricci_cov_deriv emb conn ha hal hsl hl atr (met.sharp ω) U W

-- ============================================================
-- 2.2  Bridge: conn_var = A_rf under Ricci flow
-- ============================================================

/-- Under Ricci flow, the connection variation evaluates as A_rf_scalar. -/
theorem conn_var_eq_A_rf
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (U W : V) (ω : V →ₗ[R] R) :
    conn_var_vector td conn_fam t U W ![] ![ω] =
    A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) U W ω := by
  rw [conn_var_vector_eval]
  have h_ω : ∀ v : V, ω v = (g_fam t).g v ((g_fam t).sharp ω) := by
    intro v; rw [← (g_fam t).g_sharp ω v, (g_fam t).g_symm]
  have h_fun : (fun s => ω (conn_fam s U W)) =
      (fun s => (g_fam t).g (conn_fam s U W) ((g_fam t).sharp ω)) :=
    funext (fun _ => h_ω _)
  rw [h_fun]
  change _ = - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
              U W ((g_fam t).sharp ω)
           - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
              W U ((g_fam t).sharp ω)
           + ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t) atr
              ((g_fam t).sharp ω) U W
  exact connection_evolution emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_rf h2 t h_decomp U W ((g_fam t).sharp ω)

-- ============================================================
-- 2.3  Q_hamilton_scalar: independent definition
-- ============================================================

/-- The Hamilton quadratic at the scalar level, defined independently.
    **No ∂_t. No conn_var. No dt_tensor.** -/
noncomputable def Q_hamilton_scalar
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y Z : V) (ω : V →ₗ[R] R) : R :=
  let A := A_rf_scalar emb conn ha hal hsl hl atr met
  let nd := nabla_dual emb conn ha hl
  -- (∇_X A)(Y,Z)(ω):
  ((emb.embed X) (A Y Z ω) - A Y Z (nd X ω) - A (conn X Y) Z ω - A Y (conn X Z) ω)
  -- minus (∇_Y A)(X,Z)(ω):
  - ((emb.embed Y) (A X Z ω) - A X Z (nd Y ω) - A (conn Y X) Z ω - A X (conn Y Z) ω)
  -- minus ΔRm(X,Y,Z)(ω):
  - rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω]

-- ============================================================
-- 2.4  Helper: nabla of (1,0) tensor expansion
-- ============================================================

/-- For a (1,0) tensor T, ∇_X T evaluated at ![] ![ω] equals
    X(T ![] ![ω]) − T ![] ![∇*_X ω]. -/
private theorem nabla_10_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 1 0) (ω : V →ₗ[R] R) :
    nabla_tensor emb conn ha hl X T ![] ![ω] =
    (emb.embed X) (T ![] ![ω]) - T ![] ![nabla_dual emb conn ha hl X ω] := by
  rw [nabla_tensor_eval]
  have h0 : ∑ i : Fin 0, T (Function.update ![] i (conn X (![] i))) ![ω] = 0 := by
    simp [Finset.univ_eq_empty]
  rw [h0, sub_zero]
  congr 1
  rw [show Finset.sum Finset.univ
      (fun j => T ![] (Function.update ![ω] j (nabla_dual emb conn ha hl X (![ω] j)))) =
    T ![] (Function.update ![ω] (0 : Fin 1) (nabla_dual emb conn ha hl X (![ω] 0))) from
    by simp [Finset.univ_unique, Finset.sum_singleton]]
  congr 1
  ext i; fin_cases i; simp [Function.update]

-- ============================================================
-- 2.5  Helper: nabla_conn_var expressed through A_rf
-- ============================================================

/-- Under Ricci flow, nabla_conn_var_scalar equals the A_rf_scalar expansion. -/
private theorem nabla_conn_var_as_A_rf
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω =
    (emb.embed X) (A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) Y Z ω)
    - A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) Y Z (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X ω)
    - A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) (conn_fam t X Y) Z ω
    - A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) Y (conn_fam t X Z) ω := by
  have hA : ∀ (P Q : V) (β : V →ₗ[R] R),
      conn_var_vector td conn_fam t P Q ![] ![β] =
      A_rf_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
        atr (g_fam t) P Q β :=
    fun P Q β => conn_var_eq_A_rf emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
      h_rf h2 t h_decomp P Q β
  simp only [nabla_conn_var_scalar]
  rw [nabla_10_eval emb (conn_fam t) (ha_fam t) (hl_fam t) X
    (conn_var_vector td conn_fam t Y Z) ω]
  rw [hA Y Z ω,
      hA Y Z (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X ω),
      hA (conn_fam t X Y) Z ω,
      hA Y (conn_fam t X Z) ω]

-- ============================================================
-- 2.6  Main theorem: Q_rm = Q_hamilton
-- ============================================================

/-- Q_rm equals the Hamilton quadratic. -/
theorem Q_rm_eq_hamilton
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_rm td emb conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf atr (g_fam t) t
      ![X, Y, Z] ![ω] =
    Q_hamilton_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) X Y Z ω := by
  change (riemann_variation_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t -
    rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t)
      atr (g_fam t)) ![X, Y, Z] ![ω] = _
  simp only [MultilinearMap.sub_apply]
  have h_var : riemann_variation_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t
      ![X, Y, Z] ![ω] =
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω -
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t Y X Z ω := by
    have h_form := riemann_variation_formula emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t
    rw [show riemann_variation_tensor emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf t
        ![X, Y, Z] ![ω] =
      dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
        (hl_fam s)) ![X, Y, Z] ![ω] from by rw [← h_form]]
    rw [variation_eq_dt emb td conn_fam ha_fam hal_fam hsl_fam hl_fam X Y Z ω t]
    exact riemann_variation_torsion_free emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf
      X Y Z ω t
  rw [h_var]
  rw [nabla_conn_var_as_A_rf emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        h_rf h2 t h_decomp X Y Z ω,
      nabla_conn_var_as_A_rf emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
        h_rf h2 t h_decomp Y X Z ω]
  simp only [Q_hamilton_scalar]

-- ============================================================
-- 2.7  Corollary: Hamilton decomposition
-- ============================================================

/-- Hamilton decomposition at the scalar level:
    the Riemann variation = ΔRm + Q_hamilton. -/
theorem hamilton_decomposition
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (X Y Z : V) (ω : V →ₗ[R] R) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
      (hl_fam s)) ![X, Y, Z] ![ω] =
    rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t)
      atr (g_fam t) ![X, Y, Z] ![ω] +
    Q_hamilton_scalar emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) X Y Z ω := by
  have h_evol := riemann_tensor_evolution emb td h_st atr conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_tf g_fam (fun s => (h_rf.levi_civita s).1) h_rf h_pr h2 t
  have h_eval : dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s)
      (hsl_fam s) (hl_fam s)) ![X, Y, Z] ![ω] =
    (rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t) atr (g_fam t) +
    Q_rm td emb conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf atr (g_fam t) t)
      ![X, Y, Z] ![ω] := by rw [h_evol]
  rw [h_eval]; simp only [MultilinearMap.add_apply]
  rw [Q_rm_eq_hamilton emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf
    h_rf h2 t h_decomp X Y Z ω]

end HamiltonQuadratic

-- ============================================================
-- Section 3: A_rf_scalar Linearity — Direct Proofs
-- ============================================================

section ArfLinearity

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

-- Rc linearity helpers (from Rm multilinearity + tr linearity)
private theorem Rc_add_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (X₁ X₂ Z : V) :
    Rc emb conn ha hal hsl hl atr (X₁ + X₂) Z =
    Rc emb conn ha hal hsl hl atr X₁ Z + Rc emb conn ha hal hsl hl atr X₂ Z := by
  simp only [Rc]
  rw [show RcEndo emb conn ha hal hsl hl (X₁ + X₂) Z =
      RcEndo emb conn ha hal hsl hl X₁ Z + RcEndo emb conn ha hal hsl hl X₂ Z from
    LinearMap.ext (fun Y => Rm_add_Y emb conn ha hal Y X₁ X₂ Z)]
  exact map_add atr.tr _ _

private theorem Rc_smul_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (c : R) (X Z : V) :
    Rc emb conn ha hal hsl hl atr (c • X) Z =
    c * Rc emb conn ha hal hsl hl atr X Z := by
  simp only [Rc]
  rw [show RcEndo emb conn ha hal hsl hl (c • X) Z =
      c • RcEndo emb conn ha hal hsl hl X Z from
    LinearMap.ext (fun Y => Rm_smul_Y emb conn hal hsl hl c Y X Z)]
  rw [atr.tr.map_smul, smul_eq_mul]

private theorem Rc_add_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (X Z₁ Z₂ : V) :
    Rc emb conn ha hal hsl hl atr X (Z₁ + Z₂) =
    Rc emb conn ha hal hsl hl atr X Z₁ + Rc emb conn ha hal hsl hl atr X Z₂ := by
  simp only [Rc]
  rw [show RcEndo emb conn ha hal hsl hl X (Z₁ + Z₂) =
      RcEndo emb conn ha hal hsl hl X Z₁ + RcEndo emb conn ha hal hsl hl X Z₂ from
    LinearMap.ext (fun Y => Rm_add_Z emb conn ha hal Y X Z₁ Z₂)]
  exact map_add atr.tr _ _

private theorem Rc_smul_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (c : R) (X Z : V) :
    Rc emb conn ha hal hsl hl atr X (c • Z) =
    c * Rc emb conn ha hal hsl hl atr X Z := by
  simp only [Rc]
  rw [show RcEndo emb conn ha hal hsl hl X (c • Z) =
      c • RcEndo emb conn ha hal hsl hl X Z from
    LinearMap.ext (fun Y => Rm_smul_Z emb conn ha hsl hl c Y X Z)]
  rw [atr.tr.map_smul, smul_eq_mul]

-- ricci_cov_deriv linearity in each argument
-- rcd(X,Y,Z) = X(Rc(Y,Z)) - Rc(conn(X,Y),Z) - Rc(Y,conn(X,Z))

private theorem rcd_add_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (X₁ X₂ Y Z : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr (X₁ + X₂) Y Z =
    ricci_cov_deriv emb conn ha hal hsl hl atr X₁ Y Z +
    ricci_cov_deriv emb conn ha hal hsl hl atr X₂ Y Z := by
  unfold ricci_cov_deriv
  rw [action_add_left,
    hal X₁ X₂ Y, Rc_add_X emb conn ha hal hsl hl atr (conn X₁ Y) (conn X₂ Y) Z,
    hal X₁ X₂ Z, Rc_add_Z emb conn ha hal hsl hl atr Y (conn X₁ Z) (conn X₂ Z)]
  ring

private theorem rcd_smul_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (c : R) (X Y Z : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr (c • X) Y Z =
    c * ricci_cov_deriv emb conn ha hal hsl hl atr X Y Z := by
  unfold ricci_cov_deriv
  rw [action_smul_left,
    hsl c X Y, Rc_smul_X emb conn ha hal hsl hl atr c (conn X Y) Z,
    hsl c X Z, Rc_smul_Z emb conn ha hal hsl hl atr c Y (conn X Z)]
  ring

private theorem rcd_add_Y
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (X Y₁ Y₂ Z : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr X (Y₁ + Y₂) Z =
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y₁ Z +
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y₂ Z := by
  unfold ricci_cov_deriv
  rw [Rc_add_X emb conn ha hal hsl hl atr Y₁ Y₂ Z, action_add_right,
    ha X Y₁ Y₂, Rc_add_X emb conn ha hal hsl hl atr (conn X Y₁) (conn X Y₂) Z,
    Rc_add_X emb conn ha hal hsl hl atr Y₁ Y₂ (conn X Z)]
  ring

private theorem rcd_smul_Y
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (c : R) (X Y Z : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr X (c • Y) Z =
    c * ricci_cov_deriv emb conn ha hal hsl hl atr X Y Z := by
  unfold ricci_cov_deriv
  rw [Rc_smul_X emb conn ha hal hsl hl atr c Y Z, action_smul_right,
    hl X c Y]
  simp only [action] at *
  rw [Rc_add_X emb conn ha hal hsl hl atr _ _ Z,
    Rc_smul_X emb conn ha hal hsl hl atr ((emb.embed X) c) Y Z,
    Rc_smul_X emb conn ha hal hsl hl atr c (conn X Y) Z,
    Rc_smul_X emb conn ha hal hsl hl atr c Y (conn X Z)]
  ring

private theorem rcd_add_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (X Y Z₁ Z₂ : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y (Z₁ + Z₂) =
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y Z₁ +
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y Z₂ := by
  unfold ricci_cov_deriv
  rw [Rc_add_Z emb conn ha hal hsl hl atr Y Z₁ Z₂, action_add_right,
    Rc_add_Z emb conn ha hal hsl hl atr (conn X Y) Z₁ Z₂,
    ha X Z₁ Z₂, Rc_add_Z emb conn ha hal hsl hl atr Y (conn X Z₁) (conn X Z₂)]
  ring

private theorem rcd_smul_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hal hsl hl)
    (atr : AbstractTrace R V) (c : R) (X Y Z : V) :
    ricci_cov_deriv emb conn ha hal hsl hl atr X Y (c • Z) =
    c * ricci_cov_deriv emb conn ha hal hsl hl atr X Y Z := by
  unfold ricci_cov_deriv
  rw [Rc_smul_Z emb conn ha hal hsl hl atr c Y Z, action_smul_right,
    Rc_smul_Z emb conn ha hal hsl hl atr c (conn X Y) Z,
    hl X c Z]
  simp only [action] at *
  rw [Rc_add_Z emb conn ha hal hsl hl atr Y _ _,
    Rc_smul_Z emb conn ha hal hsl hl atr ((emb.embed X) c) Y Z,
    Rc_smul_Z emb conn ha hal hsl hl atr c Y (conn X Z)]
  ring

-- ============================================================
-- A_rf_scalar linearity: add/smul in each of U, W, ω
-- ============================================================

/-- A_rf_scalar is additive in U. -/
theorem A_rf_scalar_add_U
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (U₁ U₂ W : V) (ω : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met (U₁ + U₂) W ω =
    A_rf_scalar emb conn ha hal hsl hl atr met U₁ W ω +
    A_rf_scalar emb conn ha hal hsl hl atr met U₂ W ω := by
  simp only [A_rf_scalar]
  rw [rcd_add_X emb conn ha hal hsl hl atr U₁ U₂ W _,
      rcd_add_Y emb conn ha hal hsl hl atr W U₁ U₂ _,
      rcd_add_Y emb conn ha hal hsl hl atr _ U₁ U₂ W]
  ring

/-- A_rf_scalar is R-homogeneous in U. -/
theorem A_rf_scalar_smul_U
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (U W : V) (ω : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met (c • U) W ω =
    c * A_rf_scalar emb conn ha hal hsl hl atr met U W ω := by
  simp only [A_rf_scalar]
  rw [rcd_smul_X emb conn ha hal hsl hl atr c U W _,
      rcd_smul_Y emb conn ha hal hsl hl atr c W U _,
      rcd_smul_Y emb conn ha hal hsl hl atr c _ U W]
  ring

/-- A_rf_scalar is additive in W. -/
theorem A_rf_scalar_add_W
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (U W₁ W₂ : V) (ω : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met U (W₁ + W₂) ω =
    A_rf_scalar emb conn ha hal hsl hl atr met U W₁ ω +
    A_rf_scalar emb conn ha hal hsl hl atr met U W₂ ω := by
  simp only [A_rf_scalar]
  rw [rcd_add_Y emb conn ha hal hsl hl atr U W₁ W₂ _,
      rcd_add_X emb conn ha hal hsl hl atr W₁ W₂ U _,
      rcd_add_Z emb conn ha hal hsl hl atr _ U W₁ W₂]
  ring

/-- A_rf_scalar is R-homogeneous in W. -/
theorem A_rf_scalar_smul_W
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (U W : V) (ω : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met U (c • W) ω =
    c * A_rf_scalar emb conn ha hal hsl hl atr met U W ω := by
  simp only [A_rf_scalar]
  rw [rcd_smul_Y emb conn ha hal hsl hl atr c U W _,
      rcd_smul_X emb conn ha hal hsl hl atr c W U _,
      rcd_smul_Z emb conn ha hal hsl hl atr c _ U W]
  ring

/-- A_rf_scalar is additive in ω. -/
theorem A_rf_scalar_add_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (U W : V) (ω₁ ω₂ : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met U W (ω₁ + ω₂) =
    A_rf_scalar emb conn ha hal hsl hl atr met U W ω₁ +
    A_rf_scalar emb conn ha hal hsl hl atr met U W ω₂ := by
  simp only [A_rf_scalar]
  rw [met.sharp_add ω₁ ω₂,
      rcd_add_Z emb conn ha hal hsl hl atr U W _ _,
      rcd_add_Z emb conn ha hal hsl hl atr W U _ _,
      rcd_add_X emb conn ha hal hsl hl atr _ _ U W]
  ring

/-- A_rf_scalar is R-homogeneous in ω. -/
theorem A_rf_scalar_smul_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (U W : V) (ω : V →ₗ[R] R) :
    A_rf_scalar emb conn ha hal hsl hl atr met U W (c • ω) =
    c * A_rf_scalar emb conn ha hal hsl hl atr met U W ω := by
  simp only [A_rf_scalar]
  rw [met.sharp_smul c ω,
      rcd_smul_Z emb conn ha hal hsl hl atr c U W _,
      rcd_smul_Z emb conn ha hal hsl hl atr c W U _,
      rcd_smul_X emb conn ha hal hsl hl atr c _ U W]
  ring

end ArfLinearity

-- ============================================================
-- Section 4: Q_hamilton_scalar Linearity — Direct Proofs
-- ============================================================

section QHamiltonLinearity

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

-- nabla_dual linearity in X
private theorem nabla_dual_add_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X₁ X₂ : V) (ω : V →ₗ[R] R) :
    nabla_dual emb conn ha hl (X₁ + X₂) ω =
    nabla_dual emb conn ha hl X₁ ω + nabla_dual emb conn ha hl X₂ ω := by
  ext Y; simp only [nabla_dual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  have : (emb.embed (X₁ + X₂)) (ω Y) = (emb.embed X₁) (ω Y) + (emb.embed X₂) (ω Y) := by
    simp only [map_add, Derivation.add_apply]
  rw [this, hal X₁ X₂ Y, map_add ω]; ring

private theorem nabla_dual_smul_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (c : R) (X : V) (ω : V →ₗ[R] R) :
    nabla_dual emb conn ha hl (c • X) ω =
    c • nabla_dual emb conn ha hl X ω := by
  ext Y; simp only [nabla_dual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]
  have : (emb.embed (c • X)) (ω Y) = c * (emb.embed X) (ω Y) := by
    simp only [map_smul, Derivation.smul_apply, smul_eq_mul]
  rw [this, hsl c X Y, map_smul ω, smul_eq_mul]; ring

-- ============================================================
-- Q_hamilton_scalar linearity in each argument
-- ============================================================

-- Helper lemmas for rough_laplacian_Rm multilinearity with ![...] notation.
-- These convert from Function.update form to explicit matrix form.

private theorem rlap_add_pos0
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X₁ X₂ Y Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X₁ + X₂, Y, Z] ![ω] =
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X₁, Y, Z] ![ω] +
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X₂, Y, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_add
    ![X₁, Y, Z] 0 X₁ X₂
  have upd : ∀ (v : V), Function.update ![X₁, Y, Z] 0 v = ![v, Y, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h; exact congr_arg (· ![ω]) h

private theorem rlap_smul_pos0
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![c • X, Y, Z] ![ω] =
    c * rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_smul
    ![X, Y, Z] 0 c X
  have upd : ∀ (v : V), Function.update ![X, Y, Z] 0 v = ![v, Y, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h
  have h' := congr_arg (· ![ω]) h
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h'; exact h'

private theorem rlap_add_pos1
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y₁ Y₂ Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y₁ + Y₂, Z] ![ω] =
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y₁, Z] ![ω] +
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y₂, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_add
    ![X, Y₁, Z] 1 Y₁ Y₂
  have upd : ∀ (v : V), Function.update ![X, Y₁, Z] 1 v = ![X, v, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h; exact congr_arg (· ![ω]) h

private theorem rlap_smul_pos1
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, c • Y, Z] ![ω] =
    c * rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_smul
    ![X, Y, Z] 1 c Y
  have upd : ∀ (v : V), Function.update ![X, Y, Z] 1 v = ![X, v, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h
  have h' := congr_arg (· ![ω]) h
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h'; exact h'

private theorem rlap_add_pos2
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y Z₁ Z₂ : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z₁ + Z₂] ![ω] =
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z₁] ![ω] +
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z₂] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_add
    ![X, Y, Z₁] 2 Z₁ Z₂
  have upd : ∀ (v : V), Function.update ![X, Y, Z₁] 2 v = ![X, Y, v] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h; exact congr_arg (· ![ω]) h

private theorem rlap_smul_pos2
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, c • Z] ![ω] =
    c * rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met).map_update_smul
    ![X, Y, Z] 2 c Z
  have upd : ∀ (v : V), Function.update ![X, Y, Z] 2 v = ![X, Y, v] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [upd] at h
  have h' := congr_arg (· ![ω]) h
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h'; exact h'

private theorem rlap_add_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y Z : V) (ω₁ ω₂ : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω₁ + ω₂] =
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω₁] +
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω₂] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z]).map_update_add
    ![ω₁] 0 ω₁ ω₂
  have upd : ∀ (v : V →ₗ[R] R), Function.update (![ω₁] : Fin 1 → V →ₗ[R] R) 0 v = ![v] := by
    intro v; ext i; fin_cases i; simp [Function.update]
  simp only [upd] at h; exact h

private theorem rlap_smul_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![c • ω] =
    c * rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z] ![ω] := by
  have h := (rough_laplacian_Rm emb conn ha hl hal hsl atr met ![X, Y, Z]).map_update_smul
    ![ω] 0 c ω
  have upd : ∀ (v : V →ₗ[R] R), Function.update (![ω] : Fin 1 → V →ₗ[R] R) 0 v = ![v] := by
    intro v; ext i; fin_cases i; simp [Function.update]
  simp only [upd, smul_eq_mul] at h; exact h

-- ============================================================
-- Q_hamilton_scalar linearity in each argument
-- ============================================================

-- The key pattern: Q = (∇_X A)(Y,Z,ω) - (∇_Y A)(X,Z,ω) - ΔRm(X,Y,Z,ω)
-- where (∇_P A)(U,V,ω) = P(A(U,V,ω)) - A(U,V,∇*_P ω) - A(∇_P U, V, ω) - A(U, ∇_P V, ω)
--
-- ∇_P A is R-linear in P, U, V, ω because Leibniz corrections cancel.

-- Helper: (emb.embed (X₁ + X₂)) val = (emb.embed X₁) val + (emb.embed X₂) val
private theorem embed_add_apply (emb : DerivationEmbedding k R V)
    (X₁ X₂ : V) (val : R) :
    (emb.embed (X₁ + X₂)) val = (emb.embed X₁) val + (emb.embed X₂) val := by
  simp only [map_add, Derivation.add_apply]

-- Helper: (emb.embed (c • X)) val = c * (emb.embed X) val
private theorem embed_smul_apply (emb : DerivationEmbedding k R V)
    (c : R) (X : V) (val : R) :
    (emb.embed (c • X)) val = c * (emb.embed X) val := by
  simp only [map_smul, Derivation.smul_apply, smul_eq_mul]

/-- Q_hamilton_scalar is additive in X. -/
theorem Q_hamilton_add_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X₁ X₂ Y Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met (X₁ + X₂) Y Z ω =
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X₁ Y Z ω +
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X₂ Y Z ω := by
  simp only [Q_hamilton_scalar]
  -- First bracket: rewrite embed(X₁+X₂), nabla_dual(X₁+X₂), conn(X₁+X₂,_)
  rw [embed_add_apply emb X₁ X₂,
    nabla_dual_add_X emb conn ha hal hl X₁ X₂ ω,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met Y Z _ _,
    hal X₁ X₂ Y, A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    hal X₁ X₂ Z, A_rf_scalar_add_W emb conn ha hal hsl hl atr met Y _ _ ω]
  -- Second bracket: first split A(X₁+X₂,...) THEN use map_add
  rw [A_rf_scalar_add_U emb conn ha hal hsl hl atr met X₁ X₂ Z ω,
    (emb.embed Y).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met X₁ Z ω)
      (A_rf_scalar emb conn ha hal hsl hl atr met X₂ Z ω),
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met X₁ X₂ Z
      (nabla_dual emb conn ha hl Y ω),
    ha Y X₁ X₂, A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met X₁ X₂ (conn Y Z) ω]
  rw [rlap_add_pos0 emb conn ha hl hal hsl atr met X₁ X₂ Y Z ω]
  ring

/-- Q_hamilton_scalar is R-homogeneous in X. -/
theorem Q_hamilton_smul_X
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met (c • X) Y Z ω =
    c * Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω := by
  simp only [Q_hamilton_scalar]
  rw [embed_smul_apply emb c X,
    nabla_dual_smul_X emb conn ha hsl hl c X ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c Y Z _,
    hsl c X Y, A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c _ Z ω,
    hsl c X Z, A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c Y _ ω]
  rw [A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c X Z ω,
    (emb.embed Y).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met X Z ω),
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c X Z
      (nabla_dual emb conn ha hl Y ω),
    hl Y c X,
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met ((emb.embed Y) c) X Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c (conn Y X) Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c X (conn Y Z) ω]
  rw [rlap_smul_pos0 emb conn ha hl hal hsl atr met c X Y Z ω]
  simp only [smul_eq_mul]; ring

/-- Q_hamilton_scalar is additive in Y. -/
theorem Q_hamilton_add_Y
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y₁ Y₂ Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X (Y₁ + Y₂) Z ω =
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y₁ Z ω +
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y₂ Z ω := by
  simp only [Q_hamilton_scalar]
  -- First bracket: split A(Y₁+Y₂,...) first, then use map_add
  rw [A_rf_scalar_add_U emb conn ha hal hsl hl atr met Y₁ Y₂ Z ω,
    (emb.embed X).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met Y₁ Z ω)
      (A_rf_scalar emb conn ha hal hsl hl atr met Y₂ Z ω),
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met Y₁ Y₂ Z
      (nabla_dual emb conn ha hl X ω),
    ha X Y₁ Y₂, A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met Y₁ Y₂ (conn X Z) ω]
  -- Second bracket: rewrite embed(Y₁+Y₂), nabla_dual(Y₁+Y₂), conn(Y₁+Y₂,_)
  rw [embed_add_apply emb Y₁ Y₂,
    nabla_dual_add_X emb conn ha hal hl Y₁ Y₂ ω,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met X Z _ _,
    hal Y₁ Y₂ X, A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    hal Y₁ Y₂ Z, A_rf_scalar_add_W emb conn ha hal hsl hl atr met X _ _ ω]
  rw [rlap_add_pos1 emb conn ha hl hal hsl atr met X Y₁ Y₂ Z ω]
  ring

/-- Q_hamilton_scalar is R-homogeneous in Y. -/
theorem Q_hamilton_smul_Y
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X (c • Y) Z ω =
    c * Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω := by
  simp only [Q_hamilton_scalar]
  rw [A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c Y Z ω,
    (emb.embed X).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met Y Z ω),
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c Y Z
      (nabla_dual emb conn ha hl X ω),
    hl X c Y,
    A_rf_scalar_add_U emb conn ha hal hsl hl atr met _ _ Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met ((emb.embed X) c) Y Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c (conn X Y) Z ω,
    A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c Y (conn X Z) ω]
  rw [embed_smul_apply emb c Y,
    nabla_dual_smul_X emb conn ha hsl hl c Y ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c X Z _,
    hsl c Y X, A_rf_scalar_smul_U emb conn ha hal hsl hl atr met c _ Z ω,
    hsl c Y Z, A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c X _ ω]
  rw [rlap_smul_pos1 emb conn ha hl hal hsl atr met c X Y Z ω]
  simp only [smul_eq_mul]; ring

/-- Q_hamilton_scalar is additive in Z. -/
theorem Q_hamilton_add_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y Z₁ Z₂ : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y (Z₁ + Z₂) ω =
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z₁ ω +
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z₂ ω := by
  simp only [Q_hamilton_scalar]
  -- First bracket: split A(Y,Z₁+Z₂,...) first, then use map_add
  rw [A_rf_scalar_add_W emb conn ha hal hsl hl atr met Y Z₁ Z₂ ω,
    (emb.embed X).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met Y Z₁ ω)
      (A_rf_scalar emb conn ha hal hsl hl atr met Y Z₂ ω),
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met Y Z₁ Z₂
      (nabla_dual emb conn ha hl X ω),
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met (conn X Y) Z₁ Z₂ ω,
    ha X Z₁ Z₂, A_rf_scalar_add_W emb conn ha hal hsl hl atr met Y _ _ ω]
  -- Second bracket: same pattern
  rw [A_rf_scalar_add_W emb conn ha hal hsl hl atr met X Z₁ Z₂ ω,
    (emb.embed Y).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met X Z₁ ω)
      (A_rf_scalar emb conn ha hal hsl hl atr met X Z₂ ω),
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met X Z₁ Z₂
      (nabla_dual emb conn ha hl Y ω),
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met (conn Y X) Z₁ Z₂ ω,
    ha Y Z₁ Z₂, A_rf_scalar_add_W emb conn ha hal hsl hl atr met X _ _ ω]
  rw [rlap_add_pos2 emb conn ha hl hal hsl atr met X Y Z₁ Z₂ ω]
  ring

/-- Q_hamilton_scalar is R-homogeneous in Z. -/
theorem Q_hamilton_smul_Z
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y (c • Z) ω =
    c * Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω := by
  simp only [Q_hamilton_scalar]
  rw [A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c Y Z ω,
    (emb.embed X).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met Y Z ω),
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c Y Z
      (nabla_dual emb conn ha hl X ω),
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c (conn X Y) Z ω,
    hl X c Z,
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met Y _ _ ω,
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met ((emb.embed X) c) Y Z ω,
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c Y (conn X Z) ω]
  rw [A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c X Z ω,
    (emb.embed Y).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met X Z ω),
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c X Z
      (nabla_dual emb conn ha hl Y ω),
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c (conn Y X) Z ω,
    hl Y c Z,
    A_rf_scalar_add_W emb conn ha hal hsl hl atr met X _ _ ω,
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met ((emb.embed Y) c) X Z ω,
    A_rf_scalar_smul_W emb conn ha hal hsl hl atr met c X (conn Y Z) ω]
  rw [rlap_smul_pos2 emb conn ha hl hal hsl atr met c X Y Z ω]
  simp only [smul_eq_mul]; ring

/-- Q_hamilton_scalar is additive in ω. -/
theorem Q_hamilton_add_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (X Y Z : V) (ω₁ ω₂ : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z (ω₁ + ω₂) =
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω₁ +
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω₂ := by
  simp only [Q_hamilton_scalar]
  have h_nd_X : nabla_dual emb conn ha hl X (ω₁ + ω₂) =
      nabla_dual emb conn ha hl X ω₁ + nabla_dual emb conn ha hl X ω₂ :=
    nabla_dual_map_add emb conn ha hl X ω₁ ω₂
  have h_nd_Y : nabla_dual emb conn ha hl Y (ω₁ + ω₂) =
      nabla_dual emb conn ha hl Y ω₁ + nabla_dual emb conn ha hl Y ω₂ :=
    nabla_dual_map_add emb conn ha hl Y ω₁ ω₂
  -- First bracket: split A(Y,Z,ω₁+ω₂) first, then use map_add
  rw [A_rf_scalar_add_omega emb conn ha hal hsl hl atr met Y Z ω₁ ω₂,
    (emb.embed X).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met Y Z ω₁)
      (A_rf_scalar emb conn ha hal hsl hl atr met Y Z ω₂),
    h_nd_X,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met Y Z _ _,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met _ Z _ _,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met Y _ _ _]
  -- Second bracket: same pattern
  rw [A_rf_scalar_add_omega emb conn ha hal hsl hl atr met X Z ω₁ ω₂,
    (emb.embed Y).map_add
      (A_rf_scalar emb conn ha hal hsl hl atr met X Z ω₁)
      (A_rf_scalar emb conn ha hal hsl hl atr met X Z ω₂),
    h_nd_Y,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met X Z _ _,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met _ Z _ _,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met X _ _ _]
  rw [rlap_add_omega emb conn ha hl hal hsl atr met X Y Z ω₁ ω₂]
  ring

/-- Q_hamilton_scalar is R-homogeneous in ω. -/
theorem Q_hamilton_smul_omega
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (c : R) (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z (c • ω) =
    c * Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω := by
  simp only [Q_hamilton_scalar]
  have h_nd_X : ∀ (P : V), nabla_dual emb conn ha hl P (c • ω) =
      (emb.embed P) c • ω + c • nabla_dual emb conn ha hl P ω := by
    intro P; ext Y'
    simp only [nabla_dual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [(emb.embed P).leibniz c (ω Y')]
    simp only [smul_eq_mul]; ring
  rw [A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c Y Z ω,
    (emb.embed X).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met Y Z ω),
    h_nd_X X,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met Y Z _ _,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met ((emb.embed X) c) Y Z ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c Y Z
      (nabla_dual emb conn ha hl X ω),
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c _ Z ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c Y _ ω]
  rw [A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c X Z ω,
    (emb.embed Y).leibniz c (A_rf_scalar emb conn ha hal hsl hl atr met X Z ω),
    h_nd_X Y,
    A_rf_scalar_add_omega emb conn ha hal hsl hl atr met X Z _ _,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met ((emb.embed Y) c) X Z ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c X Z
      (nabla_dual emb conn ha hl Y ω),
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c _ Z ω,
    A_rf_scalar_smul_omega emb conn ha hal hsl hl atr met c X _ ω]
  rw [rlap_smul_omega emb conn ha hl hal hsl atr met c X Y Z ω]
  simp only [smul_eq_mul]; ring

end QHamiltonLinearity

-- ============================================================
-- Section 5: Tensor-Level Q and Evolution with Independent Q
-- ============================================================

section TensorEvolutionHamilton

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable {A : Type*} [CommRing A] [Algebra R A]

-- ============================================================
-- 5.1  Q_rm_independent: TensorData from Q_hamilton_scalar — NO td
-- ============================================================

set_option maxHeartbeats 800000 in
-- Increased heartbeat limit: Hamilton quadratic tensor requires extensive algebraic normalization
/-- The Hamilton quadratic as a `TensorData R V 1 3`.

    Evaluates to `Q_hamilton_scalar` — a purely algebraic expression
    in Rm, Rc, g, ∇, atr.tr, sharp with **no ∂_t, no conn_var, no dt_tensor**.

    Multilinearity is proved DIRECTLY from the linearity of A_rf_scalar
    and Q_hamilton_scalar, WITHOUT any reference to `Q_rm` or time infrastructure.

    The type signature contains NO `td`, NO `TimeDerivativeData`, NO `conn_fam`. -/
noncomputable def Q_rm_independent
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (met : MetricDuality R V) 
    : TensorData R V 1 3 where
  toFun vs :=
    { toFun := fun αs =>
        Q_hamilton_scalar emb conn ha hal hsl hl atr met (vs 0) (vs 1) (vs 2) (αs 0)
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        change _ = _ + _
        simp only [Function.update_self]
        exact Q_hamilton_add_omega emb conn ha hal hsl hl atr met (vs 0) (vs 1) (vs 2) β₁ β₂
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        have hidx : idx = (0 : Fin 1) := Subsingleton.elim _ _; subst hidx
        simp only [Function.update_self, smul_eq_mul]
        exact Q_hamilton_smul_omega emb conn ha hal hsl hl atr met c (vs 0) (vs 1) (vs 2) β }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    fin_cases idx
    · -- idx = 0: X slot
      simp only [Function.update]
      exact Q_hamilton_add_X emb conn ha hal hsl hl atr met v₁ v₂ (vs 1) (vs 2) (αs 0)
    · -- idx = 1: Y slot
      simp only [Function.update]
      exact Q_hamilton_add_Y emb conn ha hal hsl hl atr met (vs 0) v₁ v₂ (vs 2) (αs 0)
    · -- idx = 2: Z slot
      simp only [Function.update]
      exact Q_hamilton_add_Z emb conn ha hal hsl hl atr met (vs 0) (vs 1) v₁ v₂ (αs 0)
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    fin_cases idx
    · simp only [Function.update]
      exact Q_hamilton_smul_X emb conn ha hal hsl hl atr met c v (vs 1) (vs 2) (αs 0)
    · simp only [Function.update]
      exact Q_hamilton_smul_Y emb conn ha hal hsl hl atr met c (vs 0) v (vs 2) (αs 0)
    · simp only [Function.update]
      exact Q_hamilton_smul_Z emb conn ha hal hsl hl atr met c (vs 0) (vs 1) v (αs 0)

-- ============================================================
-- 5.2  Evaluation lemma
-- ============================================================

/-- Q_rm_independent evaluates to Q_hamilton_scalar. -/
theorem Q_rm_independent_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (met : MetricDuality R V) 
    (X Y Z : V) (ω : V →ₗ[R] R) :
    Q_rm_independent emb conn ha hal hsl hl atr met ![X, Y, Z] ![ω] =
    Q_hamilton_scalar emb conn ha hal hsl hl atr met X Y Z ω := rfl

-- ============================================================
-- 5.3  Q_rm_independent = Q_rm (tensor equality)
-- ============================================================

/-- Q_rm_independent equals Q_rm as tensors.
    This is the tensor-level version of Q_rm_eq_hamilton. -/
theorem Q_rm_independent_eq_Q_rm
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t) :
    Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) =
    Q_rm td emb conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf atr (g_fam t) t := by
  ext vs αs
  exact (Q_rm_eq_hamilton emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr h_tf
    h_rf h2 t h_decomp (vs 0) (vs 1) (vs 2) (αs 0)).symm

-- ============================================================
-- 5.4  The Grand Evolution Theorem with Independent Q
-- ============================================================

/-- **Riemann curvature evolution under Ricci flow with independent Q.**

    ∂_t Rm = ΔRm + Q_rm_independent

    where Q_rm_independent evaluates to Q_hamilton_scalar — a purely algebraic
    expression in Rm, Rc, g, ∇, atr.tr, sharp. No time derivatives appear in Q. -/
theorem riemann_tensor_evolution_hamilton
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time)
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time → MetricDuality R V)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (h_rf : IsRicciFlow emb td atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam)
    (h2 : ∀ (a : R), (2 : R) * a = 0 → a = 0)
    
    (t : Time)
    (h_decomp : ∀ (F : Time → V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s)
      (hl_fam s)) =
    rough_laplacian_Rm emb (conn_fam t) (ha_fam t) (hl_fam t) (hal_fam t) (hsl_fam t)
      atr (g_fam t) +
    Q_rm_independent emb (conn_fam t) (ha_fam t) (hal_fam t) (hsl_fam t) (hl_fam t)
      atr (g_fam t) := by
  have h_evol := riemann_tensor_evolution emb td h_st atr conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_tf g_fam (fun s => (h_rf.levi_civita s).1) h_rf h_pr h2 t
  rw [← Q_rm_independent_eq_Q_rm emb td h_st atr g_fam conn_fam ha_fam hal_fam hsl_fam hl_fam
    h_pr h_tf h_rf h2 t h_decomp] at h_evol
  exact h_evol

end TensorEvolutionHamilton
