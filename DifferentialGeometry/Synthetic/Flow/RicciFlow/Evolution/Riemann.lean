import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Geometry.Bianchi
import DifferentialGeometry.Synthetic.Geometry.TensorRicciIdentity
import DifferentialGeometry.Synthetic.Analysis.TensorCalculus
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

/-!
# Evolution of the Riemann Curvature Tensor

This file formalizes the first variation (raw time derivative) of the Riemann
curvature endomorphism under a time-evolving family of connections.

The main result is the fundamental variation formula: for time-independent X, Y, Z,
  ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z)
where A(X,Y) = ∂_t(∇_X Y) is the connection variation tensor, and
  (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z).

All calculus axioms (VectorTimeDerivativeRules, ConnectionTimeCalculus) live
in the Algebra/Analysis layer (Time.lean). The conn_var_sub_left identity
is derived as a theorem, not axiomatized.
-/

variable {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [DerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  [VectorTimeDerivativeRules Time R V]
  [ConnectionTimeCalculus Time R V]


-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- Connection variation tensor: A(X,Y) = ∂_t(∇_X Y).
Measures the infinitesimal rate of change of the connection at time t.
This is a vector-valued (1,2)-tensor in the sense that A(X,Y) ∈ V. -/
def conn_var (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y : V) : V :=
  TimeDerivative.partial_t (fun s => (conn_fam s).nabla X Y) t

/-- Covariant derivative of the connection variation tensor:
  (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z).
This is the covariant derivative of the vector-valued (1,2)-tensor A. -/
def nabla_conn_var (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : V :=
  (conn_fam t).nabla X (conn_var conn_fam t Y Z)
  - conn_var conn_fam t ((conn_fam t).nabla X Y) Z
  - conn_var conn_fam t Y ((conn_fam t).nabla X Z)

/-- The Riemann variation tensor: ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z).
Defined abstractly as a vector-valued function combining the covariant
derivatives of the connection variation. -/
def t_rm (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : V :=
  nabla_conn_var conn_fam t X Y Z - nabla_conn_var conn_fam t Y X Z


-- ============================================================
-- Section 2: Derived Lemmas
-- ============================================================

/-- ∇_X(-Y) = -∇_X Y for the first argument. -/
private lemma nabla_neg_left_aux (conn : AbstractAffineConnection R V) (X Z : V) :
    conn.nabla (-X) Z = - conn.nabla X Z := by
  have h1 : conn.nabla ((-1 : R) • X) Z = (-1 : R) • conn.nabla X Z := conn.nabla_smul_left (-1) X Z
  rwa [neg_one_smul, neg_one_smul] at h1

/-- ∇_{X₁-X₂} Y = ∇_{X₁} Y - ∇_{X₂} Y (subtraction in the direction argument). -/
private lemma nabla_sub_left_aux (conn : AbstractAffineConnection R V) (X₁ X₂ Z : V) :
    conn.nabla (X₁ - X₂) Z = conn.nabla X₁ Z - conn.nabla X₂ Z := by
  calc conn.nabla (X₁ - X₂) Z
      = conn.nabla (X₁ + -X₂) Z := by rw [sub_eq_add_neg]
    _ = conn.nabla X₁ Z + conn.nabla (-X₂) Z := conn.nabla_add_left X₁ (-X₂) Z
    _ = conn.nabla X₁ Z + (- conn.nabla X₂ Z) := by rw [nabla_neg_left_aux]
    _ = conn.nabla X₁ Z - conn.nabla X₂ Z := by abel

/-- The connection variation is additive under subtraction in its first argument.
Derived from `nabla_sub_left` and `VectorTimeDerivativeRules.t_sub_V`. -/
theorem conn_var_sub_left (conn_fam : Time → AbstractAffineConnection R V)
    (X₁ X₂ Y : V) (t : Time) :
    conn_var conn_fam t (X₁ - X₂) Y =
    conn_var conn_fam t X₁ Y - conn_var conn_fam t X₂ Y := by
  unfold conn_var
  have h_eq : (fun s => (conn_fam s).nabla (X₁ - X₂) Y) =
    fun s => (conn_fam s).nabla X₁ Y - (conn_fam s).nabla X₂ Y := by
    funext s; exact nabla_sub_left_aux (conn_fam s) X₁ X₂ Y
  rw [h_eq]
  exact VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X₁ Y) (fun s => (conn_fam s).nabla X₂ Y) t


-- ============================================================
-- Section 3: Riemann Variation Theorems
-- ============================================================

variable (conn_fam : Time → AbstractAffineConnection R V)

/-- Raw 5-term expansion of the Riemann curvature variation.

Starting from Rm(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z,
the time derivative splits via the product rule into:
  ∂_t[Rm(X,Y)Z] = ∇_X(A(Y,Z)) + A(X, ∇_Y Z)
                 - ∇_Y(A(X,Z)) - A(Y, ∇_X Z)
                 - A([X,Y], Z)

This is the fundamental first variation before torsion-free simplification. -/
theorem riemann_variation_raw (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  (conn_fam t).nabla X (conn_var conn_fam t Y Z) + conn_var conn_fam t X ((conn_fam t).nabla Y Z)
  - ((conn_fam t).nabla Y (conn_var conn_fam t X Z) + conn_var conn_fam t Y ((conn_fam t).nabla X Z))
  - conn_var conn_fam t (bracket X Y) Z := by
  -- Step 1: Unfold Rm to its three-term definition
  have h_unfold : (fun s => Rm (conn_fam s) X Y Z) =
    fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)
           - (conn_fam s).nabla Y ((conn_fam s).nabla X Z)
           - (conn_fam s).nabla (bracket X Y) Z := rfl
  rw [h_unfold]
  -- Step 2: Split ∂_t over the two subtractions (left-associative: (a-b)-c)
  have hsub1 := VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)
            - (conn_fam s).nabla Y ((conn_fam s).nabla X Z))
    (fun s => (conn_fam s).nabla (bracket X Y) Z) t
  have hsub2 := VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z))
    (fun s => (conn_fam s).nabla Y ((conn_fam s).nabla X Z)) t
  rw [hsub1, hsub2]
  -- Step 3: Apply the atomic connection product rule to the two nested terms
  -- ∂_t[∇_X(∇_Y Z)] = A(X, ∇_Y Z) + ∇_X(A(Y,Z))
  have h1 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)) t =
    conn_var conn_fam t X ((conn_fam t).nabla Y Z) +
    (conn_fam t).nabla X (conn_var conn_fam t Y Z) :=
    ConnectionTimeCalculus.t_conn_apply conn_fam X (fun s => (conn_fam s).nabla Y Z) t
  -- ∂_t[∇_Y(∇_X Z)] = A(Y, ∇_X Z) + ∇_Y(A(X,Z))
  have h2 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla Y ((conn_fam s).nabla X Z)) t =
    conn_var conn_fam t Y ((conn_fam t).nabla X Z) +
    (conn_fam t).nabla Y (conn_var conn_fam t X Z) :=
    ConnectionTimeCalculus.t_conn_apply conn_fam Y (fun s => (conn_fam s).nabla X Z) t
  rw [h1, h2]
  -- Step 4: The bracket term ∂_t[∇_{[X,Y]} Z] is conn_var by definition
  have d3 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla (bracket X Y) Z) t =
    conn_var conn_fam t (bracket X Y) Z := rfl
  rw [d3]
  -- Step 5: All terms now use conn_var and nabla; close by commutativity of addition
  abel

/-- Clean Riemann variation formula for torsion-free connections.

The 5-term raw expansion simplifies to 2 terms via the torsion-free
cancellation A([X,Y], Z) = A(∇_X Y, Z) - A(∇_Y X, Z):

  ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z)

This is the fundamental first variation of the Riemann curvature. -/
theorem riemann_variation [∀ s, TorsionFree (conn_fam s)] (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  nabla_conn_var conn_fam t X Y Z - nabla_conn_var conn_fam t Y X Z := by
  rw [riemann_variation_raw conn_fam X Y Z t]
  -- Step 1: Rewrite A([X,Y], Z) using torsion-free: [X,Y] = ∇_X Y - ∇_Y X
  have h_tf : conn_var conn_fam t (bracket X Y) Z =
    conn_var conn_fam t ((conn_fam t).nabla X Y) Z -
    conn_var conn_fam t ((conn_fam t).nabla Y X) Z := by
    conv_lhs => rw [← TorsionFree.torsion_zero (conn := conn_fam t) X Y]
    exact conn_var_sub_left conn_fam
      ((conn_fam t).nabla X Y) ((conn_fam t).nabla Y X) Z t
  rw [h_tf]
  -- Step 2: Unfold nabla_conn_var and close by additive group normalization
  unfold nabla_conn_var
  abel

/-- The Riemann variation equals the abstract definition `t_rm`. -/
theorem riemann_variation_eq_t_rm [∀ s, TorsionFree (conn_fam s)] (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  t_rm conn_fam t X Y Z := by
  rw [riemann_variation conn_fam X Y Z t]; rfl

/-- Covector evaluation of the Riemann variation: for any covector ω,
  ω(∂_t[Rm(X,Y)Z]) = ω((∇_X A)(Y,Z)) - ω((∇_Y A)(X,Z)). -/
theorem riemann_variation_eval [∀ s, TorsionFree (conn_fam s)]
  (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
  ω (TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t) =
  ω (nabla_conn_var conn_fam t X Y Z) - ω (nabla_conn_var conn_fam t Y X Z) := by
  rw [riemann_variation conn_fam X Y Z t]
  exact ω.map_sub _ _


-- ============================================================
-- Section 4: Lichnerowicz Laplacian & Böhm–Berger Synthesis
-- ============================================================

/-!
## Abstract Quadratic Curvature Tensor Q(Rm)

We define Q(Rm) entirely at the `AbstractTensor` layer as specific contractions
of `tensor_prod Rm_tensor Rm_tensor` and `tensor_prod (raise Rc) Rm_tensor`.
No pointwise indices like R_{ab}R^{aijb} appear.

### Notation
- Rm_tensor : AbstractTensor R V 1 3, the (1,3) Riemann tensor R^i_{jkl}
- rc_tensor : AbstractTensor R V 0 2, the Ricci tensor R_{jk}
- g_inv     : AbstractTensor R V 2 0, the inverse metric g^{pq}

### B tensor construction
B^i_{jkl} = g^{pq} R^i_{pjs} R^s_{qkl}

Built by:
1. Form Rm ⊗ Rm : (2, 6)
2. Internal contraction a₂ with d₁ → (1, 5)
3. Raise covariant index b₁ with metric → (2, 4)
4. Contract raised b₁ with b₂ → (1, 3)
-/

section LichnerowiczSynthesis

variable {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [DerivationRules R V] [LieDerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  [VectorTimeDerivativeRules Time R V]
  [ConnectionTimeCalculus Time R V]

variable (metric : MetricDuality R V)
variable (conn : AbstractAffineConnection R V)
  [AffineTensorCalculus conn] [op : RiemannCurvatureTensorOp conn]
  [TorsionFree conn] [JacobiIdentity V]

/-- The B tensor: a fundamental metric contraction of Rm ⊗ Rm.

B^i_{jkl} = g^{pq} R^i_{pjs} R^s_{qkl}

This is the core building block of the quadratic curvature operator Q(Rm).
Constructed via:
  1. Rm ⊗ Rm : (2, 6) — tensor product of two copies of the Riemann tensor
  2. contract_general (1, 2) : contract the 2nd contra (a₂) with 3rd co (d₁) → (1, 5)
  3. raise_index (0) : raise the 1st covariant index (b₁) via g^{-1} → (2, 4)
  4. contract_general (1, 1) : contract raised b₁ with b₂ → (1, 3) -/
noncomputable def B_rm : AbstractTensor R V 1 3 :=
  let RmRm := TensorAlgebra.tensor_prod (r1 := 1) (s1 := 3) (r2 := 1) (s2 := 3)
    op.Rm_tensor op.Rm_tensor
  let step1 := TensorAlgebra.contract_general (1 : Fin 2) (2 : Fin 6) RmRm
  let step2 := raise_index metric (0 : Fin 5) step1
  TensorAlgebra.contract_general (1 : Fin 2) (1 : Fin 4) step2

/-- The Ricci endomorphism tensor: Rc# = g^{-1} Ric, a (1,1) tensor R^i_j.
Obtained by raising the first index of the Ricci tensor. -/
noncomputable def ricci_endo : AbstractTensor R V 1 1 :=
  raise_index metric (0 : Fin 2) (rc_tensor conn)

/-- Ricci–Riemann contraction on the contravariant output slot.
Rc#(Rm) : R^p_i R^i_{jkl} → (1,3) tensor.
The Ricci endomorphism post-composes with the output of Rm. -/
noncomputable def Rc_compose_Rm : AbstractTensor R V 1 3 :=
  let prod := TensorAlgebra.tensor_prod (r1 := 1) (s1 := 1) (r2 := 1) (s2 := 3)
    (ricci_endo metric conn) op.Rm_tensor
  -- prod : (2, 4) with contra: Rc_raised(0), Rm_contra(1); co: Rc_co(0), Rm_co(1,2,3)
  -- Contract Rm_contra (index 1) with Rc_co (index 0): Σ_i R^p_i R^i_{jkl}
  TensorAlgebra.contract_general (1 : Fin 2) (0 : Fin 4) prod

/-- Ricci–Riemann contraction on the j-th covariant slot.
Rm(·, Rc#(·), ·, ·) : R^i_{p k l} R^p_j → (1,3) tensor.
The Ricci endomorphism acts on the 1st covariant argument of Rm. -/
noncomputable def Rm_Rc_slot1 : AbstractTensor R V 1 3 :=
  let prod := TensorAlgebra.tensor_prod (r1 := 1) (s1 := 3) (r2 := 1) (s2 := 1)
    op.Rm_tensor (ricci_endo metric conn)
  -- prod : (2, 4) with contra: Rm_contra(0), Rc_raised(1); co: Rm_co(0,1,2), Rc_co(3)
  -- Contract Rc_raised (index 1) with Rm_co slot 0 (index 0): Σ_p R^i_{pkl} R^p_j
  TensorAlgebra.contract_general (1 : Fin 2) (0 : Fin 4) prod

/-- The abstract quadratic curvature operator Q(Rm).
Combines symmetric B-tensor terms with Ricci–Riemann corrections:

  Q = 2·(B − swap₂₃(B) + swap₁₂ swap₂₃(B) − swap₁₂(B))
    + Rc_compose_Rm − Rm_Rc_slot1

where swap_{ij} permutes covariant indices i, j of the (1,3) tensor.

In local coordinates this reproduces Hamilton's formula:
  Q^i_{jkl} = 2g^{pq}(R^i_{pjr}R^r_{qkl} − R^i_{pkr}R^r_{qjl}
              + R^i_{plr}R^r_{qjk} − R^i_{pjr}R^r_{qlk})
            + R^i_p R^p_{jkl} − R_{jp}R^{ip}_{kl} -/
noncomputable def Q_rm : AbstractTensor R V 1 3 :=
  let B := B_rm metric conn
  -- B with covariant indices (j,k,l) in positions (0,1,2)
  let B_swap_kl := TensorAlgebra.swap_covariant (1 : Fin 3) (2 : Fin 3) B
  let B_swap_jk := TensorAlgebra.swap_covariant (0 : Fin 3) (1 : Fin 3) B
  let B_swap_jk_kl := TensorAlgebra.swap_covariant (1 : Fin 3) (2 : Fin 3) B_swap_jk
  -- Quadratic Rm part: 2(B - B_kl + B_jk_kl - B_jk)
  let quad := TensorAlgebra.smul 2
    (TensorAlgebra.add
      (TensorAlgebra.add B (TensorAlgebra.smul (-1) B_swap_kl))
      (TensorAlgebra.add B_swap_jk_kl (TensorAlgebra.smul (-1) B_swap_jk)))
  -- Ricci correction: Rc#∘Rm - Rm∘Rc#
  let ricci_corr := TensorAlgebra.add
    (Rc_compose_Rm metric conn)
    (TensorAlgebra.smul (-1) (Rm_Rc_slot1 metric conn))
  -- Total Q
  TensorAlgebra.add quad ricci_corr

/-- The rough Laplacian of the Riemann tensor: Δ(Rm) = g^{pq} ∇_p ∇_q Rm.

The abstract framework provides directional covariant derivatives
nabla_tensor conn X T : T^{r,s} → T^{r,s} for fixed direction X.
The "total covariant derivative" ∇ : T^{1,3} → T^{1,4} that increases
tensor rank is obtained by recognizing that X ↦ nabla_tensor conn X T
is C∞-linear in X (by nabla_add_left and nabla_smul_left). The rough
Laplacian traces the double total derivative over the two new covariant
indices using the inverse metric.

This construction requires the total-derivative-as-tensor embedding
T^{r,s} ↪ T^{r,s+1}, which is not yet formalized in the Algebra layer.
The definition is therefore deferred to the Analytic layer, which
verifies it in local coordinates via g^{pq} ∇_p ∇_q R^i_{jkl}. -/
/- The double total derivative ∇∇Rm is a (1,5) tensor (two extra covariant
slots for the two differentiation directions, placed at positions 3 and 4).
metric_trace contracts these two slots, yielding the (1,3) rough Laplacian.

Rank arithmetic:
  Rm_tensor        : (1, 3)
  total_nabla Rm   : (1, 4)     — slot 3 = 1st derivative direction
  total_nabla²Rm   : (1, 5)     — slot 4 = 2nd derivative direction
  metric_trace contracts slots 4 and 3 → (1, 3) -/
noncomputable def rough_laplacian_Rm
    (metric : MetricDuality R V) (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [op : RiemannCurvatureTensorOp conn] : AbstractTensor R V 1 3 :=
  let nabla2Rm := _root_.total_nabla conn (_root_.total_nabla conn op.Rm_tensor)
  -- nabla2Rm : AbstractTensor R V 1 (3 + 1 + 1) = AbstractTensor R V 1 5
  -- metric_trace expects (r, s+2) → (r, s), so s+2 = 5, s = 3
  -- idx1 : Fin (s+2) = Fin 5, choosing slot 4 (2nd derivative direction)
  -- idx2 : Fin (s+1) = Fin 4, choosing slot 3 (1st derivative direction)
  metric_trace metric (⟨4, by omega⟩ : Fin (3 + 2)) (⟨3, by omega⟩ : Fin (3 + 1)) nabla2Rm

/-- The grand synthesis: evolution of the Riemann curvature tensor under Ricci flow.

  ∂_t Rm = Δ(Rm) + Q(Rm)

where Δ is the rough Laplacian g^{pq}∇_p∇_q and Q is the abstract
quadratic curvature operator combining B-tensor and Ricci corrections.

The derivation chains five steps:
  1. Riemann variation formula (riemann_variation):
     ∂_t Rm(X,Y)Z = (∇_X A)(Y,Z) − (∇_Y A)(X,Z)
  2. Connection evolution (connection_evolution):
     g(A(X,Y), Z) = −(∇_X Ric)(Y,Z) − (∇_Y Ric)(X,Z) + (∇_Z Ric)(X,Y)
  3. Tensor Ricci identity (tensor_ricci_identity):
     (R(X,Y) Ric)(U,W) = −Ric(Rm(X,Y)U, W) − Ric(U, Rm(X,Y)W)
     → commutes ∇∇ Ric producing Rm · Ric terms
  4. Second Bianchi identity (second_bianchi):
     (∇_X Rm)(Y,Z) + (∇_Y Rm)(Z,X) + (∇_Z Rm)(X,Y) = 0
     → cyclically rearranges covariant derivatives into Δ Rm
  5. Algebraic collection:
     remaining terms form Q(Rm) = 2(B − swaps) + Rc#∘Rm − Rm∘Rc# -/
theorem riemann_tensor_evolution
    (conn_fam : Time → AbstractAffineConnection R V)
    [∀ s, AffineTensorCalculus (conn_fam s)]
    [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
    [∀ s, TorsionFree (conn_fam s)]
    [JacobiIdentity V]
    (g_fam : Time → MetricDuality R V)
    [MetricTimeDerivativeRules Time R V g_fam]
    [ActionTimeDerivativeRules Time R V]
    [Invertible (2 : R)]
    [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
    [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]
    (t : Time) :
    TensorTimeCalculus.partial_t_tensor (R := R) (V := V) t
      (fun s => (RiemannCurvatureTensorOp.Rm_tensor (conn := conn_fam s))) =
    TensorAlgebra.add
      (rough_laplacian_Rm (g_fam t) (conn_fam t))
      (Q_rm (g_fam t) (conn_fam t)) := by
  sorry

end LichnerowiczSynthesis
