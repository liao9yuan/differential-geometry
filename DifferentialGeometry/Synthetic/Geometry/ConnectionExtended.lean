import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import Mathlib.Tactic.LinearCombination

/-!
# Extended Connection Theorems

Block symmetry, R_XY operator, tensor Ricci identity, scalar curvature,
and Koszul connection construction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open SyntheticTensor

-- ============================================================
-- Metric g helpers
-- ============================================================

section MetricHelpers
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem MetricDuality.g_neg_left (met : MetricDuality R V) (X Y : V) :
    met.g (-X) Y = -met.g X Y := by
  have := met.g_smul_left (-1 : R) X Y; rwa [neg_one_smul, neg_one_mul] at this

theorem MetricDuality.g_neg_right (met : MetricDuality R V) (X Y : V) :
    met.g X (-Y) = -met.g X Y := by
  rw [met.g_symm, met.g_neg_left, met.g_symm]

theorem MetricDuality.g_sub_left (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C := by
  rw [sub_eq_add_neg, met.g_add_left, met.g_neg_left, sub_eq_add_neg]

theorem MetricDuality.g_sub_right (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C := by
  rw [met.g_symm A (B - C), met.g_sub_left, met.g_symm B A, met.g_symm C A]

end MetricHelpers

-- ============================================================
-- Rm_symm_blocks: g(Rm(X,Y)Z, W) = g(Rm(Z,W)X, Y)
-- ============================================================

section RmSymmBlocks
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private theorem metric_bianchi
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_tf : IsTorsionFree emb conn) (A B C D : V) :
    met.g (Rm emb conn A B C) D + met.g (Rm emb conn B C A) D +
    met.g (Rm emb conn C A B) D = 0 := by
  have h := first_bianchi emb conn ha hal h_tf A B C
  have hc : Rm emb conn C A B = -(Rm emb conn A B C + Rm emb conn B C A) :=
    eq_neg_of_add_eq_zero_right h
  rw [hc, met.g_neg_left, met.g_add_left]; ring

/-- Block symmetry: g(Rm(X,Y)Z, W) = g(Rm(Z,W)X, Y). Needs char ≠ 2. -/
theorem Rm_symm_blocks
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (X Y Z W : V) :
    met.g (Rm emb conn X Y Z) W = met.g (Rm emb conn Z W X) Y := by
  have mb := metric_bianchi emb conn ha hal met h_tf
  have anti34 := Rm_metric_antisymm emb conn met h_mc
  have anti_comb : ∀ A B C D,
      met.g (Rm emb conn A B C) D = met.g (Rm emb conn B A D) C := by
    intro A B C D
    rw [Rm_antisymm emb conn hal A B C, met.g_neg_left, anti34 B A C D]; ring
  have b1 := mb X Y Z W
  have b2 := mb Y Z W X
  have b3 := mb Z W X Y
  have b4 := mb W X Y Z
  rw [anti_comb Z X Y W] at b1
  rw [anti34 Y Z W X, anti34 Z W Y X, anti_comb W Y Z X] at b2
  rw [anti34 W X Y Z, anti34 X Y W Z] at b4
  suffices h : met.g (Rm emb conn X Y Z) W - met.g (Rm emb conn Z W X) Y = 0 from
    sub_eq_zero.mp h
  apply char_ne_2_of_invertible_two
  linear_combination b1 + b2 - b3 - b4

end RmSymmBlocks

-- ============================================================
-- R_XY: curvature derivation on tensors
-- ============================================================

section RXY
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Curvature derivation R(X,Y) acting on tensors. -/
noncomputable def R_XY (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s :=
  nabla_tensor emb conn ha hl X (nabla_tensor emb conn ha hl Y T)
  - nabla_tensor emb conn ha hl Y (nabla_tensor emb conn ha hl X T)
  - nabla_tensor emb conn ha hl (bracket emb X Y) T

/-- Pointwise evaluation of R_XY. -/
theorem R_XY_eval (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    R_XY emb conn ha hl X Y T vs αs =
    nabla_tensor emb conn ha hl X (nabla_tensor emb conn ha hl Y T) vs αs -
    nabla_tensor emb conn ha hl Y (nabla_tensor emb conn ha hl X T) vs αs -
    nabla_tensor emb conn ha hl (bracket emb X Y) T vs αs := rfl

/-- R(X,Y) vanishes on scalars. -/
theorem R_XY_scalar (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) (f : R) :
    R_XY emb conn ha hl X Y (scalarToData f) ![] ![] = 0 := by
  rw [R_XY_eval, nabla_scalar, nabla_scalar, nabla_scalar, nabla_scalar, nabla_scalar]
  have sf : (scalarToData (R := R) (V := V) f) ![] ![] = f := by
    simp [scalarToData, MultilinearMap.constOfIsEmpty]
  rw [sf, show (emb.embed (bracket emb X Y)) f =
      (emb.embed X) ((emb.embed Y) f) - (emb.embed Y) ((emb.embed X) f) from
      action_bracket emb X Y f]; ring

/-- R(X,Y) on vectors equals Rm. -/
theorem R_XY_vector (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y U : V) :
    R_XY emb conn ha hl X Y (vectorToData (R := R) U) =
    vectorToData (R := R) (Rm emb conn X Y U) := by
  ext vs αs; simp only [R_XY, Rm]
  rw [nabla_vector, nabla_vector, nabla_vector, nabla_vector, nabla_vector]
  simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.sub_apply]

end RXY

-- ============================================================
-- Tensor Ricci identity for (0,2)-tensors
-- ============================================================

section TensorRicci02
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Evaluation formula for ∇ on (0,2)-tensors. -/
theorem nabla_02_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (U W : V) :
    nabla_tensor emb conn ha hl X T ![U, W] ![] =
    (emb.embed X) (T ![U, W] ![]) - T ![conn X U, W] ![] - T ![U, conn X W] ![] := by
  rw [nabla_tensor_eval]
  simp only [Finset.sum_of_isEmpty (s := Finset.univ (α := Fin 0)), sub_zero]
  rw [Fin.sum_univ_two]
  have hu0 : ∀ v, Function.update (![U, W] : Fin 2 → V) 0 v = ![v, W] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  have hu1 : ∀ v, Function.update (![U, W] : Fin 2 → V) 1 v = ![U, v] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [hu0, hu1, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- Tensor Ricci identity for (0,2)-tensors:
    (R(X,Y)T)(U, W) = -T(Rm(X,Y)U, W) - T(U, Rm(X,Y)W). -/
theorem tensor_ricci_identity_02
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (h_tf : IsTorsionFree emb conn)
    (X Y U W : V) (T : TensorData R V 0 2) :
    R_XY emb conn ha hl X Y T ![U, W] ![] =
    -T ![Rm emb conn X Y U, W] ![] - T ![U, Rm emb conn X Y W] ![] := by
  rw [R_XY_eval]
  -- Expand all ∇ evaluations
  rw [nabla_02_eval emb conn ha hl X (nabla_tensor emb conn ha hl Y T) U W,
      nabla_02_eval emb conn ha hl Y T U W,
      nabla_02_eval emb conn ha hl Y T (conn X U) W,
      nabla_02_eval emb conn ha hl Y T U (conn X W),
      nabla_02_eval emb conn ha hl Y (nabla_tensor emb conn ha hl X T) U W,
      nabla_02_eval emb conn ha hl X T U W,
      nabla_02_eval emb conn ha hl X T (conn Y U) W,
      nabla_02_eval emb conn ha hl X T U (conn Y W),
      nabla_02_eval emb conn ha hl (bracket emb X Y) T U W]
  rw [show (emb.embed (bracket emb X Y)) (T ![U, W] ![]) =
      (emb.embed X) ((emb.embed Y) (T ![U, W] ![])) -
      (emb.embed Y) ((emb.embed X) (T ![U, W] ![])) from
      action_bracket emb X Y (T ![U, W] ![])]
  -- Use torsion-free: conn(bracket X Y) = conn(conn X Y - conn Y X)
  have h_br : ∀ A, conn (bracket emb X Y) A = conn (conn X Y) A - conn (conn Y X) A := by
    intro A; rw [← h_tf X Y, conn_sub_left conn hal]
  rw [h_br U, h_br W]
  -- T multilinear: T ![a - b, c] ![] = T ![a, c] ![] - T ![b, c] ![]
  have Tsub0 : ∀ a b c, T ![a - b, c] ![] = T ![a, c] ![] - T ![b, c] ![] := by
    intro a b c
    have hu : ∀ v, Function.update (![b, c] : Fin 2 → V) 0 v = ![v, c] := by
      intro v; ext i; fin_cases i <;> simp [Function.update]
    have h1 := congr_arg (· ![]) (T.map_update_add ![b, c] 0 (a - b) b)
    simp only [hu, show a - b + b = a from sub_add_cancel a b, MultilinearMap.add_apply] at h1
    exact eq_sub_of_add_eq h1.symm
  have Tsub1 : ∀ a b c, T ![a, b - c] ![] = T ![a, b] ![] - T ![a, c] ![] := by
    intro a b c
    have hu : ∀ v, Function.update (![a, c] : Fin 2 → V) 1 v = ![a, v] := by
      intro v; ext i; fin_cases i <;> simp [Function.update]
    have h1 := congr_arg (· ![]) (T.map_update_add ![a, c] 1 (b - c) c)
    simp only [hu, show b - c + c = b from sub_add_cancel b c, MultilinearMap.add_apply] at h1
    exact eq_sub_of_add_eq h1.symm
  -- Distribute embed through subtractions, then use Tsub0/Tsub1
  simp only [map_sub] at *
  simp only [Tsub0, Tsub1]; unfold Rm; simp only [h_br, Tsub0, Tsub1]; ring

end TensorRicci02

-- ============================================================
-- Scalar curvature and Ricci form
-- ============================================================

section ScalarRicci
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Covector Z ↦ Rc(X, Z) for fixed X. R-linear since Rm is R-linear in Z. -/
noncomputable def RcCovector
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X : V) : V →ₗ[R] R where
  toFun Z := Rc emb conn ha hal hsl hl atr X Z
  map_add' Z₁ Z₂ := by
    simp only [Rc]
    rw [show RcEndo emb conn ha hal hsl hl X (Z₁ + Z₂) =
        RcEndo emb conn ha hal hsl hl X Z₁ + RcEndo emb conn ha hal hsl hl X Z₂ from
      LinearMap.ext (fun Y => Rm_add_Z emb conn ha hal Y X Z₁ Z₂)]
    exact map_add atr.tr _ _
  map_smul' f Z := by
    simp only [Rc, RingHom.id_apply, smul_eq_mul]
    rw [show RcEndo emb conn ha hal hsl hl X (f • Z) =
        f • RcEndo emb conn ha hal hsl hl X Z from
      LinearMap.ext (fun Y => Rm_smul_Z emb conn ha hsl hl f Y X Z)]
    exact atr.tr.map_smul f _

/-- Ricci endomorphism Rc♯: the unique L : V →ₗ[R] V such that
    g(L(X), Z) = Rc(X, Z) for all X, Z.
    Defined as X ↦ sharp(Z ↦ Rc(X, Z)). -/
noncomputable def RicciEndomorphism
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : V →ₗ[R] V where
  toFun X := met.sharp (RcCovector emb conn ha hal hsl hl atr X)
  map_add' X₁ X₂ := by
    have h : RcCovector emb conn ha hal hsl hl atr (X₁ + X₂) =
        RcCovector emb conn ha hal hsl hl atr X₁ +
        RcCovector emb conn ha hal hsl hl atr X₂ := by
      apply LinearMap.ext; intro Z
      simp only [RcCovector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Rc]
      rw [show RcEndo emb conn ha hal hsl hl (X₁ + X₂) Z =
          RcEndo emb conn ha hal hsl hl X₁ Z + RcEndo emb conn ha hal hsl hl X₂ Z from
        LinearMap.ext (fun Y => Rm_add_Y emb conn ha hal Y X₁ X₂ Z)]
      exact map_add atr.tr _ _
    rw [h, met.sharp_add]
  map_smul' f X := by
    have h : RcCovector emb conn ha hal hsl hl atr (f • X) =
        f • RcCovector emb conn ha hal hsl hl atr X := by
      apply LinearMap.ext; intro Z
      simp only [RcCovector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        smul_eq_mul, Rc]
      rw [show RcEndo emb conn ha hal hsl hl (f • X) Z =
          f • RcEndo emb conn ha hal hsl hl X Z from
        LinearMap.ext (fun Y => Rm_smul_Y emb conn hal hsl hl f Y X Z)]
      exact atr.tr.map_smul f _
    simp only [RingHom.id_apply]; rw [h, met.sharp_smul]

/-- g(RicciEndomorphism(X), Z) = Rc(X, Z). -/
theorem RicciEndomorphism_spec
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X Z : V) :
    met.g (RicciEndomorphism emb conn ha hal hsl hl atr met X) Z =
    Rc emb conn ha hal hsl hl atr X Z := by
  simp only [RicciEndomorphism, LinearMap.coe_mk, AddHom.coe_mk]
  exact met.g_sharp (RcCovector emb conn ha hal hsl hl atr X) Z

/-- Scalar curvature: R = tr(Rc♯) = atr.tr(RicciEndomorphism).
    This is the metric trace of the Ricci tensor: R = g^{ij} Rc_{ij}. -/
noncomputable def ScalarCurvature
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : R :=
  atr.tr (RicciEndomorphism emb conn ha hal hsl hl atr met)

end ScalarRicci

-- ============================================================
-- Covariant derivative of Ricci, gradient of scalar curvature
-- ============================================================

section CovDerivDefs
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Covariant derivative of Ricci tensor (scalar level):
    (∇_Y Ric)(Z, X) = Y(Rc(Z,X)) - Rc(conn Y Z, X) - Rc(Z, conn Y X). -/
noncomputable def covDerivRc
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (Y Z X : V) : R :=
  (emb.embed Y) (Rc emb conn ha hal hsl hl atr Z X) -
  Rc emb conn ha hal hsl hl atr (conn Y Z) X -
  Rc emb conn ha hal hsl hl atr Z (conn Y X)

/-- Gradient of scalar curvature: X(R). -/
noncomputable def grad_R
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (X : V) : R :=
  (emb.embed X) (ScalarCurvature emb conn ha hal hsl hl atr met)

end CovDerivDefs

-- ============================================================
-- Koszul connection construction
-- ============================================================

section KoszulConnection
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- RHS of the Koszul formula. -/
noncomputable def koszul_rhs (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (X Y Z : V) : R :=
  (emb.embed X) (met.g Y Z) + (emb.embed Y) (met.g Z X) - (emb.embed Z) (met.g X Y)
  - met.g X (bracket emb Y Z) + met.g Y (bracket emb Z X) + met.g Z (bracket emb X Y)

/-- K(A,B,C) + K(A,C,B) = 2*A(g(B,C)). -/
private theorem koszul_compat_key (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (A B C : V) :
    koszul_rhs emb met A B C + koszul_rhs emb met A C B =
    2 * (emb.embed A) (met.g B C) := by
  simp only [koszul_rhs]
  rw [met.g_symm C B, met.g_symm B A, met.g_symm A C,
      bracket_antisymm emb C B, bracket_antisymm emb B A, bracket_antisymm emb A C]
  simp only [MetricDuality.g_neg_right]; ring

/-- K(A,B,C) - K(B,A,C) = 2*g(C,[A,B]). -/
private theorem koszul_torsion_key (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (A B C : V) :
    koszul_rhs emb met A B C - koszul_rhs emb met B A C =
    2 * met.g C (bracket emb A B) := by
  simp only [koszul_rhs]
  rw [met.g_symm A C, met.g_symm C B, met.g_symm B A,
      bracket_antisymm emb A C, bracket_antisymm emb C B, bracket_antisymm emb B A]
  simp only [MetricDuality.g_neg_right]; ring

/-- The Koszul RHS is R-linear in Z, defining a covector. -/
noncomputable def koszul_covector (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) (X Y : V) : V →ₗ[R] R where
  toFun Z := koszul_rhs emb met X Y Z
  map_add' := fun Z₁ Z₂ => by
    simp only [koszul_rhs]
    rw [show (emb.embed (Z₁ + Z₂)) (met.g X Y) =
        (emb.embed Z₁) (met.g X Y) + (emb.embed Z₂) (met.g X Y) from by
      rw [map_add, Derivation.add_apply]]
    rw [met.g_add_right Y Z₁ Z₂, (emb.embed X).map_add,
        met.g_add_left Z₁ Z₂ X, (emb.embed Y).map_add,
        bracket_add_right emb Y Z₁ Z₂, met.g_add_right X,
        bracket_add_left emb Z₁ Z₂ X, met.g_add_right Y,
        met.g_add_left Z₁ Z₂]
    ring
  map_smul' := fun c Z => by
    simp only [koszul_rhs, RingHom.id_apply, smul_eq_mul]
    -- embed(c•Z) linearity
    rw [show (emb.embed (c • Z)) (met.g X Y) = c * (emb.embed Z) (met.g X Y) from by
      rw [map_smul, Derivation.smul_apply, smul_eq_mul]]
    -- g(Y, c•Z) and g(c•Z, X) before Leibniz
    rw [met.g_smul_right c Y Z, met.g_smul_left c Z X]
    -- Leibniz for X and Y acting on c*scalar
    rw [show (emb.embed X) (c * met.g Y Z) =
        c * (emb.embed X) (met.g Y Z) + met.g Y Z * (emb.embed X) c from by
      have := (emb.embed X).leibniz c (met.g Y Z); simp only [smul_eq_mul] at this; exact this]
    rw [show (emb.embed Y) (c * met.g Z X) =
        c * (emb.embed Y) (met.g Z X) + met.g Z X * (emb.embed Y) c from by
      have := (emb.embed Y).leibniz c (met.g Z X); simp only [smul_eq_mul] at this; exact this]
    -- bracket expansions
    rw [bracket_smul_right emb c Y Z, bracket_smul_left emb c Z X,
        show action emb X c = (emb.embed X) c from rfl,
        show action emb Y c = (emb.embed Y) c from rfl,
        met.g_smul_left c Z (bracket emb X Y)]
    -- Expand g(X, a + b), g(Y, a - b), g(c•v, w)
    simp only [MetricDuality.g_add_right, MetricDuality.g_sub_right,
               MetricDuality.g_smul_right]
    rw [met.g_symm Z X]; ring

/-- Levi-Civita connection via Koszul formula. -/
noncomputable def koszul_connection (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] (X Y : V) : V :=
  met.sharp (⅟(2 : R) • koszul_covector emb met X Y)

/-- 2 * g(koszul X Y, Z) = koszul_rhs(X, Y, Z). -/
theorem koszul_connection_spec (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] (X Y Z : V) :
    2 * met.g (koszul_connection emb met X Y) Z =
    koszul_rhs emb met X Y Z := by
  simp only [koszul_connection]
  rw [met.g_sharp, LinearMap.smul_apply, smul_eq_mul]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self (2 : R)
  rw [show (2 : R) * (⅟(2 : R) * (koszul_covector emb met X Y) Z) =
      ((2 : R) * ⅟(2 : R)) * (koszul_covector emb met X Y) Z from by ring, h2, one_mul]; rfl

/-- The Koszul connection is torsion-free. -/
theorem koszul_torsion_free (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsTorsionFree emb (koszul_connection emb met) := by
  intro X Y
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (koszul_connection emb met X Y -
    koszul_connection emb met Y X) Z = met.g (bracket emb X Y) Z
  rw [met.g_sub_left]
  suffices hsuff : met.g (koszul_connection emb met X Y) Z -
      met.g (koszul_connection emb met Y X) Z -
      met.g (bracket emb X Y) Z = 0 from sub_eq_zero.mp hsuff
  apply char_ne_2_of_invertible_two
  have spec1 := koszul_connection_spec emb met X Y Z
  have spec2 := koszul_connection_spec emb met Y X Z
  calc 2 * (met.g (koszul_connection emb met X Y) Z -
        met.g (koszul_connection emb met Y X) Z -
        met.g (bracket emb X Y) Z)
    = (2 * met.g (koszul_connection emb met X Y) Z -
       2 * met.g (koszul_connection emb met Y X) Z) -
       2 * met.g (bracket emb X Y) Z := by ring
    _ = (koszul_rhs emb met X Y Z - koszul_rhs emb met Y X Z) -
       2 * met.g (bracket emb X Y) Z := by rw [spec1, spec2]
    _ = 2 * met.g Z (bracket emb X Y) -
       2 * met.g (bracket emb X Y) Z := by rw [koszul_torsion_key]
    _ = 0 := by rw [met.g_symm Z (bracket emb X Y)]; ring

/-- The Koszul connection is metric-compatible. -/
theorem koszul_metric_compat (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsMetricCompatible emb (koszul_connection emb met) met := by
  intro X Y Z
  suffices hsuff : (emb.embed X) (met.g Y Z) -
      (met.g (koszul_connection emb met X Y) Z +
       met.g Y (koszul_connection emb met X Z)) = 0 from
    eq_of_sub_eq_zero hsuff
  apply char_ne_2_of_invertible_two
  rw [met.g_symm Y (koszul_connection emb met X Z)]
  have spec1 := koszul_connection_spec emb met X Y Z
  have spec2 := koszul_connection_spec emb met X Z Y
  calc 2 * ((emb.embed X) (met.g Y Z) -
      (met.g (koszul_connection emb met X Y) Z +
       met.g (koszul_connection emb met X Z) Y))
    = 2 * (emb.embed X) (met.g Y Z) -
      (2 * met.g (koszul_connection emb met X Y) Z +
       2 * met.g (koszul_connection emb met X Z) Y) := by ring
    _ = 2 * (emb.embed X) (met.g Y Z) -
      (koszul_rhs emb met X Y Z + koszul_rhs emb met X Z Y) := by rw [spec1, spec2]
    _ = 2 * (emb.embed X) (met.g Y Z) -
      2 * (emb.embed X) (met.g Y Z) := by rw [koszul_compat_key]
    _ = 0 := by ring

/-- Levi-Civita existence. -/
theorem levi_civita_exists (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    [Invertible (2 : R)] :
    IsLeviCivita emb (koszul_connection emb met) met :=
  ⟨koszul_metric_compat emb met,
   koszul_torsion_free emb met⟩

/-- Levi-Civita uniqueness. -/
theorem levi_civita_unique (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    [Invertible (2 : R)]
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) (X Y : V) :
    conn X Y = koszul_connection emb met X Y := by
  apply met.eq_of_forall_g_eq; intro Z
  suffices hsuff : met.g (conn X Y) Z - met.g (koszul_connection emb met X Y) Z = 0 from
    eq_of_sub_eq_zero hsuff
  apply char_ne_2_of_invertible_two
  have spec := koszul_connection_spec emb met X Y Z
  have koszul := levi_civita_uniqueness emb conn ha hal hl met h_mc h_tf X Y Z
  simp only [koszul_rhs] at spec
  linear_combination koszul - spec

/-- Right additivity: ∇_X (Y₁ + Y₂) = ∇_X Y₁ + ∇_X Y₂. -/
theorem koszul_connection_add_right (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X Y₁ Y₂ : V) :
    koszul_connection emb met X (Y₁ + Y₂) =
    koszul_connection emb met X Y₁ + koszul_connection emb met X Y₂ := by
  have hcov : koszul_covector emb met X (Y₁ + Y₂) =
      koszul_covector emb met X Y₁ + koszul_covector emb met X Y₂ := by
    ext Z
    simp only [koszul_covector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
               koszul_rhs]
    rw [met.g_add_left Y₁ Y₂ Z, (emb.embed X).map_add,
        show (emb.embed (Y₁ + Y₂)) (met.g Z X) =
          (emb.embed Y₁) (met.g Z X) + (emb.embed Y₂) (met.g Z X) from by
          rw [map_add, Derivation.add_apply],
        met.g_add_left Y₁ Y₂ (bracket emb Z X),
        met.g_add_right X Y₁ Y₂,
        (emb.embed Z).map_add (met.g X Y₁) (met.g X Y₂),
        bracket_add_left emb Y₁ Y₂ Z,
        met.g_add_right X (bracket emb Y₁ Z) (bracket emb Y₂ Z),
        bracket_add_right emb X Y₁ Y₂,
        met.g_add_right Z (bracket emb X Y₁) (bracket emb X Y₂)]
    ring
  simp only [koszul_connection]
  rw [hcov, smul_add, met.sharp_add]

/-- Left additivity: ∇_{X₁+X₂} Z = ∇_{X₁} Z + ∇_{X₂} Z. -/
theorem koszul_connection_add_left (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X₁ X₂ Z : V) :
    koszul_connection emb met (X₁ + X₂) Z =
    koszul_connection emb met X₁ Z + koszul_connection emb met X₂ Z := by
  have hcov : koszul_covector emb met (X₁ + X₂) Z =
      koszul_covector emb met X₁ Z + koszul_covector emb met X₂ Z := by
    ext W
    simp only [koszul_covector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
               koszul_rhs]
    rw [show (emb.embed (X₁ + X₂)) (met.g Z W) =
          (emb.embed X₁) (met.g Z W) + (emb.embed X₂) (met.g Z W) from by
          rw [map_add, Derivation.add_apply],
        met.g_add_left X₁ X₂ (bracket emb Z W),
        met.g_add_right W (X₁ : V) (X₂ : V),
        (emb.embed Z).map_add (met.g W X₁) (met.g W X₂),
        met.g_add_left X₁ X₂ Z,
        (emb.embed W).map_add (met.g X₁ Z) (met.g X₂ Z),
        bracket_add_right emb W X₁ X₂,
        met.g_add_right Z (bracket emb W X₁) (bracket emb W X₂),
        bracket_add_left emb X₁ X₂ Z,
        met.g_add_right W (bracket emb X₁ Z) (bracket emb X₂ Z)]
    ring
  simp only [koszul_connection]
  rw [hcov, smul_add, met.sharp_add]

/-- Left scalar multiplication: ∇_{f•X} Z = f • ∇_X Z. -/
theorem koszul_connection_smul_left (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (f : R) (X Z : V) :
    koszul_connection emb met (f • X) Z =
    f • koszul_connection emb met X Z := by
  have hcov : koszul_covector emb met (f • X) Z =
      f • koszul_covector emb met X Z := by
    ext W
    simp only [koszul_covector, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
               smul_eq_mul, koszul_rhs]
    -- embed(f•X)(g Z W) = f * embed(X)(g Z W)
    rw [show (emb.embed (f • X)) (met.g Z W) = f * (emb.embed X) (met.g Z W) from by
        rw [map_smul, Derivation.smul_apply, smul_eq_mul]]
    -- g(f•X, [Z,W]) and g(W, [f•X,Z])
    rw [met.g_smul_left f X (bracket emb Z W)]
    -- bracket(f•X, Z) = f•bracket(X,Z) - Z(f)•X
    rw [bracket_smul_left emb f X Z,
        show action emb Z f = (emb.embed Z) f from rfl]
    -- bracket(W, f•X) = f•bracket(W,X) + W(f)•X
    -- Actually we need bracket(Z, f•X) for the second bracket term: met.g Z (bracket emb (f•X) ... no
    -- koszul_rhs has: embed Z (g (f•X) W) and g Z (bracket emb W (f•X)) and g W (bracket emb (f•X) Z)
    -- Wait, koszul_rhs emb met (f•X) Z W =
    --   embed(f•X)(g Z W) + embed(Z)(g W (f•X)) - embed(W)(g (f•X) Z)
    --   - g(f•X, [Z,W]) + g(Z, [W, f•X]) + g(W, [f•X, Z])
    -- So we need: g(W, (f•X)) = f * g(W, X), g((f•X), Z) = f * g(X, Z)
    rw [met.g_smul_right f W X, met.g_smul_left f X Z]
    -- embed(Z)(f * g W X) = f * embed(Z)(g W X) + g(W,X) * Z(f)
    rw [show (emb.embed Z) (f * met.g W X) =
        f * (emb.embed Z) (met.g W X) + met.g W X * (emb.embed Z) f from by
        have := (emb.embed Z).leibniz f (met.g W X); simp only [smul_eq_mul] at this; exact this]
    -- embed(W)(f * g X Z) = f * embed(W)(g X Z) + g(X,Z) * W(f)
    rw [show (emb.embed W) (f * met.g X Z) =
        f * (emb.embed W) (met.g X Z) + met.g X Z * (emb.embed W) f from by
        have := (emb.embed W).leibniz f (met.g X Z); simp only [smul_eq_mul] at this; exact this]
    -- bracket(W, f•X) = f•bracket(W,X) + W(f)•X
    rw [bracket_smul_right emb f W X,
        show action emb W f = (emb.embed W) f from rfl]
    -- g(Z, f•[W,X] + W(f)•X) and g(W, f•[X,Z] - Z(f)•X)
    rw [met.g_add_right Z (f • bracket emb W X) ((emb.embed W) f • X),
        met.g_smul_right f Z (bracket emb W X),
        met.g_smul_right ((emb.embed W) f) Z X,
        met.g_sub_right W (f • bracket emb X Z) ((emb.embed Z) f • X),
        met.g_smul_right f W (bracket emb X Z),
        met.g_smul_right ((emb.embed Z) f) W X,
        met.g_symm Z X]
    ring
  simp only [koszul_connection]
  rw [hcov, smul_comm, met.sharp_smul]

/-- Leibniz rule: ∇_X (f • Y) = X(f) • Y + f • ∇_X Y. -/
theorem koszul_connection_leibniz (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V) [Invertible (2 : R)]
    (X : V) (f : R) (Y : V) :
    koszul_connection emb met X (f • Y) =
    (emb.embed X) f • Y + f • koszul_connection emb met X Y := by
  apply met.eq_of_forall_g_eq; intro Z
  suffices hsuff : met.g (koszul_connection emb met X (f • Y)) Z -
      met.g ((emb.embed X) f • Y + f • koszul_connection emb met X Y) Z = 0 from
    eq_of_sub_eq_zero hsuff
  apply char_ne_2_of_invertible_two
  rw [met.g_add_left ((emb.embed X) f • Y) (f • koszul_connection emb met X Y) Z,
      met.g_smul_left ((emb.embed X) f) Y Z,
      met.g_smul_left f (koszul_connection emb met X Y) Z]
  have specL := koszul_connection_spec emb met X (f • Y) Z
  have specR := koszul_connection_spec emb met X Y Z
  -- Need: koszul_rhs X (f•Y) Z = 2 * (emb.embed X) f * met.g Y Z + f * koszul_rhs X Y Z
  -- koszul_rhs X (f•Y) Z =
  --   X(g(f•Y,Z)) + (f•Y)(g(Z,X)) - Z(g(X,f•Y))
  --   - g(X,[f•Y,Z]) + g(f•Y,[Z,X]) + g(Z,[X,f•Y])
  suffices hkey : koszul_rhs emb met X (f • Y) Z =
      2 * (emb.embed X) f * met.g Y Z + f * koszul_rhs emb met X Y Z by
    have := calc
      2 * met.g (koszul_connection emb met X (f • Y)) Z -
        2 * ((emb.embed X) f * met.g Y Z + f * met.g (koszul_connection emb met X Y) Z)
        = koszul_rhs emb met X (f • Y) Z -
          (2 * (emb.embed X) f * met.g Y Z + f * (2 * met.g (koszul_connection emb met X Y) Z))
          := by rw [specL]; ring
      _ = koszul_rhs emb met X (f • Y) Z -
          (2 * (emb.embed X) f * met.g Y Z + f * koszul_rhs emb met X Y Z)
          := by rw [specR]
      _ = 0 := by rw [hkey]; ring
    linear_combination this
  simp only [koszul_rhs]
  -- g(f•Y, Z) = f * g(Y, Z)
  rw [met.g_smul_left f Y Z]
  -- X(f * g Y Z) = f * X(g Y Z) + g(Y,Z) * X(f)
  rw [show (emb.embed X) (f * met.g Y Z) =
      f * (emb.embed X) (met.g Y Z) + met.g Y Z * (emb.embed X) f from by
      have := (emb.embed X).leibniz f (met.g Y Z); simp only [smul_eq_mul] at this; exact this]
  -- embed(f•Y)(g Z X) = f * Y(g Z X)
  rw [show (emb.embed (f • Y)) (met.g Z X) = f * (emb.embed Y) (met.g Z X) from by
      rw [map_smul, Derivation.smul_apply, smul_eq_mul]]
  -- g(X, f•Y) = f * g(X, Y)
  rw [met.g_smul_right f X Y]
  -- Z(f * g X Y) = f * Z(g X Y) + g(X,Y) * Z(f)
  rw [show (emb.embed Z) (f * met.g X Y) =
      f * (emb.embed Z) (met.g X Y) + met.g X Y * (emb.embed Z) f from by
      have := (emb.embed Z).leibniz f (met.g X Y); simp only [smul_eq_mul] at this; exact this]
  -- [f•Y, Z] = f•[Y,Z] - Z(f)•Y
  rw [bracket_smul_left emb f Y Z,
      show action emb Z f = (emb.embed Z) f from rfl]
  -- g(X, f•[Y,Z] - Z(f)•Y)
  rw [met.g_sub_right X (f • bracket emb Y Z) ((emb.embed Z) f • Y),
      met.g_smul_right f X (bracket emb Y Z),
      met.g_smul_right ((emb.embed Z) f) X Y]
  -- g(f•Y, [Z,X]) = f * g(Y, [Z,X])
  rw [met.g_smul_left f Y (bracket emb Z X)]
  -- [X, f•Y] = f•[X,Y] + X(f)•Y
  rw [bracket_smul_right emb f X Y,
      show action emb X f = (emb.embed X) f from rfl]
  -- g(Z, f•[X,Y] + X(f)•Y)
  rw [met.g_add_right Z (f • bracket emb X Y) ((emb.embed X) f • Y),
      met.g_smul_right f Z (bracket emb X Y),
      met.g_smul_right ((emb.embed X) f) Z Y,
      met.g_symm Z Y]
  ring

end KoszulConnection

-- ============================================================
-- Contracted Bianchi (vector-level foundation)
-- ============================================================

section ContractedBianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The second Bianchi identity at the vector level (= second_bianchi restated). -/
theorem covDerivRm_sum_endo
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn) (X Y Z W : V) :
    covDerivRm emb conn X Y Z W + covDerivRm emb conn Y Z X W +
    covDerivRm emb conn Z X Y W = 0 :=
  second_bianchi emb conn ha hal h_tf X Y Z W

end ContractedBianchi
