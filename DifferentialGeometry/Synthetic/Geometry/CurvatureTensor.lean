import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Algebra.VectorField
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Curvature Tensor Tensoriality
Proofs of the C-infinity linearity of the Riemann curvature tensor.
-/

open AbstractDerivationAction
open AbstractLieBracket

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V]

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V]


/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its third vector field argument. -/
theorem Rm_smul_Z (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn X Y (f • Z) = f • (Rm conn X Y Z) := by
  -- Proof strategy:
  -- Rm conn X Y (fZ) = nabla X (nabla Y (fZ)) - nabla Y (nabla X (fZ)) - nabla [X,Y] (fZ)
  unfold Rm
  rw [conn.leibniz f Y Z]
  rw [conn.leibniz f X Z]
  rw [conn.leibniz f (bracket X Y) Z]
  rw [conn.nabla_add_right]
  rw [conn.nabla_add_right]
  rw [conn.leibniz (action Y f) X Z]
  rw [conn.leibniz (action X f) Y Z]
  rw [conn.leibniz f X (conn.nabla Y Z)]
  rw [conn.leibniz f Y (conn.nabla X Z)]
  rw [LieDerivationRules.action_bracket X Y f]
  rw [sub_smul]
  rw [smul_sub, smul_sub]
  abel

omit [AbstractLieBracket V] in
lemma nabla_neg_left (conn : AbstractAffineConnection R V) (X Z : V) : conn.nabla (-X) Z = - conn.nabla X Z := by
  have h1 : conn.nabla (X + -X) Z = conn.nabla X Z + conn.nabla (-X) Z := conn.nabla_add_left X (-X) Z
  have h3 : conn.nabla (0 + 0) Z = conn.nabla 0 Z + conn.nabla 0 Z := conn.nabla_add_left 0 0 Z
  have h5 : conn.nabla 0 Z = 0 := by
    calc conn.nabla 0 Z = conn.nabla 0 Z + conn.nabla 0 Z - conn.nabla 0 Z := by abel
      _ = conn.nabla (0 + 0) Z - conn.nabla 0 Z := by rw [← h3]
      _ = conn.nabla 0 Z - conn.nabla 0 Z := by rw [add_zero]
      _ = 0 := by abel
  calc conn.nabla (-X) Z = conn.nabla X Z + conn.nabla (-X) Z - conn.nabla X Z := by abel
    _ = conn.nabla (X + -X) Z - conn.nabla X Z := by rw [← h1]
    _ = conn.nabla 0 Z - conn.nabla X Z := by rw [add_neg_cancel]
    _ = 0 - conn.nabla X Z := by rw [h5]
    _ = - conn.nabla X Z := by abel

omit [AbstractLieBracket V] in
lemma nabla_sub_left (conn : AbstractAffineConnection R V) (A B Z : V) : conn.nabla (A - B) Z = conn.nabla A Z - conn.nabla B Z := by
  calc conn.nabla (A - B) Z = conn.nabla (A + -B) Z := by rw [sub_eq_add_neg]
    _ = conn.nabla A Z + conn.nabla (-B) Z := conn.nabla_add_left A (-B) Z
    _ = conn.nabla A Z + - conn.nabla B Z := by rw [nabla_neg_left]
    _ = conn.nabla A Z - conn.nabla B Z := by rw [sub_eq_add_neg]

/-- Proves that Riemann curvature is additive in the first vector field argument. -/
lemma Rm_add_X (conn : AbstractAffineConnection R V) [DerivationRules R V] (X₁ X₂ Y Z : V) : Rm conn (X₁ + X₂) Y Z = Rm conn X₁ Y Z + Rm conn X₂ Y Z := by
  unfold Rm
  rw [conn.nabla_add_left X₁ X₂ (conn.nabla Y Z)]
  rw [conn.nabla_add_left X₁ X₂ Z]
  rw [DerivationRules.bracket_add_left R X₁ X₂ Y]
  rw [conn.nabla_add_left (bracket X₁ Y) (bracket X₂ Y) Z]
  rw [conn.nabla_add_right Y (conn.nabla X₁ Z) (conn.nabla X₂ Z)]
  abel

/-- Proves that Riemann curvature is additive in the third vector field argument. -/
lemma Rm_add_Z (conn : AbstractAffineConnection R V) (X Y Z₁ Z₂ : V) : Rm conn X Y (Z₁ + Z₂) = Rm conn X Y Z₁ + Rm conn X Y Z₂ := by
  unfold Rm
  rw [conn.nabla_add_right Y Z₁ Z₂]
  rw [conn.nabla_add_right X (conn.nabla Y Z₁) (conn.nabla Y Z₂)]
  rw [conn.nabla_add_right X Z₁ Z₂]
  rw [conn.nabla_add_right Y (conn.nabla X Z₁) (conn.nabla X Z₂)]
  rw [conn.nabla_add_right (bracket X Y) Z₁ Z₂]
  abel

/-- Proves that Riemann curvature is additive in the second vector field argument. -/
lemma Rm_add_Y (conn : AbstractAffineConnection R V) [DerivationRules R V] (X Y₁ Y₂ Z : V) : Rm conn X (Y₁ + Y₂) Z = Rm conn X Y₁ Z + Rm conn X Y₂ Z := by
  unfold Rm
  rw [conn.nabla_add_left Y₁ Y₂ Z]
  rw [conn.nabla_add_right X (conn.nabla Y₁ Z) (conn.nabla Y₂ Z)]
  rw [conn.nabla_add_left Y₁ Y₂ (conn.nabla X Z)]
  rw [DerivationRules.bracket_add_right R X Y₁ Y₂]
  rw [conn.nabla_add_left (bracket X Y₁) (bracket X Y₂) Z]
  abel

/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its second vector field argument. -/
theorem Rm_smul_Y (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn X (f • Y) Z = f • (Rm conn X Y Z) := by
  unfold Rm
  rw [conn.nabla_smul_left f Y Z]
  rw [conn.leibniz f X (conn.nabla Y Z)]
  rw [conn.nabla_smul_left f Y (conn.nabla X Z)]
  rw [DerivationRules.bracket_smul_right f X Y]
  rw [conn.nabla_add_left (f • (bracket X Y)) ((action X f) • Y) Z]
  rw [conn.nabla_smul_left f (bracket X Y) Z]
  rw [conn.nabla_smul_left (action X f) Y Z]
  rw [smul_sub, smul_sub]
  abel



/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its first vector field argument. -/
theorem Rm_smul_X (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn (f • X) Y Z = f • (Rm conn X Y Z) := by
  unfold Rm
  rw [conn.nabla_smul_left f X (conn.nabla Y Z)]
  rw [conn.nabla_smul_left f X Z]
  rw [conn.leibniz f Y (conn.nabla X Z)]
  rw [DerivationRules.bracket_smul_left f X Y]
  rw [nabla_sub_left]
  rw [conn.nabla_smul_left f (bracket X Y) Z]
  rw [conn.nabla_smul_left (action Y f) X Z]
  rw [smul_sub, smul_sub]
  abel

/-- The Riemann curvature endomorphism is skew-symmetric with respect to the metric:
    g(Rm(X,Y)Z, W) = -g(Rm(X,Y)W, Z).
    Proved by double expansion of metric compatibility and the bracket-action identity,
    where cross-terms cancel and remaining terms collect into the Rm definition. -/
lemma Rm_metric_antisymm {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [DifferentialGeometry.TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V]
    [DerivationRules R V] [LieDerivationRules R V]
    (conn : AbstractAffineConnection R V)
    (metric : MetricDuality R V)
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (X Y Z W : V) :
    metric.g (Rm conn X Y Z) W = - metric.g (Rm conn X Y W) Z := by
  -- Abbreviate the underlying AbstractMetricTensor
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor with hm_def
  -- Step 1: Suffices to show g(Rm(X,Y)Z, W) + g(Z, Rm(X,Y)W) = 0
  suffices h : m.g (Rm conn X Y Z) W + m.g Z (Rm conn X Y W) = 0 by
    have hsymm : m.g Z (Rm conn X Y W) = m.g (Rm conn X Y W) Z := m.symm Z (Rm conn X Y W)
    linarith
  -- Step 2: Metric subtraction in the second argument
  have metric_sub_right : ∀ A B C : V, m.g C (A - B) = m.g C A - m.g C B := fun A B C => by
    rw [m.symm C (A - B), metric_sub_left m A B C, m.symm A C, m.symm B C]
  -- Step 3: Metric compatibility — single expansions
  have c1 : action Y (m.g Z W) = m.g (conn.nabla Y Z) W + m.g Z (conn.nabla Y W) :=
    MetricCompatible.compat Y Z W
  have c2 : action X (m.g Z W) = m.g (conn.nabla X Z) W + m.g Z (conn.nabla X W) :=
    MetricCompatible.compat X Z W
  -- Step 4: Metric compatibility — double expansions (X after Y, and Y after X)
  have c3 : action X (m.g (conn.nabla Y Z) W) =
      m.g (conn.nabla X (conn.nabla Y Z)) W + m.g (conn.nabla Y Z) (conn.nabla X W) :=
    MetricCompatible.compat X (conn.nabla Y Z) W
  have c4 : action X (m.g Z (conn.nabla Y W)) =
      m.g (conn.nabla X Z) (conn.nabla Y W) + m.g Z (conn.nabla X (conn.nabla Y W)) :=
    MetricCompatible.compat X Z (conn.nabla Y W)
  have c5 : action Y (m.g (conn.nabla X Z) W) =
      m.g (conn.nabla Y (conn.nabla X Z)) W + m.g (conn.nabla X Z) (conn.nabla Y W) :=
    MetricCompatible.compat Y (conn.nabla X Z) W
  have c6 : action Y (m.g Z (conn.nabla X W)) =
      m.g (conn.nabla Y Z) (conn.nabla X W) + m.g Z (conn.nabla Y (conn.nabla X W)) :=
    MetricCompatible.compat Y Z (conn.nabla X W)
  -- Step 5: Metric compatibility — bracket expansion
  have c7 : action (bracket X Y) (m.g Z W) =
      m.g (conn.nabla (bracket X Y) Z) W + m.g Z (conn.nabla (bracket X Y) W) :=
    MetricCompatible.compat (bracket X Y) Z W
  -- Step 6: Full double expansions via action distributivity + compat
  --   X(Y(g(Z,W))) = g(∇_X∇_YZ, W) + g(∇_YZ, ∇_XW) + g(∇_XZ, ∇_YW) + g(Z, ∇_X∇_YW)
  have hXY : action X (action Y (m.g Z W)) =
      m.g (conn.nabla X (conn.nabla Y Z)) W + m.g (conn.nabla Y Z) (conn.nabla X W) +
      m.g (conn.nabla X Z) (conn.nabla Y W) + m.g Z (conn.nabla X (conn.nabla Y W)) := by
    rw [c1, DerivationRules.action_add_right, c3, c4]; ring
  --   Y(X(g(Z,W))) = g(∇_Y∇_XZ, W) + g(∇_XZ, ∇_YW) + g(∇_YZ, ∇_XW) + g(Z, ∇_Y∇_XW)
  have hYX : action Y (action X (m.g Z W)) =
      m.g (conn.nabla Y (conn.nabla X Z)) W + m.g (conn.nabla X Z) (conn.nabla Y W) +
      m.g (conn.nabla Y Z) (conn.nabla X W) + m.g Z (conn.nabla Y (conn.nabla X W)) := by
    rw [c2, DerivationRules.action_add_right, c5, c6]; ring
  -- Step 7: Bracket-action identity [X,Y](f) = X(Y(f)) - Y(X(f))
  have ba : action (bracket X Y) (m.g Z W) =
      action X (action Y (m.g Z W)) - action Y (action X (m.g Z W)) :=
    LieDerivationRules.action_bracket X Y (m.g Z W)
  -- Step 8: Unfold Rm, distribute metric over subtraction, close by linarith
  --   Cross-terms g(∇_YZ,∇_XW) and g(∇_XZ,∇_YW) cancel in X(Y(g))−Y(X(g)),
  --   and remaining terms regroup into g(Rm(X,Y)Z, W) + g(Z, Rm(X,Y)W) = 0.
  unfold Rm
  rw [metric_sub_left, metric_sub_left, metric_sub_right, metric_sub_right]
  linarith

/-- Antisymmetry of Rm in the first two arguments: `Rm(X,Y)Z = -Rm(Y,X)Z`. -/
private lemma Rm_antisymm_local (conn : AbstractAffineConnection R V) [DerivationRules R V] (X Y Z : V) :
    Rm conn X Y Z = - Rm conn Y X Z := by
  unfold Rm
  rw [DerivationRules.bracket_antisymm R X Y, nabla_neg_left]; abel

/-- `∇_X(0) = 0` from additivity. -/
private lemma nabla_zero_right (conn : AbstractAffineConnection R V) (X : V) :
    conn.nabla X (0 : V) = 0 := by
  have hd : conn.nabla X 0 + conn.nabla X 0 = conn.nabla X 0 := by
    conv_rhs => rw [show (0 : V) = 0 + 0 from (add_zero 0).symm]
    exact (conn.nabla_add_right X 0 0).symm
  exact add_left_cancel (hd.trans (add_zero _).symm)

/-- `∇_X(-Y) = -∇_X Y` for the second argument. -/
private lemma nabla_neg_right_local (conn : AbstractAffineConnection R V) (X Y : V) :
    conn.nabla X (-Y) = - conn.nabla X Y := by
  have h := conn.nabla_add_right X Y (-Y)
  rw [add_neg_cancel, nabla_zero_right] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- First Bianchi Identity: `Rm(X,Y)Z + Rm(Y,Z)X + Rm(Z,X)Y = 0`. -/
private lemma first_bianchi_local
    (conn : AbstractAffineConnection R V) [DerivationRules R V]
    [TorsionFree conn] [JacobiIdentity V] (X Y Z : V) :
    Rm conn X Y Z + Rm conn Y Z X + Rm conn Z X Y = 0 := by
  have torsion : ∀ A B : V, conn.nabla A B - conn.nabla B A = bracket A B :=
    fun A B => TorsionFree.torsion_zero A B
  have nsub : ∀ A B C : V, conn.nabla A (B - C) = conn.nabla A B - conn.nabla A C := by
    intro A B C
    calc conn.nabla A (B - C) = conn.nabla A (B + -C) := by rw [sub_eq_add_neg]
      _ = conn.nabla A B + conn.nabla A (-C) := conn.nabla_add_right A B (-C)
      _ = conn.nabla A B + - conn.nabla A C := by rw [nabla_neg_right_local conn A C]
      _ = conn.nabla A B - conn.nabla A C := by rw [sub_eq_add_neg]
  have regroup : ∀ A B C : V, conn.nabla A (conn.nabla B C) - conn.nabla A (conn.nabla C B) =
      conn.nabla A (bracket B C) := by
    intro A B C; rw [← nsub, torsion]
  unfold Rm
  have r1 := regroup X Y Z; have r2 := regroup Y Z X; have r3 := regroup Z X Y
  have t1 := torsion X (bracket Y Z); have t2 := torsion Y (bracket Z X); have t3 := torsion Z (bracket X Y)
  have jac := JacobiIdentity.jacobi X Y Z
  -- All equalities are in the additive group V — close with abel
  calc conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla (bracket X Y) Z
    + (conn.nabla Y (conn.nabla Z X) - conn.nabla Z (conn.nabla Y X) - conn.nabla (bracket Y Z) X)
    + (conn.nabla Z (conn.nabla X Y) - conn.nabla X (conn.nabla Z Y) - conn.nabla (bracket Z X) Y)
      = (conn.nabla X (conn.nabla Y Z) - conn.nabla X (conn.nabla Z Y))
      + (conn.nabla Y (conn.nabla Z X) - conn.nabla Y (conn.nabla X Z))
      + (conn.nabla Z (conn.nabla X Y) - conn.nabla Z (conn.nabla Y X))
      - conn.nabla (bracket X Y) Z - conn.nabla (bracket Y Z) X - conn.nabla (bracket Z X) Y := by abel
    _ = conn.nabla X (bracket Y Z)
      + conn.nabla Y (bracket Z X)
      + conn.nabla Z (bracket X Y)
      - conn.nabla (bracket X Y) Z - conn.nabla (bracket Y Z) X - conn.nabla (bracket Z X) Y := by rw [r1, r2, r3]
    _ = (conn.nabla X (bracket Y Z) - conn.nabla (bracket Y Z) X)
      + (conn.nabla Y (bracket Z X) - conn.nabla (bracket Z X) Y)
      + (conn.nabla Z (bracket X Y) - conn.nabla (bracket X Y) Z) := by abel
    _ = bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) := by rw [t1, t2, t3]
    _ = 0 := jac

/-- Riemann tensor block symmetry: `g(Rm(X,Y)Z, W) = g(Rm(Z,W)X, Y)`.
    Proved algebraically from the first Bianchi identity and the metric
    antisymmetry of Rm, using four permutations of the metric Bianchi
    identity paired with the two antisymmetries. -/
lemma Rm_symm_blocks {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [DifferentialGeometry.TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V]
    [DerivationRules R V] [LieDerivationRules R V]
    (conn : AbstractAffineConnection R V)
    [TorsionFree conn] [JacobiIdentity V]
    (metric : MetricDuality R V)
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (X Y Z W : V) :
    metric.g (Rm conn X Y Z) W = metric.g (Rm conn Z W X) Y := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  -- g(0, D) = 0
  have g_zero : ∀ D : V, m.g 0 D = 0 := by
    intro D
    have h3 : m.g (0 + 0) D = m.g 0 D + m.g 0 D := m.bilinear_add_left 0 0 D
    rw [add_zero] at h3; linarith
  -- Metric Bianchi: B(A,B,C,D) + B(B,C,A,D) + B(C,A,B,D) = 0
  have bianchi : ∀ A B C D : V, m.g (Rm conn A B C) D + m.g (Rm conn B C A) D + m.g (Rm conn C A B) D = 0 := by
    intro A B C D
    have fb := first_bianchi_local conn A B C
    calc m.g (Rm conn A B C) D + m.g (Rm conn B C A) D + m.g (Rm conn C A B) D
      _ = m.g (Rm conn A B C + Rm conn B C A + Rm conn C A B) D := by
          rw [m.bilinear_add_left, m.bilinear_add_left]
      _ = m.g 0 D := by rw [fb]
      _ = 0 := g_zero D
  -- A2: antisymmetry in 2nd pair
  have a2 : ∀ A B C D : V, m.g (Rm conn A B C) D = - m.g (Rm conn A B D) C :=
    Rm_metric_antisymm conn metric
  -- A1: antisymmetry in 1st pair
  have a1 : ∀ A B C D : V, m.g (Rm conn A B C) D = - m.g (Rm conn B A C) D := by
    intro A B C D
    rw [Rm_antisymm_local conn A B C, metric_neg_left]
  -- Provide Bianchi instances + all antisymmetry instances needed
  have b1 := bianchi X Y Z W
  have b2 := bianchi X Z W Y
  have b3 := bianchi Y W X Z
  have b4 := bianchi Y W Z X
  -- A2 instances
  have h1 := a2 X Y Z W; have h2 := a2 X Y W Z
  have h3 := a2 Y Z X W; have h4 := a2 Y Z W X
  have h5 := a2 Z X Y W; have h6 := a2 Z X W Y
  have h7 := a2 X Z W Y; have h8 := a2 X Z Y W
  have h9 := a2 Z W X Y; have h10 := a2 Z W Y X
  have h11 := a2 Y W X Z; have h12 := a2 Y W Z X
  have h13 := a2 W X Z Y; have h14 := a2 W X Y Z
  -- A1 instances
  have h15 := a1 X Z W Y; have h16 := a1 W X Z Y
  have h17 := a1 W X Y Z; have h18 := a1 W Z Y X
  have h19 := a1 Z Y W X; have h20 := a1 X Y W Z
  have h21 := a1 Y W Z X; have h22 := a1 Y W X Z
  linarith
