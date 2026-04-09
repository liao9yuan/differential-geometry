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
