import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Metric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Affine and Levi-Civita Connections
Definitions for affine connections, torsion, metric compatibility, and the Levi-Civita theorem.
-/

variable (R V : Type*)
variable [CommRing R] [AddCommGroup V] [Module R V]

variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

open AbstractDerivationAction
open AbstractLieBracket

/-- Affine connection (covariant derivative) on a vector bundle.
Input: (V, V)
Output: V

# Reference:
# Hongxi Wu, An Introduction to Riemannian Geometry. (2014). Higher Education Press.
-/
structure AbstractAffineConnection [AbstractDerivationAction R V] where
  nabla : V → V → V
  nabla_add_left : ∀ X Y Z : V, nabla (X + Y) Z = nabla X Z + nabla Y Z
  nabla_add_right : ∀ X Y Z : V, nabla X (Y + Z) = nabla X Y + nabla X Z
  nabla_smul_left : ∀ (f : R) (X Z : V), nabla (f • X) Z = f • (nabla X Z)
  leibniz : ∀ (f : R) (X Y : V), nabla X (f • Y) = (action X f) • Y + f • (nabla X Y)

-- 2. Local Frames & Christoffel Symbols
variable {I : Type}

structure LocalFrame (I R V : Type*) where
  vec : I → V
  coord : V → I → R

section Symbols

variable {R V} {I : Type*}

/-- Christoffel symbols characterizing the connection in a local frame.
Input: (AbstractAffineConnection R V, LocalFrame I R V, I, I, I)
Output: R
-/
def christoffel_symbol [AbstractDerivationAction R V]
  (conn : AbstractAffineConnection R V) (frame : LocalFrame I R V) (i j k : I) : R :=
  frame.coord (conn.nabla (frame.vec i) (frame.vec j)) k

end Symbols

-- 3. Metric Compatibility & Torsion-Free Conditions
variable {R V}
variable [AbstractDerivationAction R V]

/-- Metric compatibility condition: `X⟨Y, Z⟩ = ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩`.
Input: (AbstractAffineConnection R V, AbstractMetricTensor R V)
Output: Prop -/
class MetricCompatible (conn : AbstractAffineConnection R V) (metric : AbstractMetricTensor R V) where
  compat : ∀ X Y Z : V,
    action X (metric.g Y Z) = metric.g (conn.nabla X Y) Z + metric.g Y (conn.nabla X Z)

/-- Directional derivative of squared norm under metric compatibility: `X⟨Y, Y⟩ = 2⟨∇_X Y, Y⟩`.
Input: (V, V)
Output: Prop -/
theorem norm_sq_deriv (conn : AbstractAffineConnection R V) (metric : AbstractMetricTensor R V) [MetricCompatible conn metric] (X Y : V) :
  action X (metric.g Y Y) = metric.g (conn.nabla X Y) Y + metric.g (conn.nabla X Y) Y := by
  -- Step 1: Expand using metric compatibility: X ⟨Y, Y⟩ = ⟨∇_X Y, Y⟩ + ⟨Y, ∇_X Y⟩
  rw [MetricCompatible.compat (conn := conn) X Y Y]
  -- Step 2: Use the symmetry of the metric tensor: ⟨Y, ∇_X Y⟩ = ⟨∇_X Y, Y⟩
  rw [metric.symm Y (conn.nabla X Y)]

/-- Torsion-free condition: `∇_X Y - ∇_Y X = [X, Y]`.
Input: (AbstractAffineConnection R V)
Output: Prop -/
class TorsionFree (conn : AbstractAffineConnection R V) [AbstractLieBracket V] where
  torsion_zero : ∀ X Y : V, conn.nabla X Y - conn.nabla Y X = bracket X Y

/-- Koszul formula deriving the unique Levi-Civita connection.
Input: (AbstractAffineConnection R V, AbstractMetricTensor R V, V, V, V)
Output: Prop

# Reference:
# Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
-/
theorem levi_civita_uniqueness [AbstractLieBracket V]
  (conn : AbstractAffineConnection R V) (metric : AbstractMetricTensor R V)
  [MetricCompatible conn metric] [TorsionFree conn] (X Y Z : V) :
  2 * metric.g (conn.nabla X Y) Z =
    action X (metric.g Y Z) + action Y (metric.g X Z) - action Z (metric.g X Y)
    - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y) := by
  have a2 : action Y (metric.g X Z) = action Y (metric.g Z X) := congrArg (action Y) (metric.symm X Z)
  have eq1 : action X (metric.g Y Z) = metric.g (conn.nabla X Y) Z + metric.g (conn.nabla X Z) Y := by
    rw [MetricCompatible.compat (conn := conn) X Y Z, metric.symm Y (conn.nabla X Z)]
  have eq2 : action Y (metric.g X Z) = metric.g (conn.nabla Y Z) X + metric.g (conn.nabla Y X) Z := by
    rw [a2, MetricCompatible.compat (conn := conn) Y Z X, metric.symm Z (conn.nabla Y X)]
  have eq3 : action Z (metric.g X Y) = metric.g (conn.nabla Z X) Y + metric.g (conn.nabla Z Y) X := by
    rw [MetricCompatible.compat (conn := conn) Z X Y, metric.symm X (conn.nabla Z Y)]
  have t1 : conn.nabla X Y = conn.nabla Y X + bracket X Y := by
    calc conn.nabla X Y = conn.nabla X Y - conn.nabla Y X + conn.nabla Y X := by abel
      _ = bracket X Y + conn.nabla Y X := by rw [TorsionFree.torsion_zero (conn := conn)]
      _ = conn.nabla Y X + bracket X Y := by abel
  have t2 : conn.nabla Z X = conn.nabla X Z + bracket Z X := by
    calc conn.nabla Z X = conn.nabla Z X - conn.nabla X Z + conn.nabla X Z := by abel
      _ = bracket Z X + conn.nabla X Z := by rw [TorsionFree.torsion_zero (conn := conn)]
      _ = conn.nabla X Z + bracket Z X := by abel
  have t3 : conn.nabla Y Z = conn.nabla Z Y + bracket Y Z := by
    calc conn.nabla Y Z = conn.nabla Y Z - conn.nabla Z Y + conn.nabla Z Y := by abel
      _ = bracket Y Z + conn.nabla Z Y := by rw [TorsionFree.torsion_zero (conn := conn)]
      _ = conn.nabla Z Y + bracket Y Z := by abel
  have g1 : metric.g (conn.nabla X Y) Z = metric.g (conn.nabla Y X) Z + metric.g (bracket X Y) Z := by
    rw [t1, metric.bilinear_add_left]
  have g2 : metric.g (conn.nabla Z X) Y = metric.g (conn.nabla X Z) Y + metric.g (bracket Z X) Y := by
    rw [t2, metric.bilinear_add_left]
  have g3 : metric.g (conn.nabla Y Z) X = metric.g (conn.nabla Z Y) X + metric.g (bracket Y Z) X := by
    rw [t3, metric.bilinear_add_left]
  have s1 : metric.g X (bracket Y Z) = metric.g (bracket Y Z) X := metric.symm _ _
  have s2 : metric.g Y (bracket Z X) = metric.g (bracket Z X) Y := metric.symm _ _
  have s3 : metric.g Z (bracket X Y) = metric.g (bracket X Y) Z := metric.symm _ _
  rw [eq1, eq2, eq3, g1, g2, g3, s1, s2, s3]
  ring

/-- Leibniz rule and Jacobi identity for derivation action and Lie bracket.
Input: (R, V)
Output: Type -/
class DerivationRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  action_add_left : ∀ X Y : V, ∀ f : R, action (X + Y) f = action X f + action Y f
  action_add_right : ∀ X : V, ∀ f g : R, action X (f + g) = action X f + action X g
  action_smul_left : ∀ (c : R) (X : V) (f : R), action (c • X) f = c * action X f
  action_smul_right : ∀ X : V, ∀ (c f : R), action X (c * f) = action X c * f + c * action X f
  bracket_add_left : ∀ X Y Z : V, bracket (X + Y) Z = bracket X Z + bracket Y Z
  bracket_add_right : ∀ X Y Z : V, bracket X (Y + Z) = bracket X Y + bracket X Z
  bracket_smul_left : ∀ (c : R) (X Y : V), bracket (c • X) Y = c • (bracket X Y) - (action Y c) • X
  bracket_smul_right : ∀ (c : R) (X Y : V), bracket X (c • Y) = c • (bracket X Y) + (action X c) • Y
  bracket_antisymm : ∀ X Y : V, bracket X Y = - bracket Y X

variable [AbstractLieBracket V]
variable [DerivationRules R V]

/-- $X(0) = 0$ -/
lemma action_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) : action X (0:R) = 0 := by
  have h := DerivationRules.action_add_right X (0:R) (0:R)
  rw [add_zero] at h
  calc action X (0:R) = action X (0:R) + action X (0:R) - action X (0:R) := by abel
    _ = action X (0:R) - action X (0:R) := by rw [← h]
    _ = 0 := by abel

/-- $X(-g) = -X(g)$ -/
lemma action_neg {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) (g : R) : action X (- g) = - action X g := by
  have h : action X (g + -g) = action X g + action X (-g) := DerivationRules.action_add_right X g (-g)
  have hz : g + -g = 0 := by abel
  rw [hz, action_zero X] at h
  calc action X (-g) = action X g + action X (-g) - action X g := by abel
    _ = 0 - action X g := by rw [← h]
    _ = - action X g := by abel

/-- Explicit construction of the Levi-Civita connection using the Koszul formula.
Input: (AbstractMetricTensor R V)
Output: AbstractAffineConnection R V

# Reference:
# Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
-/
def koszul_connection [Invertible (2 : R)] [AbstractLieBracket V] [DerivationRules R V]
  (metric : MetricDuality R V) : AbstractAffineConnection R V where
  nabla X Y := metric.sharp (fun Z =>
    (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y)
      - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2)
  nabla_add_left X1 X2 Y := by
    have eq_func : (fun Z : V => (action (X1 + X2) (metric.g Y Z) + action Y (metric.g Z (X1 + X2)) - action Z (metric.g (X1 + X2) Y) - metric.g (X1 + X2) (bracket Y Z) + metric.g Y (bracket Z (X1 + X2)) + metric.g Z (bracket (X1 + X2) Y)) * ⅟2)
                   = (fun Z : V => (action X1 (metric.g Y Z) + action Y (metric.g Z X1) - action Z (metric.g X1 Y) - metric.g X1 (bracket Y Z) + metric.g Y (bracket Z X1) + metric.g Z (bracket X1 Y)) * ⅟2 +
                                   (action X2 (metric.g Y Z) + action Y (metric.g Z X2) - action Z (metric.g X2 Y) - metric.g X2 (bracket Y Z) + metric.g Y (bracket Z X2) + metric.g Z (bracket X2 Y)) * ⅟2) := by
      funext Z
      have h1 : action (X1 + X2) (metric.g Y Z) = action X1 (metric.g Y Z) + action X2 (metric.g Y Z) := DerivationRules.action_add_left X1 X2 _
      have h2 : metric.g Z (X1 + X2) = metric.g Z X1 + metric.g Z X2 := by rw [metric.symm Z (X1 + X2), metric.bilinear_add_left, metric.symm X1 Z, metric.symm X2 Z]
      have h3 : action Y (metric.g Z (X1 + X2)) = action Y (metric.g Z X1) + action Y (metric.g Z X2) := by rw [h2, DerivationRules.action_add_right]
      have h4 : metric.g (X1 + X2) Y = metric.g X1 Y + metric.g X2 Y := metric.bilinear_add_left _ _ _
      have h5 : action Z (metric.g (X1 + X2) Y) = action Z (metric.g X1 Y) + action Z (metric.g X2 Y) := by rw [h4, DerivationRules.action_add_right]
      have h6 : metric.g (X1 + X2) (bracket Y Z) = metric.g X1 (bracket Y Z) + metric.g X2 (bracket Y Z) := metric.bilinear_add_left _ _ _
      have h7 : bracket Z (X1 + X2) = bracket Z X1 + bracket Z X2 := DerivationRules.bracket_add_right R Z X1 X2
      have h8 : metric.g Y (bracket Z (X1 + X2)) = metric.g Y (bracket Z X1) + metric.g Y (bracket Z X2) := by rw [h7, metric.symm Y _, metric.bilinear_add_left, metric.symm _ Y, metric.symm _ Y]
      have h9 : bracket (X1 + X2) Y = bracket X1 Y + bracket X2 Y := DerivationRules.bracket_add_left R X1 X2 Y
      have h10 : metric.g Z (bracket (X1 + X2) Y) = metric.g Z (bracket X1 Y) + metric.g Z (bracket X2 Y) := by rw [h9, metric.symm Z _, metric.bilinear_add_left, metric.symm _ Z, metric.symm _ Z]
      rw [h1, h3, h5, h6, h8, h10]
      ring_nf
    rw [eq_func, metric.sharp_add]
  nabla_add_right X Y1 Y2 := by
    have eq_func : (fun Z : V => (action X (metric.g (Y1 + Y2) Z) + action (Y1 + Y2) (metric.g Z X) - action Z (metric.g X (Y1 + Y2)) - metric.g X (bracket (Y1 + Y2) Z) + metric.g (Y1 + Y2) (bracket Z X) + metric.g Z (bracket X (Y1 + Y2))) * ⅟2)
                   = (fun Z : V => (action X (metric.g Y1 Z) + action Y1 (metric.g Z X) - action Z (metric.g X Y1) - metric.g X (bracket Y1 Z) + metric.g Y1 (bracket Z X) + metric.g Z (bracket X Y1)) * ⅟2 +
                                   (action X (metric.g Y2 Z) + action Y2 (metric.g Z X) - action Z (metric.g X Y2) - metric.g X (bracket Y2 Z) + metric.g Y2 (bracket Z X) + metric.g Z (bracket X Y2)) * ⅟2) := by
      funext Z
      have h1 : metric.g (Y1 + Y2) Z = metric.g Y1 Z + metric.g Y2 Z := metric.bilinear_add_left _ _ _
      have h1a : action X (metric.g (Y1 + Y2) Z) = action X (metric.g Y1 Z) + action X (metric.g Y2 Z) := by rw [h1, DerivationRules.action_add_right]
      have h2 : action (Y1 + Y2) (metric.g Z X) = action Y1 (metric.g Z X) + action Y2 (metric.g Z X) := DerivationRules.action_add_left Y1 Y2 _
      have h3 : metric.g X (Y1 + Y2) = metric.g X Y1 + metric.g X Y2 := by rw [metric.symm X _, metric.bilinear_add_left, metric.symm _ X, metric.symm _ X]
      have h3a : action Z (metric.g X (Y1 + Y2)) = action Z (metric.g X Y1) + action Z (metric.g X Y2) := by rw [h3, DerivationRules.action_add_right]
      have h4 : bracket (Y1 + Y2) Z = bracket Y1 Z + bracket Y2 Z := DerivationRules.bracket_add_left R Y1 Y2 Z
      have h4a : metric.g X (bracket (Y1 + Y2) Z) = metric.g X (bracket Y1 Z) + metric.g X (bracket Y2 Z) := by rw [h4, metric.symm X _, metric.bilinear_add_left, metric.symm _ X, metric.symm _ X]
      have h5 : bracket Z (Y1 + Y2) = bracket Z Y1 + bracket Z Y2 := DerivationRules.bracket_add_right R Z Y1 Y2
      have h5a : metric.g (Y1 + Y2) (bracket Z X) = metric.g Y1 (bracket Z X) + metric.g Y2 (bracket Z X) := metric.bilinear_add_left _ _ _
      have h6 : bracket X (Y1 + Y2) = bracket X Y1 + bracket X Y2 := DerivationRules.bracket_add_right R X Y1 Y2
      have h6a : metric.g Z (bracket X (Y1 + Y2)) = metric.g Z (bracket X Y1) + metric.g Z (bracket X Y2) := by rw [h6, metric.symm Z _, metric.bilinear_add_left, metric.symm _ Z, metric.symm _ Z]
      rw [h1a, h2, h3a, h4a, h5a, h6a]
      ring_nf
    rw [eq_func, metric.sharp_add]
  nabla_smul_left c X Y := by
    have eq_func : (fun Z : V => (action (c • X) (metric.g Y Z) + action Y (metric.g Z (c • X)) - action Z (metric.g (c • X) Y) - metric.g (c • X) (bracket Y Z) + metric.g Y (bracket Z (c • X)) + metric.g Z (bracket (c • X) Y)) * ⅟2)
                   = (fun Z : V => c * ((action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2)) := by
      funext Z
      have h1 : action (c • X) (metric.g Y Z) = c * action X (metric.g Y Z) := DerivationRules.action_smul_left c X _
      have h2 : metric.g Z (c • X) = c * metric.g Z X := by rw [metric.symm Z _, metric.bilinear_smul_left, metric.symm X Z]
      have h2a : action Y (metric.g Z (c • X)) = action Y c * metric.g Z X + c * action Y (metric.g Z X) := by rw [h2, DerivationRules.action_smul_right]
      have h3 : metric.g (c • X) Y = c * metric.g X Y := metric.bilinear_smul_left _ _ _
      have h3a : action Z (metric.g (c • X) Y) = action Z c * metric.g X Y + c * action Z (metric.g X Y) := by rw [h3, DerivationRules.action_smul_right]
      have h4 : metric.g (c • X) (bracket Y Z) = c * metric.g X (bracket Y Z) := metric.bilinear_smul_left _ _ _
      have h5 : bracket Z (c • X) = c • (bracket Z X) + (action Z c) • X := DerivationRules.bracket_smul_right c Z X
      have h5a : metric.g Y (bracket Z (c • X)) = c * metric.g Y (bracket Z X) + action Z c * metric.g Y X := by rw [h5, metric.symm Y _, metric.bilinear_add_left, metric.bilinear_smul_left, metric.bilinear_smul_left, metric.symm (bracket _ _) Y, metric.symm X Y]
      have h6 : bracket (c • X) Y = c • (bracket X Y) - (action Y c) • X := DerivationRules.bracket_smul_left c X Y
      have h6a : metric.g Z (bracket (c • X) Y) = c * metric.g Z (bracket X Y) - action Y c * metric.g Z X := by rw [h6, metric.symm Z _, metric_sub_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.bilinear_smul_left, metric.bilinear_smul_left, metric.symm (bracket _ _) Z, metric.symm X Z]
      rw [h1, h2a, h3a, h4, h5a, h6a]
      have s1 : metric.g Z X = metric.g X Z := metric.symm Z X
      have s2 : metric.g Y X = metric.g X Y := metric.symm Y X
      rw [s1, s2]
      ring_nf
    rw [eq_func, metric.sharp_smul]
  leibniz c X Y := by
    have eq_func : (fun Z : V => (action X (metric.g (c • Y) Z) + action (c • Y) (metric.g Z X) - action Z (metric.g X (c • Y)) - metric.g X (bracket (c • Y) Z) + metric.g (c • Y) (bracket Z X) + metric.g Z (bracket X (c • Y))) * ⅟2)
                   = (fun Z : V => action X c * metric.g Y Z * ⅟2 * 2 +
                                   c * ((action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2)) := by
      funext Z
      have h1 : metric.g (c • Y) Z = c * metric.g Y Z := metric.bilinear_smul_left _ _ _
      have h1a : action X (metric.g (c • Y) Z) = action X c * metric.g Y Z + c * action X (metric.g Y Z) := by rw [h1, DerivationRules.action_smul_right]
      have h2 : action (c • Y) (metric.g Z X) = c * action Y (metric.g Z X) := DerivationRules.action_smul_left c Y _
      have h3 : metric.g X (c • Y) = c * metric.g X Y := by rw [metric.symm X _, metric.bilinear_smul_left, metric.symm Y X]
      have h3a : action Z (metric.g X (c • Y)) = action Z c * metric.g X Y + c * action Z (metric.g X Y) := by rw [h3, DerivationRules.action_smul_right]
      have h4 : bracket (c • Y) Z = c • (bracket Y Z) - (action Z c) • Y := DerivationRules.bracket_smul_left c Y Z
      have h4a : metric.g X (bracket (c • Y) Z) = c * metric.g X (bracket Y Z) - action Z c * metric.g X Y := by rw [h4, metric.symm X _, metric_sub_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.bilinear_smul_left, metric.bilinear_smul_left, metric.symm (bracket _ _) X, metric.symm Y X]
      have h5 : bracket Z (c • Y) = c • (bracket Z Y) + (action Z c) • Y := DerivationRules.bracket_smul_right c Z Y
      have h5a : metric.g (c • Y) (bracket Z X) = c * metric.g Y (bracket Z X) := metric.bilinear_smul_left _ _ _
      have h6 : bracket X (c • Y) = c • (bracket X Y) + (action X c) • Y := DerivationRules.bracket_smul_right c X Y
      have h6a : metric.g Z (bracket X (c • Y)) = c * metric.g Z (bracket X Y) + action X c * metric.g Z Y := by rw [h6, metric.symm Z _, metric.bilinear_add_left, metric.bilinear_smul_left, metric.bilinear_smul_left, metric.symm (bracket _ _) Z, metric.symm Y Z]
      rw [h1a, h2, h3a, h4a, h5a, h6a]
      have s1 : metric.g Z Y = metric.g Y Z := metric.symm Z Y
      rw [s1]
      ring_nf
    rw [eq_func, metric.sharp_add, metric.sharp_smul]
    have direct_term : metric.sharp (fun Z => action X c * metric.g Y Z * ⅟2 * 2) = (action X c) • Y := by
      have h_cancel : ∀ Z, action X c * metric.g Y Z * ⅟2 * 2 = action X c * metric.g Y Z := fun Z => by
        calc action X c * metric.g Y Z * ⅟2 * 2 = action X c * metric.g Y Z * (⅟2 * 2) := by ring
          _ = action X c * metric.g Y Z * 1 := by rw [invOf_mul_self 2]
          _ = action X c * metric.g Y Z := by ring
      have h : (fun Z => action X c * metric.g Y Z * ⅟2 * 2) = (fun Z => action X c * metric.g Y Z) := funext h_cancel
      rw [h, metric.sharp_smul, metric.sharp_g]
    rw [direct_term]

instance metric_compat_koszul [Invertible (2 : R)] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (metric : MetricDuality R V) : MetricCompatible (koszul_connection metric) metric.toNonDegenerateMetric.toAbstractMetricTensor where
  compat X Y Z := by
    let nabla := (koszul_connection metric).nabla
    have h1 : metric.g (nabla X Y) Z = (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 := by
      exact metric.g_sharp _ _
    have h2 : metric.g (nabla X Z) Y = (action X (metric.g Z Y) + action Z (metric.g Y X) - action Y (metric.g X Z) - metric.g X (bracket Z Y) + metric.g Z (bracket Y X) + metric.g Y (bracket X Z)) * ⅟2 := by
      exact metric.g_sharp _ _
    have h3 : metric.g Y (nabla X Z) = metric.g (nabla X Z) Y := metric.symm _ _
    rw [h1, h3, h2]
    have s1 : metric.g Z Y = metric.g Y Z := metric.symm Z Y
    have s2 : metric.g Y X = metric.g X Y := metric.symm Y X
    have s3 : metric.g X Z = metric.g Z X := metric.symm X Z
    have b1 : bracket Z Y = - bracket Y Z := DerivationRules.bracket_antisymm R Z Y
    have b2 : bracket Y X = - bracket X Y := DerivationRules.bracket_antisymm R Y X
    have b3 : bracket X Z = - bracket Z X := DerivationRules.bracket_antisymm R X Z
    have m1 : metric.g X (bracket Z Y) = - metric.g X (bracket Y Z) := by rw [b1, metric.symm X _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ X]
    have m2 : metric.g Z (bracket Y X) = - metric.g Z (bracket X Y) := by rw [b2, metric.symm Z _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ Z]
    have m3 : metric.g Y (bracket X Z) = - metric.g Y (bracket Z X) := by rw [b3, metric.symm Y _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ Y]
    rw [s1, s2, s3, m1, m2, m3]
    have eq_rhs : (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 + (action X (metric.g Y Z) + action Z (metric.g X Y) - action Y (metric.g Z X) - -metric.g X (bracket Y Z) + -metric.g Z (bracket X Y) + -metric.g Y (bracket Z X)) * ⅟2 = action X (metric.g Y Z) * ⅟2 * 2 := by ring_nf
    rw [eq_rhs]
    calc action X (metric.g Y Z) = action X (metric.g Y Z) * 1 := by ring
        _ = action X (metric.g Y Z) * (⅟2 * 2) := by rw [← invOf_mul_self 2]
        _ = action X (metric.g Y Z) * ⅟2 * 2 := by ring

instance torsion_free_koszul [Invertible (2 : R)] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (metric : MetricDuality R V) : TorsionFree (koszul_connection metric) where
  torsion_zero X Y := by
    let nabla := (koszul_connection metric).nabla
    have eq_func : (fun Z : V => (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 - (action Y (metric.g X Z) + action X (metric.g Z Y) - action Z (metric.g Y X) - metric.g Y (bracket X Z) + metric.g X (bracket Z Y) + metric.g Z (bracket Y X)) * ⅟2) = (fun Z : V => metric.g (bracket X Y) Z) := by
      funext Z
      have s1 : metric.g X Z = metric.g Z X := metric.symm X Z
      have s2 : metric.g Z Y = metric.g Y Z := metric.symm Z Y
      have s3 : metric.g Y X = metric.g X Y := metric.symm Y X
      have b1 : bracket X Z = - bracket Z X := DerivationRules.bracket_antisymm R X Z
      have b2 : bracket Z Y = - bracket Y Z := DerivationRules.bracket_antisymm R Z Y
      have b3 : bracket Y X = - bracket X Y := DerivationRules.bracket_antisymm R Y X
      have m1 : metric.g Y (bracket X Z) = - metric.g Y (bracket Z X) := by rw [b1, metric.symm Y _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ Y]
      have m2 : metric.g X (bracket Z Y) = - metric.g X (bracket Y Z) := by rw [b2, metric.symm X _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ X]
      have m3 : metric.g Z (bracket Y X) = - metric.g Z (bracket X Y) := by rw [b3, metric.symm Z _, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), metric.symm _ Z]
      rw [s1, s2, s3, m1, m2, m3]
      have eq_rhs : (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 - (action Y (metric.g Z X) + action X (metric.g Y Z) - action Z (metric.g X Y) - -metric.g Y (bracket Z X) + -metric.g X (bracket Y Z) + -metric.g Z (bracket X Y)) * ⅟2 = metric.g Z (bracket X Y) * ⅟2 * 2 := by ring_nf
      rw [eq_rhs]
      have h_cancel : metric.g Z (bracket X Y) * ⅟2 * 2 = metric.g Z (bracket X Y) := by
        calc metric.g Z (bracket X Y) * ⅟2 * 2 = metric.g Z (bracket X Y) * (⅟2 * 2) := by ring
          _ = metric.g Z (bracket X Y) * 1 := by rw [invOf_mul_self 2]
          _ = metric.g Z (bracket X Y) := by ring
      rw [h_cancel]
      exact metric.symm Z (bracket X Y)
    have g_inj : ∀ A B : V, (∀ Z, metric.g A Z = metric.g B Z) → A = B := by
      intro A B h
      have hA : metric.sharp (fun Z => metric.g A Z) = A := metric.sharp_g A
      have hB : metric.sharp (fun Z => metric.g B Z) = B := metric.sharp_g B
      have hF : (fun Z => metric.g A Z) = (fun Z => metric.g B Z) := funext h
      rw [← hA, ← hB, hF]
    apply g_inj
    intro Z
    have hg : metric.g (nabla X Y - nabla Y X) Z = metric.g (nabla X Y) Z - metric.g (nabla Y X) Z := by
      have hsub : nabla X Y - nabla Y X = nabla X Y + - nabla Y X := sub_eq_add_neg _ _
      rw [hsub, metric.bilinear_add_left, metric_neg_left (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor), ← sub_eq_add_neg]
    rw [hg]
    have gX : metric.g (nabla X Y) Z = (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 := metric.g_sharp _ _
    have gY : metric.g (nabla Y X) Z = (action Y (metric.g X Z) + action X (metric.g Z Y) - action Z (metric.g Y X) - metric.g Y (bracket X Z) + metric.g X (bracket Z Y) + metric.g Z (bracket Y X)) * ⅟2 := metric.g_sharp _ _
    rw [gX, gY]
    exact congrFun eq_func Z

/-- Fundamental Theorem of Riemannian Geometry:
For any Riemannian manifold, there exists a unique affine connection that is symmetric (torsion-free) and compatible with the metric.
Input: (AbstractMetricTensor R V)
Output: Prop

# Reference:
# Differential Geometry and Applications, Richard Hamilton, Monique Chyba and Xiaodong Cao
-/
theorem levi_civita_exists_unique [Invertible (2 : R)] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (metric : MetricDuality R V) :
  ∃ (conn : AbstractAffineConnection R V),
    (MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor ∧ TorsionFree conn) ∧
    (∀ (conn' : AbstractAffineConnection R V), MetricCompatible conn' metric.toNonDegenerateMetric.toAbstractMetricTensor ∧ TorsionFree conn' → conn' = conn) := by
  use koszul_connection metric
  constructor
  · exact ⟨metric_compat_koszul metric, torsion_free_koszul metric⟩
  · intro conn' h
    rcases h with ⟨compat', torsion'⟩
    have h_nabla : conn'.nabla = (koszul_connection metric).nabla := by
      funext X Y
      have g_inj : ∀ A B : V, (∀ Z, metric.g A Z = metric.g B Z) → A = B := by
        intro A B h_g
        have hA : metric.sharp (fun Z => metric.g A Z) = A := metric.sharp_g A
        have hB : metric.sharp (fun Z => metric.g B Z) = B := metric.sharp_g B
        have hF : (fun Z => metric.g A Z) = (fun Z => metric.g B Z) := funext h_g
        rw [← hA, ← hB, hF]
      apply g_inj
      intro Z
      have h1 : 2 * metric.g (conn'.nabla X Y) Z = action X (metric.g Y Z) + action Y (metric.g X Z) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y) := levi_civita_uniqueness conn' metric.toNonDegenerateMetric.toAbstractMetricTensor X Y Z
      have h2 : metric.g ((koszul_connection metric).nabla X Y) Z = (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 := metric.g_sharp _ _
      have sx : metric.g X Z = metric.g Z X := metric.symm X Z
      rw [sx] at h1
      calc metric.g (conn'.nabla X Y) Z = metric.g (conn'.nabla X Y) Z * 1 := by ring
        _ = metric.g (conn'.nabla X Y) Z * (2 * ⅟2) := by rw [mul_invOf_self 2]
        _ = (2 * metric.g (conn'.nabla X Y) Z) * ⅟2 := by ring
        _ = (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y) - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) * ⅟2 := by rw [h1]
        _ = metric.g ((koszul_connection metric).nabla X Y) Z := by rw [← h2]
    cases conn'
    have hk : koszul_connection metric = AbstractAffineConnection.mk (koszul_connection metric).nabla (koszul_connection metric).nabla_add_left (koszul_connection metric).nabla_add_right (koszul_connection metric).nabla_smul_left (koszul_connection metric).leibniz := rfl
    rw [hk]
    congr

-- 5. Bundled Levi-Civita Connection
class AbstractLeviCivitaConnection (metric : AbstractMetricTensor R V) [AbstractLieBracket V] extends AbstractAffineConnection R V where
  compat : ∀ X Y Z : V, action X (metric.g Y Z) = metric.g (nabla X Y) Z + metric.g Y (nabla X Z)
  torsion_zero : ∀ X Y : V, nabla X Y - nabla Y X = bracket X Y
