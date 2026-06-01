import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra
import DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Tactic.Abel

/-!
# Affine Connections and Curvature

Torsion-free and Levi-Civita conditions, Riemann curvature Rm(X,Y)Z,
Rm multilinearity, and the first Bianchi identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open SyntheticTensor

-- ============================================================
-- Generic: Invertible 2 implies annihilation form of 2-regularity
-- ============================================================

/-- Generic derivation: given `Invertible (2 : R)` in a monoid-with-zero structure,
`2 * a = 0 → a = 0`. This is the annihilation form of 2-regularity, and is implied
by `Invertible (2 : R)`. -/
theorem char_ne_2_of_invertible_two {R : Type*} [MonoidWithZero R]
    [OfNat R 2] [Invertible (2 : R)] (a : R) (h : (2 : R) * a = 0) : a = 0 := by
  calc a = ⅟(2 : R) * ((2 : R) * a) := (invOf_mul_cancel_left _ _).symm
    _ = ⅟(2 : R) * 0 := by rw [h]
    _ = 0 := mul_zero _

-- ============================================================
-- IsTorsionFree, IsLeviCivita
-- ============================================================

section Conditions
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def IsTorsionFree (emb : DerivationEmbedding k R V) (conn : V → V → V) : Prop :=
  ∀ X Y : V, conn X Y - conn Y X = bracket emb X Y

def IsLeviCivita (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (met : MetricDuality R V) : Prop :=
  IsMetricCompatible emb conn met ∧ IsTorsionFree emb conn

end Conditions

-- ============================================================
-- Connection helpers
-- ============================================================

section ConnHelpers
variable {V : Type*} [AddCommGroup V]

theorem conn_zero_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (Z : V) :
    conn 0 Z = 0 := by
  have h := hal 0 0 Z; simp only [zero_add] at h
  -- h : conn 0 Z = conn 0 Z + conn 0 Z
  have : conn 0 Z + conn 0 Z = conn 0 Z + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem conn_neg_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (X Z : V) :
    conn (-X) Z = -conn X Z := by
  have h := hal X (-X) Z; rw [add_neg_cancel, conn_zero_left conn hal] at h
  -- h : 0 = conn X Z + conn (-X) Z, i.e. conn X Z + conn (-X) Z = 0
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

theorem conn_sub_left (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z) (A B Z : V) :
    conn (A - B) Z = conn A Z - conn B Z := by
  rw [sub_eq_add_neg, hal, conn_neg_left conn hal, ← sub_eq_add_neg]

theorem conn_zero_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X : V) :
    conn X 0 = 0 := by
  have h := ha X 0 0; simp only [zero_add] at h
  have : conn X 0 + conn X 0 = conn X 0 + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem conn_neg_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X Y : V) :
    conn X (-Y) = -conn X Y := by
  have h := ha X Y (-Y); rw [add_neg_cancel, conn_zero_right conn ha] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

theorem conn_sub_right (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z) (X A B : V) :
    conn X (A - B) = conn X A - conn X B := by
  rw [sub_eq_add_neg, ha, conn_neg_right conn ha, ← sub_eq_add_neg]

end ConnHelpers

-- ============================================================
-- Riemann curvature
-- ============================================================

section Curvature
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def Rm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket emb X Y) Z

theorem Rm_antisymm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y Z : V) :
    Rm emb conn X Y Z = -Rm emb conn Y X Z := by
  simp only [Rm, bracket_antisymm emb X Y, conn_neg_left conn hal]; abel

theorem Rm_add_Z (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y Z₁ Z₂ : V) :
    Rm emb conn X Y (Z₁ + Z₂) = Rm emb conn X Y Z₁ + Rm emb conn X Y Z₂ := by
  simp only [Rm, ha]; abel

theorem Rm_add_X (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X₁ X₂ Y Z : V) :
    Rm emb conn (X₁ + X₂) Y Z = Rm emb conn X₁ Y Z + Rm emb conn X₂ Y Z := by
  simp only [Rm, hal, ha, bracket_add_left emb]; abel

theorem Rm_add_Y (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (X Y₁ Y₂ Z : V) :
    Rm emb conn X (Y₁ + Y₂) Z = Rm emb conn X Y₁ Z + Rm emb conn X Y₂ Z := by
  simp only [Rm, hal, ha, bracket_add_right emb]; abel

theorem Rm_smul_Z (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn X Y (f • Z) = f • Rm emb conn X Y Z := by
  unfold Rm
  rw [hl Y f Z, hl X f Z, hl (bracket emb X Y) f Z,
      ha X _ _, ha Y _ _,
      hl X ((emb.embed Y) f) Z, hl Y ((emb.embed X) f) Z,
      hl X f (conn Y Z), hl Y f (conn X Z)]
  -- Key: [X,Y](f) = X(Y(f)) - Y(X(f)) by action_bracket
  -- In the goal, (emb.embed (bracket emb X Y)) f appears, which is action emb (bracket emb X Y) f
  have hab : (emb.embed (bracket emb X Y)) f =
      (emb.embed X) ((emb.embed Y) f) - (emb.embed Y) ((emb.embed X) f) :=
    action_bracket emb X Y f
  rw [hab, sub_smul, smul_sub, smul_sub]; abel

theorem Rm_smul_Y (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn X (f • Y) Z = f • Rm emb conn X Y Z := by
  unfold Rm
  rw [hsl f Y Z, hl X f (conn Y Z), hsl f Y (conn X Z),
      bracket_smul_right emb, hal _ _ Z, hsl f _ Z,
      show action emb X f = (emb.embed X) f from rfl,
      hsl ((emb.embed X) f) Y Z, smul_sub, smul_sub]; abel

theorem Rm_smul_X (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X Y Z : V) :
    Rm emb conn (f • X) Y Z = f • Rm emb conn X Y Z := by
  unfold Rm
  rw [hsl f X (conn Y Z), hsl f X Z, hl Y f (conn X Z),
      bracket_smul_left emb,
      show action emb Y f = (emb.embed Y) f from rfl,
      conn_sub_left conn hal, hsl f _ Z, hsl ((emb.embed Y) f) X Z,
      smul_sub, smul_sub]; abel

end Curvature

-- ============================================================
-- First Bianchi identity
-- ============================================================

section Bianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- **First Bianchi identity.** For a torsion-free connection `conn` (additive in its
second argument), the cyclic sum of the Riemann curvature endomorphism vanishes:
`Rm(X,Y)Z + Rm(Y,Z)X + Rm(Z,X)Y = 0`. The proof rewrites the cyclic sum, using
torsion-freeness to turn second-order terms into single covariant derivatives of
brackets, and closes with the Jacobi identity for the bracket. -/
theorem bianchi_first_Rm_cyclic_sum_zero_of_torsionFree (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z : V) :
    Rm emb conn X Y Z + Rm emb conn Y Z X + Rm emb conn Z X Y = 0 := by
  have t : ∀ A B, bracket emb A B = conn A B - conn B A := fun A B => (h_tf A B).symm
  have r : ∀ A B C, conn A (conn B C) - conn A (conn C B) = conn A (bracket emb B C) := by
    intro A B C; rw [← conn_sub_right conn ha, t]
  unfold Rm
  calc conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket emb X Y) Z
    + (conn Y (conn Z X) - conn Z (conn Y X) - conn (bracket emb Y Z) X)
    + (conn Z (conn X Y) - conn X (conn Z Y) - conn (bracket emb Z X) Y)
      = (conn X (conn Y Z) - conn X (conn Z Y))
      + (conn Y (conn Z X) - conn Y (conn X Z))
      + (conn Z (conn X Y) - conn Z (conn Y X))
      - conn (bracket emb X Y) Z - conn (bracket emb Y Z) X
      - conn (bracket emb Z X) Y := by abel
    _ = conn X (bracket emb Y Z) + conn Y (bracket emb Z X) + conn Z (bracket emb X Y)
      - conn (bracket emb X Y) Z - conn (bracket emb Y Z) X
      - conn (bracket emb Z X) Y := by rw [r X Y Z, r Y Z X, r Z X Y]
    _ = (conn X (bracket emb Y Z) - conn (bracket emb Y Z) X)
      + (conn Y (bracket emb Z X) - conn (bracket emb Z X) Y)
      + (conn Z (bracket emb X Y) - conn (bracket emb X Y) Z) := by abel
    _ = bracket emb X (bracket emb Y Z) + bracket emb Y (bracket emb Z X)
      + bracket emb Z (bracket emb X Y) := by
      rw [t X (bracket emb Y Z), t Y (bracket emb Z X), t Z (bracket emb X Y)]
    _ = 0 := jacobi_identity emb X Y Z

end Bianchi

-- ============================================================
-- Koszul formula (koszul_formula_of_metricCompatible_torsionFree)
-- ============================================================

section Koszul
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

-- Metric subtraction helpers
private theorem g_sub_left' (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C := by
  have h1 := met.g_add_left A (-B) C
  rw [show A + -B = A - B from (sub_eq_add_neg A B).symm] at h1
  have h2 : met.g (-B) C = -met.g B C := by
    have := met.g_smul_left (-1 : R) B C; rwa [neg_one_smul, neg_one_mul] at this
  rw [h1, h2, sub_eq_add_neg]

private theorem g_sub_right' (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C := by
  rw [met.g_symm A (B - C), g_sub_left' met B C A, met.g_symm B A, met.g_symm C A]

/-- **Koszul formula.** Any metric-compatible, torsion-free connection `conn` satisfies
`2·g(∇_X Y, Z) = X(g(Y,Z)) + Y(g(Z,X)) - Z(g(X,Y)) - g(X,[Y,Z]) + g(Y,[Z,X]) + g(Z,[X,Y])`.
This expresses the connection in terms of the metric and brackets; it is the identity
underlying uniqueness of the Levi-Civita connection (uniqueness itself is a separate
statement). The proof expands the brackets via torsion-freeness, distributes the metric
over the resulting differences, and applies metric compatibility three times. -/
theorem koszul_formula_of_metricCompatible_torsionFree
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (_ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (_hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) (X Y Z : V) :
    2 * met.g (conn X Y) Z =
      (emb.embed X) (met.g Y Z) + (emb.embed Y) (met.g Z X) - (emb.embed Z) (met.g X Y)
      - met.g X (bracket emb Y Z) + met.g Y (bracket emb Z X) + met.g Z (bracket emb X Y) := by
  have eq1 := h_mc X Y Z
  have eq2 := h_mc Y Z X
  have eq3 := h_mc Z X Y
  rw [show bracket emb X Y = conn X Y - conn Y X from (h_tf X Y).symm,
      show bracket emb Z X = conn Z X - conn X Z from (h_tf Z X).symm,
      show bracket emb Y Z = conn Y Z - conn Z Y from (h_tf Y Z).symm,
      g_sub_right' met X _ _, g_sub_right' met Y _ _, g_sub_right' met Z _ _,
      eq1, eq2, eq3,
      met.g_symm (conn Y Z) X, met.g_symm Z (conn Y X),
      met.g_symm (conn Z X) Y, met.g_symm X (conn Z Y),
      met.g_symm Z (conn X Y)]; ring

end Koszul

-- ============================================================
-- Rm metric antisymmetry: g(Rm(X,Y)Z, W) = -g(Rm(X,Y)W, Z)
-- ============================================================

section RmMetric
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- For a metric-compatible connection, the Riemann curvature is skew-symmetric in its
last two arguments with respect to the metric: `g(Rm(X,Y)Z, W) = -g(Rm(X,Y)W, Z)`.
The proof differentiates the metric-compatibility identity a second time to expand
`X(Y(g(Z,W)))` and `Y(X(g(Z,W)))`, uses `action_bracket` for the `[X,Y]` term, and
collects the curvature terms so the cross terms cancel. -/
theorem Rm_metric_skew_last_two_of_metricCompatible
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X Y Z W : V) :
    met.g (Rm emb conn X Y Z) W = -met.g (Rm emb conn X Y W) Z := by
  suffices h : met.g (Rm emb conn X Y Z) W + met.g Z (Rm emb conn X Y W) = 0 by
    rw [met.g_symm Z _] at h; exact eq_neg_of_add_eq_zero_left h
  -- Metric compatibility: X(g(A,B)) = g(∇XA,B) + g(A,∇XB)
  have c1 := h_mc Y Z W; have c2 := h_mc X Z W
  have c3 := h_mc X (conn Y Z) W; have c4 := h_mc X Z (conn Y W)
  have c5 := h_mc Y (conn X Z) W; have c6 := h_mc Y Z (conn X W)
  have c7 := h_mc (bracket emb X Y) Z W
  -- Double expansions: X(Y(g(Z,W))) and Y(X(g(Z,W)))
  have hXY : (emb.embed X) ((emb.embed Y) (met.g Z W)) =
      met.g (conn X (conn Y Z)) W + met.g (conn Y Z) (conn X W) +
      met.g (conn X Z) (conn Y W) + met.g Z (conn X (conn Y W)) := by
    rw [c1, (emb.embed X).map_add (met.g (conn Y Z) W) (met.g Z (conn Y W)), c3, c4]; ring
  have hYX : (emb.embed Y) ((emb.embed X) (met.g Z W)) =
      met.g (conn Y (conn X Z)) W + met.g (conn X Z) (conn Y W) +
      met.g (conn Y Z) (conn X W) + met.g Z (conn Y (conn X W)) := by
    rw [c2, (emb.embed Y).map_add (met.g (conn X Z) W) (met.g Z (conn X W)), c5, c6]; ring
  -- Key identity: g(∇[X,Y]Z,W) + g(Z,∇[X,Y]W) = g(∇X∇YZ,W) - g(∇Y∇XZ,W) + g(Z,∇X∇YW) - g(Z,∇Y∇XW)
  -- From c7 + action_bracket + hXY + hYX
  have key : met.g (conn (bracket emb X Y) Z) W + met.g Z (conn (bracket emb X Y) W) =
      met.g (conn X (conn Y Z)) W - met.g (conn Y (conn X Z)) W +
      met.g Z (conn X (conn Y W)) - met.g Z (conn Y (conn X W)) := by
    -- c7 gives LHS = (emb.embed [X,Y])(g(Z,W))
    -- action_bracket gives [X,Y](g) = X(Y(g)) - Y(X(g))
    -- hXY/hYX expand X(Y(g)) and Y(X(g)), cross terms cancel
    have hab : (emb.embed (bracket emb X Y)) (met.g Z W) =
        (emb.embed X) ((emb.embed Y) (met.g Z W)) -
        (emb.embed Y) ((emb.embed X) (met.g Z W)) :=
      action_bracket emb X Y (met.g Z W)
    rw [← c7, hab, hXY, hYX]; ring
  -- Unfold Rm and distribute metric over subtraction
  unfold Rm
  rw [g_sub_left' met, g_sub_left' met, g_sub_right' met, g_sub_right' met]
  -- Goal: A - B - C + (D - E - F) = 0 where key says C + F = A - B + D - E
  -- Rearrange: (A - B + D - E) - (C + F) = 0, then apply key
  rw [show met.g (conn X (conn Y Z)) W - met.g (conn Y (conn X Z)) W -
      met.g (conn (bracket emb X Y) Z) W +
      (met.g Z (conn X (conn Y W)) - met.g Z (conn Y (conn X W)) -
       met.g Z (conn (bracket emb X Y) W)) =
      (met.g (conn X (conn Y Z)) W - met.g (conn Y (conn X Z)) W +
       met.g Z (conn X (conn Y W)) - met.g Z (conn Y (conn X W))) -
      (met.g (conn (bracket emb X Y) Z) W + met.g Z (conn (bracket emb X Y) W)) from by ring,
      key, sub_self]

end RmMetric

-- ============================================================
-- Second Bianchi identity
-- ============================================================

section SecondBianchi
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Covariant derivative of Rm. -/
noncomputable def covDerivRm (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (X Y Z W : V) : V :=
  conn X (Rm emb conn Y Z W) - Rm emb conn (conn X Y) Z W
  - Rm emb conn Y (conn X Z) W - Rm emb conn Y Z (conn X W)

/-- **Second Bianchi identity.** For a torsion-free connection `conn` (additive in each
argument), the cyclic sum of covariant derivatives of the Riemann tensor vanishes:
`(∇_X Rm)(Y,Z)W + (∇_Y Rm)(Z,X)W + (∇_Z Rm)(X,Y)W = 0`, where `∇ Rm` is `covDerivRm`.
The proof expands all twelve second-order terms, pairs them via torsion-freeness into
covariant derivatives of double brackets, and closes with the Jacobi identity. -/
theorem bianchi_second_covDerivRm_cyclic_sum_zero_of_torsionFree
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z W : V) :
    covDerivRm emb conn X Y Z W + covDerivRm emb conn Y Z X W +
    covDerivRm emb conn Z X Y W = 0 := by
  -- ∇_X Rm(Y,Z)W = conn X (Rm Y Z W) - Rm(∇XY,Z)W - Rm(Y,∇XZ)W - Rm(Y,Z,∇XW)
  -- Use bianchi_first_Rm_cyclic_sum_zero_of_torsionFree on the bracket-level structure:
  -- After expanding, the sum telescopes to bracket(bracket) terms which vanish by Jacobi.
  have t : ∀ A B, bracket emb A B = conn A B - conn B A := fun A B => (h_tf A B).symm
  have sl : ∀ A B C, conn (A - B) C = conn A C - conn B C := conn_sub_left conn hal
  have sr : ∀ A B C, conn A (B - C) = conn A B - conn A C := conn_sub_right conn ha
  unfold covDerivRm Rm
  simp only [t, sl, sr]
  -- 12 terms of form ± conn(conn(a)(b))(W). Group pairs using sl on OUTER conn:
  -- conn(conn(connXY)Z)W - conn(conn(connYX)Z)W = conn(conn(connXY - connYX)Z)W
  --   = conn(conn([X,Y])Z)W by torsion-free
  -- But abel can't do this. Rewrite manually:
  -- Rearrange 12 terms into 6 pairs, each differing in inner first-arg
  -- Pair helpers: combine ± conn(conn(a)(b))(W) using conn_sub_left on inner conn
  have p1 : conn (conn (conn X Y) Z) W - conn (conn (conn Y X) Z) W =
      conn (conn (bracket emb X Y) Z) W := by
    rw [← sl]; congr 1; rw [← sl, t]
  have p2 : conn (conn (conn Y Z) X) W - conn (conn (conn Z Y) X) W =
      conn (conn (bracket emb Y Z) X) W := by
    rw [← sl]; congr 1; rw [← sl, t]
  have p3 : conn (conn (conn Z X) Y) W - conn (conn (conn X Z) Y) W =
      conn (conn (bracket emb Z X) Y) W := by
    rw [← sl]; congr 1; rw [← sl, t]
  have p4 : conn (conn Z (conn Y X)) W - conn (conn Z (conn X Y)) W =
      conn (conn Z (-(bracket emb X Y))) W := by
    rw [← sl]; congr 1; rw [← sr]; congr 1; rw [t]; abel
  have p5 : conn (conn X (conn Z Y)) W - conn (conn X (conn Y Z)) W =
      conn (conn X (-(bracket emb Y Z))) W := by
    rw [← sl]; congr 1; rw [← sr]; congr 1; rw [t]; abel
  have p6 : conn (conn Y (conn X Z)) W - conn (conn Y (conn Z X)) W =
      conn (conn Y (-(bracket emb Z X))) W := by
    rw [← sl]; congr 1; rw [← sr]; congr 1; rw [t]; abel
  -- Combine all 12 terms into the 6 paired expressions
  -- The 12 terms after abel_nf grouping: rearrange to form the 6 differences
  calc _ = (conn (conn (conn X Y) Z) W - conn (conn (conn Y X) Z) W) +
           (conn (conn (conn Y Z) X) W - conn (conn (conn Z Y) X) W) +
           (conn (conn (conn Z X) Y) W - conn (conn (conn X Z) Y) W) +
           (conn (conn Z (conn Y X)) W - conn (conn Z (conn X Y)) W) +
           (conn (conn X (conn Z Y)) W - conn (conn X (conn Y Z)) W) +
           (conn (conn Y (conn X Z)) W - conn (conn Y (conn Z X)) W) := by abel
    _ = conn (conn (bracket emb X Y) Z) W + conn (conn (bracket emb Y Z) X) W +
        conn (conn (bracket emb Z X) Y) W +
        conn (conn Z (-(bracket emb X Y))) W + conn (conn X (-(bracket emb Y Z))) W +
        conn (conn Y (-(bracket emb Z X))) W := by rw [p1, p2, p3, p4, p5, p6]
    _ = conn (conn (bracket emb X Y) Z) W - conn (conn Z (bracket emb X Y)) W +
        (conn (conn (bracket emb Y Z) X) W - conn (conn X (bracket emb Y Z)) W) +
        (conn (conn (bracket emb Z X) Y) W - conn (conn Y (bracket emb Z X)) W) := by
      simp only [conn_neg_right conn ha, conn_neg_left conn hal]; abel
    _ = conn (bracket emb (bracket emb X Y) Z) W +
        conn (bracket emb (bracket emb Y Z) X) W +
        conn (bracket emb (bracket emb Z X) Y) W := by
      rw [← sl, ← t, ← sl, ← t, ← sl, ← t]
    _ = conn (bracket emb (bracket emb X Y) Z + bracket emb (bracket emb Y Z) X +
             bracket emb (bracket emb Z X) Y) W := by
      rw [← hal, ← hal]
    _ = conn (-(bracket emb Z (bracket emb X Y) + bracket emb X (bracket emb Y Z) +
                bracket emb Y (bracket emb Z X))) W := by
      congr 1; rw [bracket_antisymm emb (bracket emb X Y) Z,
                    bracket_antisymm emb (bracket emb Y Z) X,
                    bracket_antisymm emb (bracket emb Z X) Y]; abel
    _ = conn (-(0 : V)) W := by rw [jacobi_identity emb Z X Y]
    _ = conn 0 W := by rw [neg_zero]
    _ = 0 := conn_zero_left conn hal W

end SecondBianchi

-- ============================================================
-- Ricci identity: [∇_X, ∇_Y]Z = Rm(X,Y)Z for torsion-free ∇
-- ============================================================

section RicciIdentity
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def secondCovDerivCommutator (conn : V → V → V) (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (conn X Y - conn Y X) Z

theorem ricci_identity
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (_hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn) (X Y Z : V) :
    secondCovDerivCommutator conn X Y Z = Rm emb conn X Y Z := by
  unfold secondCovDerivCommutator Rm
  rw [(h_tf X Y).symm]

end RicciIdentity

-- ============================================================
-- Ricci tensor and scalar curvature
-- ============================================================

section RicciTensor
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def RcEndo (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Z : V) : V →ₗ[R] V where
  toFun Y := Rm emb conn Y X Z
  map_add' Y₁ Y₂ := Rm_add_X emb conn ha hal Y₁ Y₂ X Z
  map_smul' f Y := by
    simp only [RingHom.id_apply]; exact Rm_smul_X emb conn hal hsl hl f Y X Z

noncomputable def Rc (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (X Z : V) : R :=
  atr.tr (RcEndo emb conn ha hal hsl hl X Z)

end RicciTensor
