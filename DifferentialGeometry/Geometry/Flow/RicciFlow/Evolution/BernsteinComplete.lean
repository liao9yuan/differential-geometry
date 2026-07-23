import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiHigher
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

/-!
# Complete noncompact Bernstein estimates

This file owns the noncompact localization interfaces for the Bernstein
curvature tower.  A valid complete-manifold proof must consume quantitative
parabolic cutoffs and the curvature-tower Kato estimate before discarding the
negative next-level terms.

The legacy `estimate_complete` statement below predates that audit and has
insufficient hypotheses.  It remains temporarily for its current caller, but
must not be treated as the canonical target.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

/-- Quantitative spacetime cutoffs for a complete-flow Bernstein argument.
Each cutoff is supported in one spatial compact set for the whole time slab;
this is stronger than slicewise compact support and is what makes the
localized spacetime maximum argument compact. -/
structure ShiCutoffData
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) where
  chi : Nat → Real → M → Real
  err : Nat → Real
  support : Nat → Set M
  err_nonneg : ∀ n, 0 ≤ err n
  err_tendsto : Filter.Tendsto err Filter.atTop (nhds 0)
  support_compact : ∀ n, IsCompact (support n)
  support_zero : ∀ n t, t ∈ Set.Icc 0 T → ∀ x, x ∉ support n → chi n t x = 0
  range : ∀ n t x, t ∈ Set.Icc 0 T → chi n t x ∈ Set.Icc (0 : Real) 1
  exhausts : ∀ t x, t ∈ Set.Icc 0 T →
    ∃ n₀, ∀ n, n₀ ≤ n → chi n t x = 1
  joint_cont : ∀ n, ContinuousOn
    (fun p : Real × M => chi n p.1 p.2) (spacetimeSlab (M := M) T)
  time_diff : ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
    DifferentiableWithinAt Real (fun s => chi n s x) (Set.Icc 0 T) t
  space_smooth : ∀ n t, t ∈ Set.Icc 0 T →
    ContMDiff I 𝓘(Real, Real) ∞ (chi n t)
  grad_sq_le : ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (chi n t) x)
        (gradientFun (I := I) (G.metric t) (chi n t) x) ≤
      err n * chi n t x
  parabolic_le : ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
    parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) (chi n) t x ≤ err n

namespace ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- The uniform spatial support produces a compact spacetime slab for each
cutoff. -/
theorem support_slab
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (n : Nat) :
    IsCompact (Set.Icc 0 T ×ˢ cut.support n) :=
  isCompact_Icc.prod (cut.support_compact n)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- A cutoff is pointwise differentiable in space on every controlled time
slice. -/
theorem space_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I 𝓘(Real, Real) (cut.chi n t) x :=
  (cut.space_smooth n t ht).mdifferentiableAt (by simp)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- The spatial gradient of a cutoff is pointwise differentiable on every
controlled time slice. -/
theorem grad_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (cut.chi n t) y) x :=
  gradientFun_mdiffAt (I := I) (G.metric t) (cut.space_smooth n t ht) x

end ShiCutoffData

/-- Pointwise Kato control for the gradients of a Bernstein tower.  For the
curvature tower this is supplied by `towerNorm_grad_le`; it is generated from
the solution and is not an HCG input. -/
def TowerNormGradUpTo
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G) (m : Nat) : Prop :=
  ∀ k : Nat, k ≤ m → ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (B.w k t) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      4 * B.w k t x * B.w (k + 1) t x

/-- Pointwise Kato control at every level of a Bernstein tower. -/
def TowerNormGradOn
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G) : Prop :=
  ∀ m : Nat, TowerNormGradUpTo (I := I) B m

namespace TowerNormGradOn

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- Restrict all-level Kato control to the levels used by a localized
Bernstein polynomial. -/
theorem upTo
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    {B : BernsteinTower (I := I) G}
    (h : TowerNormGradOn (I := I) B) (m : Nat) :
    TowerNormGradUpTo (I := I) B m :=
  h m

end TowerNormGradOn

namespace ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The cutoff-gradient cross term is absorbed by half of the next tower
level, up to the cutoff error times the current level. -/
theorem cross_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n k : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hk : k ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (cut.chi n t) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      cut.chi n t x * B.w (k + 1) t x +
        4 * cut.err n * B.w k t x := by
  let a := gradientFun (I := I) (G.metric t) (cut.chi n t) x
  let b := gradientFun (I := I) (G.metric t) (B.w k t) x
  let c := (G.metric t).inner x a b
  let p := cut.chi n t x * B.w (k + 1) t x
  let q := 4 * cut.err n * B.w k t x
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  have herr : 0 ≤ cut.err n := cut.err_nonneg n
  have hw : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
  have hnext : 0 ≤ B.w (k + 1) t x := B.hw_nonneg (k + 1) t ht x
  have ha : (G.metric t).inner x a a ≤ cut.err n * cut.chi n t x := by
    simpa [a] using cut.grad_sq_le n t ht htpos x
  have hb : (G.metric t).inner x b b ≤ 4 * B.w k t x * B.w (k + 1) t x := by
    simpa [b] using hgrad k hk t ht htpos x
  have haa : 0 ≤ (G.metric t).inner x a a :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x a
  have hbb : 0 ≤ (G.metric t).inner x b b :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x b
  have hsq : c ^ 2 ≤ p * q := by
    calc
      c ^ 2 ≤
          (G.metric t).inner x a a * (G.metric t).inner x b b := by
        exact DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x) :=
        mul_le_mul ha hb hbb (mul_nonneg herr hchi)
      _ = p * q := by simp only [p, q]; ring
  have hp : 0 ≤ p := mul_nonneg hchi hnext
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg (by norm_num) herr) hw
  have hhalf : p * q ≤ ((p + q) / 2) ^ 2 := by
    nlinarith [sq_nonneg (p - q)]
  have habs : |c| ≤ (p + q) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (p + q) / 2 := (neg_le_abs c).trans habs
  dsimp [c, p, q] at hneg ⊢
  linarith

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless] in
/-- The parabolic cutoff error of a positive natural power is controlled by
the same power with one factor removed. -/
theorem pow_parabolic_le
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (n p : Nat)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => (cut.chi n s y) ^ (p + 1)) t x ≤
      (((p + 1 : Nat) : Real) * cut.err n) * (cut.chi n t x) ^ p := by
  induction p with
  | zero =>
      simpa using cut.parabolic_le n t ht htpos x
  | succ p ih =>
      have hu_time : DifferentiableWithinAt Real
          (fun s : Real => (cut.chi n s x) ^ (p + 1)) (Set.Icc 0 T) t :=
        (cut.time_diff n t ht htpos x).pow (p + 1)
      have hv_time : DifferentiableWithinAt Real
          (fun s : Real => cut.chi n s x) (Set.Icc 0 T) t :=
        cut.time_diff n t ht htpos x
      have hu_space : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => (cut.chi n t z) ^ (p + 1)) y :=
        fun y => (cut.space_diff ht y).pow (p + 1)
      have hv_space : ∀ y : M,
          MDifferentiableAt I 𝓘(Real, Real) (cut.chi n t) y :=
        fun y => cut.space_diff ht y
      have hu_grad : ∀ y : M,
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
            gradientFun (I := I) (G.metric t)
              (fun q : M => (cut.chi n t q) ^ (p + 1)) z) y :=
        fun y => gradientFun_mdiffAt (I := I) (G.metric t)
          ((cut.space_smooth n t ht).pow (p + 1)) y
      have hv_grad : ∀ y : M,
          MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
            gradientFun (I := I) (G.metric t) (cut.chi n t) z) y :=
        fun y => cut.grad_diff ht y
      have hmul := parabolic_mul (I := I) G T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => (cut.chi n s y) ^ (p + 1)) (cut.chi n) t x
        hu_time hv_time hu_space hv_space hu_grad hv_grad
      have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
      have hgrad := gradientFun_pow (I := I) (G.metric t)
        (f := cut.chi n t) p (cut.space_diff (n := n) ht x)
      have hinner : 0 ≤ (G.metric t).inner x
          (gradientAt (I := I) G t
            (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
          (gradientAt (I := I) G t (cut.chi n t) x) := by
        simp only [gradientAt_eq, hgrad, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hchi p))
          (DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
            (I := I) (M := M) (G.metric t) x
              (gradientFun (I := I) (G.metric t) (cut.chi n t) x))
      have hcross : -2 * (G.metric t).inner x
          (gradientAt (I := I) G t
            (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
          (gradientAt (I := I) G t (cut.chi n t) x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by norm_num) hinner
      have hcut := cut.parabolic_le n t ht htpos x
      have hcut_mul := mul_le_mul_of_nonneg_left hcut (pow_nonneg hchi (p + 1))
      have hih_mul := mul_le_mul_of_nonneg_left ih hchi
      calc
        parabolicOperatorWithDrift (I := I) G T
            (fun _ y => (0 : TangentSpace I y))
            (fun s y => (cut.chi n s y) ^ (Nat.succ p + 1)) t x =
            parabolicOperatorWithDrift (I := I) G T
              (fun _ y => (0 : TangentSpace I y))
              (fun s y => (cut.chi n s y) ^ (p + 1) * cut.chi n s y) t x := by
                apply congrArg (fun u : Real → M → Real =>
                  parabolicOperatorWithDrift (I := I) G T
                    (fun _ y => (0 : TangentSpace I y)) u t x)
                funext s y
                rw [show Nat.succ p + 1 = (p + 1) + 1 by omega, pow_succ]
        _ = (cut.chi n t x) ^ (p + 1) *
              parabolicOperatorWithDrift (I := I) G T
                (fun _ y => (0 : TangentSpace I y)) (cut.chi n) t x +
            cut.chi n t x *
              parabolicOperatorWithDrift (I := I) G T
                (fun _ y => (0 : TangentSpace I y))
                (fun s y => (cut.chi n s y) ^ (p + 1)) t x -
            2 * (G.metric t).inner x
              (gradientAt (I := I) G t
                (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
              (gradientAt (I := I) G t (cut.chi n t) x) := hmul
        _ ≤ (cut.chi n t x) ^ (p + 1) * cut.err n +
            cut.chi n t x *
              ((((p + 1 : Nat) : Real) * cut.err n) *
                (cut.chi n t x) ^ p) := by
              linarith
        _ = (((Nat.succ p + 1 : Nat) : Real) * cut.err n) *
            (cut.chi n t x) ^ Nat.succ p := by
              simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ]
              ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- A cutoff-power gradient term is absorbed by half of the next tower level,
leaving an error with one fewer cutoff factor. -/
theorem pow_cross_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n k p : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hk : k ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M) :
    -2 * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t)
          (fun y : M => (cut.chi n t y) ^ (p + 1)) x)
        (gradientFun (I := I) (G.metric t) (B.w k t) x) ≤
      (1 / 2 : Real) * (cut.chi n t x) ^ (p + 1) * B.w (k + 1) t x +
        8 * (((p + 1 : Nat) : Real) ^ 2) * cut.err n *
          (cut.chi n t x) ^ p * B.w k t x := by
  let a := gradientFun (I := I) (G.metric t) (cut.chi n t) x
  let b := gradientFun (I := I) (G.metric t) (B.w k t) x
  let c₀ := (G.metric t).inner x a b
  let c := (G.metric t).inner x
    (gradientFun (I := I) (G.metric t)
      (fun y : M => (cut.chi n t y) ^ (p + 1)) x) b
  let r : Real := ((p + 1 : Nat) : Real) * (cut.chi n t x) ^ p
  let q₁ : Real := (1 / 2 : Real) * (cut.chi n t x) ^ (p + 1) * B.w (k + 1) t x
  let q₂ : Real := 8 * (((p + 1 : Nat) : Real) ^ 2) * cut.err n *
    (cut.chi n t x) ^ p * B.w k t x
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  have herr : 0 ≤ cut.err n := cut.err_nonneg n
  have hw : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
  have hnext : 0 ≤ B.w (k + 1) t x := B.hw_nonneg (k + 1) t ht x
  have ha : (G.metric t).inner x a a ≤ cut.err n * cut.chi n t x := by
    simpa [a] using cut.grad_sq_le n t ht htpos x
  have hb : (G.metric t).inner x b b ≤ 4 * B.w k t x * B.w (k + 1) t x := by
    simpa [b] using hgrad k hk t ht htpos x
  have haa : 0 ≤ (G.metric t).inner x a a :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x a
  have hbb : 0 ≤ (G.metric t).inner x b b :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) (G.metric t) x b
  have hsq₀ : c₀ ^ 2 ≤
      (cut.err n * cut.chi n t x) *
        (4 * B.w k t x * B.w (k + 1) t x) := by
    calc
      c₀ ^ 2 ≤ (G.metric t).inner x a a * (G.metric t).inner x b b := by
        exact DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
          (I := I) (M := M) (G.metric t) x a b
      _ ≤ (cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x) :=
        mul_le_mul ha hb hbb (mul_nonneg herr hchi)
  have hc : c = r * c₀ := by
    dsimp [c, r, c₀, a]
    rw [gradientFun_pow (I := I) (G.metric t)
      (f := cut.chi n t) p (cut.space_diff (n := n) ht x)]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hsq : c ^ 2 ≤ q₁ * q₂ := by
    rw [hc]
    calc
      (r * c₀) ^ 2 = r ^ 2 * c₀ ^ 2 := by ring
      _ ≤ r ^ 2 * ((cut.err n * cut.chi n t x) *
          (4 * B.w k t x * B.w (k + 1) t x)) :=
        mul_le_mul_of_nonneg_left hsq₀ hr2
      _ = q₁ * q₂ := by
        dsimp [r, q₁, q₂]
        rw [pow_succ]
        ring
  have hq₁ : 0 ≤ q₁ := by
    dsimp [q₁]
    positivity
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂]
    positivity
  have hhalf : q₁ * q₂ ≤ ((q₁ + q₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (q₁ - q₂)]
  have habs : |c| ≤ (q₁ + q₂) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans hhalf) (by positivity)
  have hneg : -c ≤ (q₁ + q₂) / 2 := (neg_le_abs c).trans habs
  dsimp [c, q₁, q₂, b] at hneg ⊢
  linarith

end ShiCutoffData

/-- The scalar coefficient of the level-`i` cutoff error in the graded
Bernstein recurrence. -/
def cutErrCoeff (i : Nat) : Real :=
  8 * (i + 1 : Real) ^ 2 + (i + 1 : Real)

/-- Graded cutoff-error coefficients are nonnegative. -/
theorem cutErrCoeff_nonneg (i : Nat) : 0 ≤ cutErrCoeff i := by
  unfold cutErrCoeff
  positivity

/-- The graded cutoff-error coefficient increases with the tower level. -/
theorem cutErrCoeff_mono : Monotone cutErrCoeff := by
  intro i j hij
  have hij' : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
  have hi : 0 ≤ (i : Real) + 1 := by positivity
  have hj : 0 ≤ (j : Real) + 1 := by positivity
  have hfac :
      0 ≤ (((j : Real) + 1) - ((i : Real) + 1)) *
        (((j : Real) + 1) + ((i : Real) + 1)) :=
    mul_nonneg (by linarith) (add_nonneg hj hi)
  unfold cutErrCoeff
  nlinarith

namespace ShiCutoffData

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] [I.Boundaryless]
  [VectorBundle Real E (TangentSpace I : M → Type _)] in
/-- For every fixed finite tower, the cutoff errors eventually satisfy the
smallness inequalities used by the graded Bernstein recurrence. -/
theorem cutErr_small
    {G : RealizedMetricFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (m : Nat) :
    ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.range (m + 1),
      cutErrCoeff i * cut.err n * T < (1 : Real) / 4 := by
  refine (Filter.eventually_all_finset (Finset.range (m + 1))).mpr ?_
  intro i hi
  have hlim : Filter.Tendsto
      (fun n ↦ cutErrCoeff i * cut.err n * T)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (cut.err_tendsto.const_mul (cutErrCoeff i)).mul_const T
  exact hlim.eventually_lt_const (by norm_num)

end ShiCutoffData

/-- The graded localized Bernstein polynomial.  Level `i` is multiplied by
`chi^(i+1)`, so every summand has compact support while cutoff errors can be
absorbed one level lower in the tower recursion. -/
noncomputable def GfunCut
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) (t : Real) (x : M) : Real :=
  ∑ i ∈ Finset.range (m + 1),
    BernsteinTower.Gcoef (I := I) B m i * t ^ i *
      (cut.chi n t x) ^ (i + 1) * B.w i t x

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded localized Bernstein polynomial is nonnegative on the controlled
time slab. -/
theorem GfunCut_nonneg
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (x : M) :
    0 ≤ GfunCut (I := I) B cut m n t x := by
  rw [GfunCut]
  apply Finset.sum_nonneg
  intro i hi
  have hchi : 0 ≤ cut.chi n t x := (cut.range n t x ht).1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (BernsteinTower.Gcoef_nonneg (I := I) B m i)
        (pow_nonneg ht.1 i))
      (pow_nonneg hchi (i + 1)))
    (B.hw_nonneg i t ht x)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded polynomial vanishes wherever the cutoff vanishes. -/
@[simp] theorem GfunCut_zero
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} {t : Real} {x : M}
    (hchi : cut.chi n t x = 0) :
    GfunCut (I := I) B cut m n t x = 0 := by
  simp [GfunCut, hchi]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded polynomial vanishes outside the spatial support of its cutoff
on the controlled time slab. -/
theorem GfunCut_off
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T)
    {x : M} (hx : x ∉ cut.support n) :
    GfunCut (I := I) B cut m n t x = 0 :=
  GfunCut_zero (I := I) B cut (cut.support_zero n t ht x hx)

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- The graded localized Bernstein polynomial is jointly continuous on its
closed spacetime slab. -/
theorem GfunCut_cont
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) :
    ContinuousOn (fun p : Real × M => GfunCut (I := I) B cut m n p.1 p.2)
      (spacetimeSlab (M := M) B.T) := by
  rw [show (fun p : Real × M => GfunCut (I := I) B cut m n p.1 p.2) =
      (fun p : Real × M => ∑ i ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m i * p.1 ^ i *
          (cut.chi n p.1 p.2) ^ (i + 1) * B.w i p.1 p.2) from by
    funext p
    rw [GfunCut]]
  apply continuousOn_finset_sum
  intro i hi
  exact (((continuous_const.mul (continuous_fst.pow i)).continuousOn.mul
    ((cut.joint_cont n).pow (i + 1))).mul (B.hw_cont i))

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
/-- On the exhausted region, the graded polynomial is the ordinary Bernstein
polynomial. -/
theorem GfunCut_one
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} {t : Real} {x : M}
    (hchi : cut.chi n t x = 1) :
    GfunCut (I := I) B cut m n t x = BernsteinTower.Gfun (I := I) B m t x := by
  simp [GfunCut, BernsteinTower.Gfun, hchi]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutWterms_nonpos
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} (hm : 1 ≤ m) {t : Real}
    (ht : t ∈ Set.Icc 0 B.T) (x : M)
    (hsmall : 2 * cut.err n * B.T * cutErrCoeff m ≤ 1) :
    let q := cut.chi n t x
    let beta := towerBeta B.c B.α (towerConst B.c B.α) m
    let barTop := towerBarTop B.c (towerConst B.c B.α) m
    (∑ k ∈ Finset.Ico 1 m, (
        BernsteinTower.Gcoef (I := I) B m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
            BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
              t ^ k * q ^ k * B.w k t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
              t ^ (k - 1) * q ^ k * B.w k t x)) +
      (BernsteinTower.Gcoef (I := I) B m m *
              ((m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x) +
            BernsteinTower.Gcoef (I := I) B m m * cutErrCoeff m * cut.err n *
              t ^ m * q ^ m * B.w m t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (m - 1) *
              t ^ (m - 1) * q ^ m * B.w m t x +
            barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)) ≤ 0 := by
  classical
  dsimp only
  set q : Real := cut.chi n t x with hq
  set beta : Real := towerBeta B.c B.α (towerConst B.c B.α) m with hbeta
  set barTop : Real := towerBarTop B.c (towerConst B.c B.α) m with hbarTop
  have hq0 : 0 ≤ q := by simpa [q] using (cut.range n t x ht).1
  have hq1 : q ≤ 1 := by simpa [q] using (cut.range n t x ht).2
  have ht0 : 0 ≤ t := ht.1
  have hT0 : 0 ≤ B.T := le_trans ht.1 ht.2
  have he0 : 0 ≤ cut.err n := cut.err_nonneg n
  have hbeta0 : 0 ≤ beta := by
    simpa [beta] using towerBeta_nonneg B.hc B.hα m
  have hbarTop0 : 0 ≤ barTop := by
    simpa [barTop] using towerBarTop_nonneg B.hc B.α m
  have hKt : t * B.K ≤ B.α := by
    have htT : t ≤ B.T := ht.2
    have htle : t ≤ B.α / B.K := htT.trans B.hTK
    calc
      t * B.K ≤ (B.α / B.K) * B.K :=
        mul_le_mul_of_nonneg_right htle (le_of_lt B.hK)
      _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
  have herr_le (k : Nat) (hk : k ≤ m) :
      cut.err n * cutErrCoeff k * t ≤ (1 / 2 : Real) := by
    have hck : cutErrCoeff k ≤ cutErrCoeff m := cutErrCoeff_mono hk
    have hprod : 2 * cut.err n * t * cutErrCoeff k ≤
        2 * cut.err n * B.T * cutErrCoeff m := by
      have htprod : cut.err n * t ≤ cut.err n * B.T :=
        mul_le_mul_of_nonneg_left ht.2 he0
      have hleft0 : 0 ≤ 2 * cut.err n * t := by positivity
      have hmid0 : 0 ≤ 2 * cut.err n * B.T := by positivity
      calc
        2 * cut.err n * t * cutErrCoeff k ≤
            2 * cut.err n * t * cutErrCoeff m :=
          mul_le_mul_of_nonneg_left hck hleft0
        _ ≤ 2 * cut.err n * B.T * cutErrCoeff m :=
          mul_le_mul_of_nonneg_right (by linarith) (cutErrCoeff_nonneg m)
    nlinarith [hprod.trans hsmall]
  have hmid : ∀ k ∈ Finset.Ico 1 m,
      BernsteinTower.Gcoef (I := I) B m k *
            ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
          BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
            t ^ k * q ^ k * B.w k t x -
          (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
            t ^ (k - 1) * q ^ k * B.w k t x ≤ 0 := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkm : k < m := hk.2
    have hkle : k ≤ m := hkm.le
    have hGk : BernsteinTower.Gcoef (I := I) B m k =
        beta * towerFactCoeff m k := by
      rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ k = m)]
    have hfac : (k : Real) * towerFactCoeff m k =
        towerFactCoeff m (k - 1) :=
      nat_mul_towerFactCoeff m hk1
    have hG0 : 0 ≤ BernsteinTower.Gcoef (I := I) B m k :=
      BernsteinTower.Gcoef_nonneg (I := I) B m k
    have hw0 : 0 ≤ B.w k t x := B.hw_nonneg k t ht x
    have hz0 : 0 ≤ t ^ (k - 1) * q ^ k * B.w k t x := by positivity
    have hqpow : q ^ (k + 1) ≤ q ^ k := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hq0 k) hq1
    have htime :
        BernsteinTower.Gcoef (I := I) B m k *
            ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) ≤
          beta * towerFactCoeff m (k - 1) *
            (t ^ (k - 1) * q ^ k * B.w k t x) := by
      rw [hGk]
      have hpowmul : t ^ (k - 1) * q ^ (k + 1) * B.w k t x ≤
          t ^ (k - 1) * q ^ k * B.w k t x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqpow (pow_nonneg ht0 (k - 1))) hw0
      calc
        beta * towerFactCoeff m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) =
            (beta * ((k : Real) * towerFactCoeff m k)) *
              (t ^ (k - 1) * q ^ (k + 1) * B.w k t x) := by ring
        _ = (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ (k + 1) * B.w k t x) := by rw [hfac]
        _ ≤ (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) :=
          mul_le_mul_of_nonneg_left hpowmul
            (mul_nonneg hbeta0 (towerFactCoeff_nonneg _ _))
    have hGprev : BernsteinTower.Gcoef (I := I) B m k ≤
        beta * towerFactCoeff m (k - 1) := by
      rw [hGk, ← hfac]
      have hfact0 : 0 ≤ towerFactCoeff m k := towerFactCoeff_nonneg _ _
      apply mul_le_mul_of_nonneg_left _ hbeta0
      calc
        towerFactCoeff m k = 1 * towerFactCoeff m k := by ring
        _ ≤ (k : Real) * towerFactCoeff m k :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hfact0
    have herr :
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
              t ^ k * q ^ k * B.w k t x ≤
          (1 / 2 : Real) * (beta * towerFactCoeff m (k - 1)) *
            (t ^ (k - 1) * q ^ k * B.w k t x) := by
      have htk : t ^ k = t * t ^ (k - 1) := by
        calc
          t ^ k = t ^ ((k - 1) + 1) := by
            congr 1
            omega
          _ = t * t ^ (k - 1) := pow_succ' t (k - 1)
      rw [htk]
      have he : cut.err n * cutErrCoeff k * t ≤ (1 / 2 : Real) :=
        herr_le k hkle
      calc
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
              (t * t ^ (k - 1)) * q ^ k * B.w k t x =
            (BernsteinTower.Gcoef (I := I) B m k *
              (cut.err n * cutErrCoeff k * t)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by ring
        _ ≤ (BernsteinTower.Gcoef (I := I) B m k * (1 / 2 : Real)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he hG0) hz0
        _ ≤ ((beta * towerFactCoeff m (k - 1)) * (1 / 2 : Real)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGprev (by norm_num)) hz0
        _ = (1 / 2 : Real) * (beta * towerFactCoeff m (k - 1)) *
              (t ^ (k - 1) * q ^ k * B.w k t x) := by ring
    linarith
  have hmidsum :
      (∑ k ∈ Finset.Ico 1 m, (
        BernsteinTower.Gcoef (I := I) B m k *
              ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x) +
            BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
              t ^ k * q ^ k * B.w k t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (k - 1) *
              t ^ (k - 1) * q ^ k * B.w k t x)) ≤ 0 :=
    Finset.sum_nonpos hmid
  have hGm : BernsteinTower.Gcoef (I := I) B m m = 1 := by
    rw [BernsteinTower.Gcoef]
    simp
  have hfactm : towerFactCoeff m (m - 1) = 1 := by
    rw [towerFactCoeff]
    rw [div_self (by exact_mod_cast (Nat.factorial_pos (m - 1)).ne')]
  have hwm0 : 0 ≤ B.w m t x := B.hw_nonneg m t ht x
  have hz0 : 0 ≤ t ^ (m - 1) * q ^ m * B.w m t x := by positivity
  have hqpow : q ^ (m + 1) ≤ q ^ m := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hq0 m) hq1
  have htimeTop :
      (m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x ≤
        (m : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow (pow_nonneg ht0 (m - 1))) hwm0)
      (Nat.cast_nonneg m)
  have herrTop :
      cutErrCoeff m * cut.err n * t ^ m * q ^ m * B.w m t x ≤
        (1 / 2 : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    have htm : t ^ m = t * t ^ (m - 1) := by
      calc
        t ^ m = t ^ ((m - 1) + 1) := by
          congr 1
          omega
        _ = t * t ^ (m - 1) := pow_succ' t (m - 1)
    rw [htm]
    have he : cut.err n * cutErrCoeff m * t ≤ (1 / 2 : Real) :=
      herr_le m le_rfl
    calc
      cutErrCoeff m * cut.err n * (t * t ^ (m - 1)) * q ^ m * B.w m t x =
          (cut.err n * cutErrCoeff m * t) *
            (t ^ (m - 1) * q ^ m * B.w m t x) := by ring
      _ ≤ (1 / 2 : Real) * (t ^ (m - 1) * q ^ m * B.w m t x) :=
        mul_le_mul_of_nonneg_right he hz0
  have hreactTop :
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) ≤
        (barTop * B.α) * (t ^ (m - 1) * q ^ m * B.w m t x) := by
    have htm : t ^ m = t * t ^ (m - 1) := by
      calc
        t ^ m = t ^ ((m - 1) + 1) := by
          congr 1
          omega
        _ = t * t ^ (m - 1) := pow_succ' t (m - 1)
    rw [htm]
    have hKtq : B.K * t * q ≤ B.α := by
      have hKt' : B.K * t ≤ B.α := by simpa [mul_comm] using hKt
      calc
        B.K * t * q ≤ B.K * t * 1 :=
          mul_le_mul_of_nonneg_left hq1 (mul_nonneg (le_of_lt B.hK) ht0)
        _ = B.K * t := by ring
        _ ≤ B.α := hKt'
    calc
      barTop * B.K * ((t * t ^ (m - 1)) * q ^ (m + 1) * B.w m t x) =
          (barTop * (B.K * t * q)) *
            (t ^ (m - 1) * q ^ m * B.w m t x) := by
        rw [pow_succ]
        ring
      _ ≤ (barTop * B.α) *
            (t ^ (m - 1) * q ^ m * B.w m t x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKtq hbarTop0) hz0
  have hbetaEq : beta = barTop * B.α + (m : Real) := by
    rw [hbeta, towerBeta, ← hbarTop]
  have htop :
      BernsteinTower.Gcoef (I := I) B m m *
              ((m : Real) * t ^ (m - 1) * q ^ (m + 1) * B.w m t x) +
            BernsteinTower.Gcoef (I := I) B m m * cutErrCoeff m * cut.err n *
              t ^ m * q ^ m * B.w m t x -
            (3 / 2 : Real) * beta * towerFactCoeff m (m - 1) *
              t ^ (m - 1) * q ^ m * B.w m t x +
            barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) ≤ 0 := by
    rw [hGm, hfactm, one_mul, one_mul]
    have hcoef :
        (m : Real) + (1 / 2 : Real) - (3 / 2 : Real) * beta +
            barTop * B.α ≤ 0 := by
      rw [hbetaEq]
      have hm1 : (1 : Real) ≤ (m : Real) := by exact_mod_cast hm
      nlinarith [hbarTop0, B.hα]
    nlinarith [htimeTop, herrTop, hreactTop, mul_nonpos_of_nonpos_of_nonneg hcoef hz0]
  linarith

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutWsum_nonpos
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} (hm : 1 ≤ m) {t : Real}
    (ht : t ∈ Set.Icc 0 B.T) (x : M)
    (hsmall : 2 * cut.err n * B.T * cutErrCoeff m ≤ 1) :
    let q := cut.chi n t x
    let beta := towerBeta B.c B.α (towerConst B.c B.α) m
    let barTop := towerBarTop B.c (towerConst B.c B.α) m
    (∑ k ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m k *
          ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x)) -
      (3 / 2 : Real) * beta *
        (∑ k ∈ Finset.range m,
          towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) +
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) +
      (∑ k ∈ Finset.range (m + 1),
        BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
          t ^ k * q ^ k * B.w k t x) ≤
        BernsteinTower.Gcoef (I := I) B m 0 * cutErrCoeff 0 * cut.err n *
          B.w 0 t x := by
  classical
  dsimp only
  set q : Real := cut.chi n t x with hq
  set beta : Real := towerBeta B.c B.α (towerConst B.c B.α) m with hbeta
  set barTop : Real := towerBarTop B.c (towerConst B.c B.α) m with hbarTop
  have hcore := cutWterms_nonpos (I := I) B cut hm ht x hsmall
  dsimp only at hcore
  rw [← hq, ← hbeta, ← hbarTop] at hcore
  let timeTerm : Nat → Real := fun k =>
    BernsteinTower.Gcoef (I := I) B m k *
      ((k : Real) * t ^ (k - 1) * q ^ (k + 1) * B.w k t x)
  let errTerm : Nat → Real := fun k =>
    BernsteinTower.Gcoef (I := I) B m k * cutErrCoeff k * cut.err n *
      t ^ k * q ^ k * B.w k t x
  let negTerm : Nat → Real := fun k =>
    towerFactCoeff m (k - 1) * t ^ (k - 1) * q ^ k * B.w k t x
  have hcore' :
      (∑ k ∈ Finset.Ico 1 m, timeTerm k) +
          (∑ k ∈ Finset.Ico 1 m, errTerm k) -
          (3 / 2 : Real) * beta * (∑ k ∈ Finset.Ico 1 m, negTerm k) +
        (timeTerm m + errTerm m - (3 / 2 : Real) * beta * negTerm m +
          barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hcore
    simpa only [timeTerm, errTerm, negTerm, Finset.mul_sum, mul_assoc] using hcore
  have htime :
      (∑ k ∈ Finset.range (m + 1), timeTerm k) =
        (∑ k ∈ Finset.Ico 1 m, timeTerm k) + timeTerm m := by
    rw [BernsteinTower.sum_range_succ_split timeTerm hm]
    have hzero : timeTerm 0 = 0 := by simp [timeTerm]
    rw [hzero, zero_add]
  have herr :
      (∑ k ∈ Finset.range (m + 1), errTerm k) =
        errTerm 0 + (∑ k ∈ Finset.Ico 1 m, errTerm k) + errTerm m :=
    BernsteinTower.sum_range_succ_split errTerm hm
  have hnegIcc :
      (∑ k ∈ Finset.range m,
        towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) =
        ∑ k ∈ Finset.Icc 1 m, negTerm k := by
    have hIcc : Finset.Ico 1 (m + 1) = Finset.Icc 1 m := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [← hIcc, Finset.sum_Ico_eq_sum_range]
    rw [show m + 1 - 1 = m by omega]
    apply Finset.sum_congr rfl
    intro k _
    simp only [negTerm]
    rw [show 1 + k - 1 = k by omega, show 1 + k = k + 1 by omega]
  have hmIcc : m ∈ Finset.Icc 1 m := by
    simp only [Finset.mem_Icc]
    omega
  have herase : (Finset.Icc 1 m).erase m = Finset.Ico 1 m := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hneg :
      (∑ k ∈ Finset.range m,
        towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) =
        (∑ k ∈ Finset.Ico 1 m, negTerm k) + negTerm m := by
    rw [hnegIcc, ← Finset.sum_erase_add _ _ hmIcc, herase]
  have herr0 : errTerm 0 =
      BernsteinTower.Gcoef (I := I) B m 0 * cutErrCoeff 0 * cut.err n *
        B.w 0 t x := by
    simp [errTerm]
  rw [← herr0]
  change (∑ k ∈ Finset.range (m + 1), timeTerm k) -
      (3 / 2 : Real) * beta *
        (∑ k ∈ Finset.range m,
          towerFactCoeff m k * t ^ k * q ^ (k + 1) * B.w (k + 1) t x) +
      barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x) +
      (∑ k ∈ Finset.range (m + 1), errTerm k) ≤ errTerm 0
  rw [htime, herr, hneg]
  convert add_le_add_right hcore' (errTerm 0) using 1 <;> ring

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem cutLevel_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n i : Nat} (hgrad : TowerNormGradUpTo (I := I) B m) (hi : i ≤ m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M)
    (d : Real)
    (hd : HasDerivWithinAt (fun s : Real => B.w i s x) d (Set.Icc 0 B.T) t)
    (hheat : d - B.wLap i t x ≤
      -2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x) :
    parabolicOperatorWithDrift (I := I) G B.T
        (fun _ y => (0 : TangentSpace I y))
        (fun s y => BernsteinTower.Gcoef (I := I) B m i *
          (s ^ i * (cut.chi n s y) ^ (i + 1) * B.w i s y)) t x ≤
      BernsteinTower.Gcoef (I := I) B m i *
        ((cut.chi n t x) ^ (i + 1) *
            ((i : Real) * t ^ (i - 1) * B.w i t x +
              t ^ i * (-2 * B.w (i + 1) t x +
                towerReactionSum (M := M) B.w B.c i t x)) +
          (1 / 2 : Real) * t ^ i * (cut.chi n t x) ^ (i + 1) *
            B.w (i + 1) t x +
          cutErrCoeff i * cut.err n * t ^ i * (cut.chi n t x) ^ i *
            B.w i t x) := by
  let qpow : Real → M → Real := fun s y => (cut.chi n s y) ^ (i + 1)
  let v : Real → M → Real := fun s y => s ^ i * B.w i s y
  have hq_time : DifferentiableWithinAt Real
      (fun s : Real => qpow s x) (Set.Icc 0 B.T) t := by
    simpa [qpow] using (cut.time_diff n t ht htpos x).pow (i + 1)
  have hv_time : DifferentiableWithinAt Real
      (fun s : Real => v s x) (Set.Icc 0 B.T) t := by
    exact (((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).mul hd).differentiableWithinAt
  have hq_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (qpow t) y := by
    intro y
    simpa [qpow] using (cut.space_diff ht y).pow (i + 1)
  have hv_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) y := by
    intro y
    have h := (B.hw_space i t ht htpos y).const_smul (t ^ i)
    simpa [v, smul_eq_mul] using h
  have hq_grad : ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (qpow t) z) y := by
    intro y
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      ((cut.space_smooth n t ht).pow (i + 1)) y
  have hv_grad : ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t) (v t) z) y := by
    intro y
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (B.w i t) z) := by
      funext z
      rw [show v t = t ^ i • B.w i t by
        funext w
        simp [v, smul_eq_mul]]
      exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
        (B.hw_space i t ht htpos z)
    have hsection :
        (T% fun z : M => gradientFun (I := I) (G.metric t) (v t) z) =
          (T% (t ^ i • fun z : M =>
            gradientFun (I := I) (G.metric t) (B.w i t) z)) := by
      funext z
      simpa using congrFun hplain z
    rw [hsection]
    exact (B.hw_grad i t ht htpos y).smul_const_section (a := t ^ i)
  have hprod_grad : ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M =>
        gradientFun (I := I) (G.metric t)
          (fun w : M => qpow t w * v t w) z) y := by
    intro y
    have hplain :
        (fun z : M => gradientFun (I := I) (G.metric t)
          (fun w : M => qpow t w * v t w) z) =
        (fun z : M => qpow t z •
            gradientFun (I := I) (G.metric t) (v t) z +
          v t z • gradientFun (I := I) (G.metric t) (qpow t) z) := by
      funext z
      exact gradientFun_mul (I := I) (G.metric t) (hq_space z) (hv_space z)
    have hsection :
        (T% fun z : M => gradientFun (I := I) (G.metric t)
          (fun w : M => qpow t w * v t w) z) =
        (T% fun z : M => qpow t z •
            gradientFun (I := I) (G.metric t) (v t) z +
          v t z • gradientFun (I := I) (G.metric t) (qpow t) z) := by
      funext z
      simpa using congrFun hplain z
    rw [hsection]
    exact mdifferentiableAt_add_section
      ((hq_space y).smul_section (hv_grad y))
      ((hv_space y).smul_section (hq_grad y))
  have hv_parabolic :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) v t x =
        (i : Real) * t ^ (i - 1) * B.w i t x +
          t ^ i * (d - B.wLap i t x) := by
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) t :=
      (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt ht
    have htime : derivWithin (fun s : Real => v s x) (Set.Icc 0 B.T) t =
        (i : Real) * t ^ (i - 1) * B.w i t x + t ^ i * d := by
      simpa [v] using
        (((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).mul hd).derivWithin huniq
    have hheat : heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) (v t) x =
        t ^ i * B.wLap i t x := by
      have hscale := heatOperatorWithDrift_const_smul
        (I := I) G t (fun y : M => (0 : TangentSpace I y)) (t ^ i)
        (B.hw_space i t ht htpos) (B.hw_grad i t ht htpos x)
      rw [show v t = t ^ i • B.w i t by
        funext y
        simp [v, smul_eq_mul]]
      rw [hscale, B.hLap i t ht htpos x]
    rw [parabolicOperatorWithDrift_eq, htime, hheat]
    ring
  have hv_gradient : gradientAt (I := I) G t (v t) x =
      t ^ i • gradientAt (I := I) G t (B.w i t) x := by
    unfold gradientAt
    rw [show v t = t ^ i • B.w i t by
      funext y
      simp [v, smul_eq_mul]]
    exact gradientFun_const_smul (I := I) (G.metric t) (t ^ i)
      (B.hw_space i t ht htpos x)
  have hmul := parabolic_mul (I := I) G B.T
    (fun _ y => (0 : TangentSpace I y)) qpow v t x
    hq_time hv_time hq_space hv_space hq_grad hv_grad
  have hscale := parabolic_smul (I := I) G B.T
    (fun _ y => (0 : TangentSpace I y))
    (BernsteinTower.Gcoef (I := I) B m i)
    (fun s y => qpow s y * v s y) t x
    (hq_time.mul hv_time)
    (fun y => (hq_space y).mul (hv_space y)) (hprod_grad x)
  have hq_bound := cut.pow_parabolic_le n i ht htpos x
  have hcross := cut.pow_cross_le B (m := m) (n := n) (k := i) (p := i)
    hgrad hi ht htpos x
  have hcoef0 : 0 ≤ BernsteinTower.Gcoef (I := I) B m i :=
    BernsteinTower.Gcoef_nonneg (I := I) B m i
  have hti0 : 0 ≤ t ^ i := pow_nonneg ht.1 i
  have hwi0 : 0 ≤ B.w i t x := B.hw_nonneg i t ht x
  have hq_term :
      v t x * parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) qpow t x ≤
        (((i + 1 : Nat) : Real) * cut.err n) *
          t ^ i * (cut.chi n t x) ^ i * B.w i t x := by
    have hmult := mul_le_mul_of_nonneg_left hq_bound
      (mul_nonneg hti0 hwi0)
    dsimp [qpow, v]
    convert hmult using 1
    ring
  have hcross_term :
      -2 * (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (v t) x) ≤
        (1 / 2 : Real) * t ^ i * (cut.chi n t x) ^ (i + 1) *
            B.w (i + 1) t x +
          8 * (((i + 1 : Nat) : Real) ^ 2) * cut.err n * t ^ i *
            (cut.chi n t x) ^ i * B.w i t x := by
    rw [hv_gradient]
    simp only [map_smul, smul_eq_mul]
    have hmult := mul_le_mul_of_nonneg_left hcross hti0
    dsimp [qpow]
    unfold gradientAt
    convert hmult using 1 <;> ring
  rw [show (fun s y => BernsteinTower.Gcoef (I := I) B m i *
        (s ^ i * (cut.chi n s y) ^ (i + 1) * B.w i s y)) =
      (fun s y => BernsteinTower.Gcoef (I := I) B m i *
        (qpow s y * v s y)) by
      funext s y
      dsimp [qpow, v]
      ring]
  rw [hscale, hmul, hv_parabolic]
  have hheat_mul :
      (cut.chi n t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) ≤
        (cut.chi n t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (-2 * B.w (i + 1) t x +
              towerReactionSum (M := M) B.w B.c i t x)) := by
    apply mul_le_mul_of_nonneg_left _
      (pow_nonneg (cut.range n t x ht).1 (i + 1))
    linarith [mul_le_mul_of_nonneg_left hheat hti0]
  apply mul_le_mul_of_nonneg_left _ hcoef0
  calc
    qpow t x *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) +
        v t x * parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y => (0 : TangentSpace I y)) qpow t x -
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t (qpow t) x)
          (gradientAt (I := I) G t (v t) x) ≤
      (cut.chi n t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (d - B.wLap i t x)) +
        (((i + 1 : Nat) : Real) * cut.err n) * t ^ i *
          (cut.chi n t x) ^ i * B.w i t x +
        ((1 / 2 : Real) * t ^ i * (cut.chi n t x) ^ (i + 1) *
            B.w (i + 1) t x +
          8 * (((i + 1 : Nat) : Real) ^ 2) * cut.err n * t ^ i *
            (cut.chi n t x) ^ i * B.w i t x) := by
      dsimp [qpow, v]
      linarith
    _ ≤ (cut.chi n t x) ^ (i + 1) *
          ((i : Real) * t ^ (i - 1) * B.w i t x +
            t ^ i * (-2 * B.w (i + 1) t x +
              towerReactionSum (M := M) B.w B.c i t x)) +
        (1 / 2 : Real) * t ^ i * (cut.chi n t x) ^ (i + 1) *
          B.w (i + 1) t x +
        cutErrCoeff i * cut.err n * t ^ i * (cut.chi n t x) ^ i *
          B.w i t x := by
      rw [cutErrCoeff]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hheat_mul]

omit [NeZero (Module.finrank Real E)] in
/-- The graded localized Bernstein polynomial satisfies the closed pointwise
parabolic recurrence.  All positive-level cutoff errors telescope into the
retained next-level dissipation; only the base curvature error remains. -/
theorem GfunCut_parabolic_le
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    {m n : Nat} (hm : 1 ≤ m)
    (hgrad : TowerNormGradUpTo (I := I) B m)
    {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t) (x : M)
    (hIH : ∀ j, j < m →
      t ^ j * B.w j t x ≤ (towerConst B.c B.α j) ^ 2 * B.K ^ 2)
    (hsmall : 2 * cut.err n * B.T * cutErrCoeff m ≤ 1) :
    parabolicOperatorWithDrift (I := I) G B.T
        (fun _ y ↦ (0 : TangentSpace I y))
        (GfunCut (I := I) B cut m n) t x ≤
      (towerBarTop B.c (towerConst B.c B.α) m +
          towerBeta B.c B.α (towerConst B.c B.α) m *
            ∑ i ∈ Finset.range m,
              towerFactCoeff m i *
                towerBarGood B.c (towerConst B.c B.α) i) * B.K ^ 3 +
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := by
  classical
  set q : Real := cut.chi n t x with hq
  set C : Nat → Real := towerConst B.c B.α with hC
  set beta : Real := towerBeta B.c B.α C m with hbeta
  set barTop : Real := towerBarTop B.c C m with hbarTop
  have hq0 : 0 ≤ q := by simpa only [hq] using (cut.range n t x ht).1
  have hq1 : q ≤ 1 := by simpa only [hq] using (cut.range n t x ht).2
  have hqpow_le : ∀ k : Nat, q ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        calc
          q ^ k * q ≤ q ^ k * 1 :=
            mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 k)
          _ = q ^ k := mul_one _
          _ ≤ 1 := ih
  have hbeta0 : 0 ≤ beta := by
    simpa only [hbeta, hC] using towerBeta_nonneg B.hc B.hα m
  have hbarTop0 : 0 ≤ barTop := by
    simpa only [hbarTop, hC] using towerBarTop_nonneg B.hc B.α m
  let tau : RealTimeInterval.RegularTime B.D :=
    ⟨t, B.hregular t ht htpos⟩
  set dvec : Nat → Real := fun i ↦ Classical.choose (B.hheat i tau x) with hdvec
  have hspec : ∀ i : Nat,
      HasDerivWithinAt (fun r : Real ↦ B.w i r x) (dvec i) B.D.carrier t ∧
      dvec i ≤ B.wLap i t x +
        (-2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x) := by
    intro i
    have h := Classical.choose_spec (B.hheat i tau x)
    simpa only [hdvec, tau] using h
  have hd : ∀ i : Nat,
      HasDerivWithinAt (fun r : Real ↦ B.w i r x) (dvec i) (Set.Icc 0 B.T) t :=
    fun i ↦ (hspec i).1.mono B.hslab
  let term : Nat → Real → M → Real := fun i s y ↦
    BernsteinTower.Gcoef (I := I) B m i *
      (s ^ i * (cut.chi n s y) ^ (i + 1) * B.w i s y)
  have htime : ∀ i ∈ Finset.range (m + 1),
      DifferentiableWithinAt Real (fun s : Real ↦ term i s x) (Set.Icc 0 B.T) t := by
    intro i _
    have hprod :=
      ((((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).differentiableWithinAt.mul
        ((cut.time_diff n t ht htpos x).pow (i + 1))).mul
          (hd i).differentiableWithinAt)
    simpa only [term, mul_assoc] using
      hprod.const_mul (BernsteinTower.Gcoef (I := I) B m i)
  have hspace : ∀ i ∈ Finset.range (m + 1), ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (term i t) y := by
    intro i _ y
    have hprod := ((cut.space_diff (n := n) ht y).pow (i + 1)).mul
      (B.hw_space i t ht htpos y)
    have hscaled := hprod.const_smul
      (BernsteinTower.Gcoef (I := I) B m i * t ^ i)
    change MDifferentiableAt I 𝓘(Real, Real)
      (fun z : M ↦ (BernsteinTower.Gcoef (I := I) B m i * t ^ i) *
        ((cut.chi n t z) ^ (i + 1) * B.w i t z)) y at hscaled
    simpa only [term, mul_assoc] using hscaled
  have hgradTerm : ∀ i ∈ Finset.range (m + 1), ∀ y : M,
      MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
        gradientFun (I := I) (G.metric t) (term i t) z) y := by
    intro i _ y
    let qpow : M → Real := fun z ↦ (cut.chi n t z) ^ (i + 1)
    let wi : M → Real := B.w i t
    have hq_space : ∀ z : M, MDifferentiableAt I 𝓘(Real, Real) qpow z := by
      intro z
      simpa only [qpow] using (cut.space_diff (n := n) ht z).pow (i + 1)
    have hw_space : ∀ z : M, MDifferentiableAt I 𝓘(Real, Real) wi z := by
      intro z
      simpa only [wi] using B.hw_space i t ht htpos z
    have hq_grad : ∀ z : M,
        MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun w : M ↦
        gradientFun (I := I) (G.metric t) qpow w) z := by
      intro z
      exact gradientFun_mdiffAt (I := I) (G.metric t)
        ((cut.space_smooth n t ht).pow (i + 1)) z
    have hw_grad : ∀ z : M,
        MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun w : M ↦
        gradientFun (I := I) (G.metric t) wi w) z := by
      intro z
      simpa only [wi] using B.hw_grad i t ht htpos z
    have hprod_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
        gradientFun (I := I) (G.metric t) (fun w ↦ qpow w * wi w) z) y := by
      have hplain :
          (fun z : M ↦ gradientFun (I := I) (G.metric t)
            (fun w ↦ qpow w * wi w) z) =
            (fun z : M ↦ qpow z • gradientFun (I := I) (G.metric t) wi z +
              wi z • gradientFun (I := I) (G.metric t) qpow z) := by
        funext z
        exact gradientFun_mul (I := I) (G.metric t) (hq_space z) (hw_space z)
      rw [show (T% fun z : M ↦ gradientFun (I := I) (G.metric t)
          (fun w ↦ qpow w * wi w) z) =
          (T% fun z : M ↦ qpow z • gradientFun (I := I) (G.metric t) wi z +
            wi z • gradientFun (I := I) (G.metric t) qpow z) by
        funext z
        simpa using congrFun hplain z]
      exact mdifferentiableAt_add_section
        ((hq_space y).smul_section (hw_grad y))
        ((hw_space y).smul_section (hq_grad y))
    have hterm : term i t =
        (BernsteinTower.Gcoef (I := I) B m i * t ^ i) •
          (fun z : M ↦ qpow z * wi z) := by
      funext z
      simp only [term, qpow, wi, Pi.smul_apply, smul_eq_mul]
      ring
    have hplain :
        (fun z : M ↦ gradientFun (I := I) (G.metric t) (term i t) z) =
          (BernsteinTower.Gcoef (I := I) B m i * t ^ i) •
            (fun z : M ↦ gradientFun (I := I) (G.metric t)
              (fun w ↦ qpow w * wi w) z) := by
      funext z
      rw [hterm]
      exact gradientFun_const_smul (I := I) (G.metric t)
        (BernsteinTower.Gcoef (I := I) B m i * t ^ i)
        ((hq_space z).mul (hw_space z))
    rw [show (T% fun z : M ↦
        gradientFun (I := I) (G.metric t) (term i t) z) =
        (T% ((BernsteinTower.Gcoef (I := I) B m i * t ^ i) •
          fun z : M ↦ gradientFun (I := I) (G.metric t)
            (fun w ↦ qpow w * wi w) z)) by
      funext z
      simpa using congrFun hplain z]
    exact hprod_grad.smul_const_section
      (a := BernsteinTower.Gcoef (I := I) B m i * t ^ i)
  have hsum :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y))
          (GfunCut (I := I) B cut m n) t x =
        ∑ i ∈ Finset.range (m + 1),
          parabolicOperatorWithDrift (I := I) G B.T
            (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x := by
    rw [show GfunCut (I := I) B cut m n =
        (fun s y ↦ ∑ i ∈ Finset.range (m + 1), term i s y) by
      funext s y
      rw [GfunCut]
      apply Finset.sum_congr rfl
      intro i _
      simp only [term]
      ring]
    exact parabolic_sum (I := I) (Finset.range (m + 1)) G B.T
      (fun _ y ↦ (0 : TangentSpace I y)) term t x htime hspace hgradTerm
  have hlevel : ∀ i ∈ Finset.range (m + 1),
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x ≤
        BernsteinTower.Gcoef (I := I) B m i *
          (q ^ (i + 1) *
              ((i : Real) * t ^ (i - 1) * B.w i t x +
                t ^ i * (-2 * B.w (i + 1) t x +
                  towerReactionSum (M := M) B.w B.c i t x)) +
            (1 / 2 : Real) * t ^ i * q ^ (i + 1) * B.w (i + 1) t x +
            cutErrCoeff i * cut.err n * t ^ i * q ^ i * B.w i t x) := by
    intro i hi
    have him : i ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
    have hheat : dvec i - B.wLap i t x ≤
        -2 * B.w (i + 1) t x + towerReactionSum (M := M) B.w B.c i t x := by
      linarith [(hspec i).2]
    simpa only [term, hq] using
      cutLevel_le (I := I) B cut hgrad him ht htpos x (dvec i) (hd i) hheat
  let timeTerm : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i *
      ((i : Real) * t ^ (i - 1) * q ^ (i + 1) * B.w i t x)
  let negTerm : Nat → Real := fun i ↦
    (3 / 2 : Real) * beta * towerFactCoeff m i * t ^ i * q ^ (i + 1) *
      B.w (i + 1) t x
  let errTerm : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i * cutErrCoeff i * cut.err n *
      t ^ i * q ^ i * B.w i t x
  let forceTerm : Nat → Real := fun i ↦
    beta * towerFactCoeff m i * towerBarGood B.c C i * B.K ^ 3
  let lowerBound : Nat → Real := fun i ↦
    timeTerm i - negTerm i + errTerm i + forceTerm i
  let topNeg : Real := (3 / 2 : Real) * t ^ m * q ^ (m + 1) * B.w (m + 1) t x
  let topSpace : Real := barTop * B.K * (t ^ m * q ^ (m + 1) * B.w m t x)
  let topBound : Real :=
    timeTerm m - topNeg + topSpace + barTop * B.K ^ 3 + errTerm m
  have hlower : ∀ i ∈ Finset.range m,
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x ≤ lowerBound i := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hGi : BernsteinTower.Gcoef (I := I) B m i =
        beta * towerFactCoeff m i := by
      rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ i = m), hbeta, hC]
    have hR := BernsteinTower.tpow_mul_reactionSum_le (I := I) B i htpos
      (fun j hj ↦ hIH j (lt_of_le_of_lt hj him))
    rw [← hC] at hR
    have hforce0 : 0 ≤ towerBarGood B.c C i * B.K ^ 3 :=
      mul_nonneg (by simpa only [hC] using towerBarGood_nonneg B.hc B.α i)
        (pow_nonneg (le_of_lt B.hK) 3)
    have hRq : q ^ (i + 1) *
        (t ^ i * towerReactionSum (M := M) B.w B.c i t x) ≤
          towerBarGood B.c C i * B.K ^ 3 := by
      calc
        q ^ (i + 1) * (t ^ i * towerReactionSum (M := M) B.w B.c i t x) ≤
            q ^ (i + 1) * (towerBarGood B.c C i * B.K ^ 3) :=
          mul_le_mul_of_nonneg_left hR (pow_nonneg hq0 (i + 1))
        _ ≤ 1 * (towerBarGood B.c C i * B.K ^ 3) :=
          mul_le_mul_of_nonneg_right (hqpow_le (i + 1)) hforce0
        _ = towerBarGood B.c C i * B.K ^ 3 := one_mul _
    have hcoef0 : 0 ≤ beta * towerFactCoeff m i :=
      mul_nonneg hbeta0 (towerFactCoeff_nonneg _ _)
    have hRqcoef := mul_le_mul_of_nonneg_left hRq hcoef0
    have hraw := hlevel i (Finset.mem_range.mpr (lt_trans him (Nat.lt_succ_self m)))
    rw [hGi] at hraw
    dsimp only [lowerBound, timeTerm, negTerm, errTerm, forceTerm]
    rw [hGi]
    nlinarith [hRqcoef]
  have htop :
      parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term m) t x ≤ topBound := by
    have hGm : BernsteinTower.Gcoef (I := I) B m m = 1 := by
      rw [BernsteinTower.Gcoef]
      simp
    have hreact := BernsteinTower.reactionSum_top_le (I := I) B hm htpos ht hIH
    rw [← hC, ← hbarTop] at hreact
    have htm0 : 0 ≤ t ^ m := pow_nonneg ht.1 m
    have htmne : t ^ m ≠ 0 := ne_of_gt (pow_pos htpos m)
    have htmR :
        t ^ m * towerReactionSum (M := M) B.w B.c m t x ≤
          barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3 := by
      calc
        t ^ m * towerReactionSum (M := M) B.w B.c m t x ≤
            t ^ m * (barTop * B.K * (B.w m t x + B.K ^ 2 / t ^ m)) :=
          mul_le_mul_of_nonneg_left hreact htm0
        _ = barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3 := by
          field_simp
    have htopForce0 : 0 ≤ barTop * B.K ^ 3 :=
      mul_nonneg hbarTop0 (pow_nonneg (le_of_lt B.hK) 3)
    have hRq : q ^ (m + 1) *
        (t ^ m * towerReactionSum (M := M) B.w B.c m t x) ≤
          topSpace + barTop * B.K ^ 3 := by
      calc
        q ^ (m + 1) * (t ^ m * towerReactionSum (M := M) B.w B.c m t x) ≤
            q ^ (m + 1) *
              (barTop * B.K * (t ^ m * B.w m t x) + barTop * B.K ^ 3) :=
          mul_le_mul_of_nonneg_left htmR (pow_nonneg hq0 (m + 1))
        _ = topSpace + q ^ (m + 1) * (barTop * B.K ^ 3) := by
          dsimp only [topSpace]
          ring
        _ ≤ topSpace + 1 * (barTop * B.K ^ 3) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right (hqpow_le (m + 1)) htopForce0) topSpace
        _ = topSpace + barTop * B.K ^ 3 := by ring
    have hraw := hlevel m (Finset.mem_range.mpr (Nat.lt_succ_self m))
    rw [hGm] at hraw
    dsimp only [topBound, timeTerm, topNeg, topSpace, errTerm]
    rw [hGm]
    nlinarith [hRq]
  have hsumBound :
      (∑ i ∈ Finset.range (m + 1),
        parabolicOperatorWithDrift (I := I) G B.T
          (fun _ y ↦ (0 : TangentSpace I y)) (term i) t x) ≤
        (∑ i ∈ Finset.range m, lowerBound i) + topBound := by
    rw [Finset.sum_range_succ]
    exact add_le_add (Finset.sum_le_sum hlower) htop
  have hW := cutWsum_nonpos (I := I) B cut hm ht x hsmall
  dsimp only at hW
  rw [← hq, ← hbeta, ← hbarTop] at hW
  rw [Finset.mul_sum] at hW
  have hW' : (∑ i ∈ Finset.range (m + 1), timeTerm i) -
      (∑ i ∈ Finset.range m, negTerm i) + topSpace +
      (∑ i ∈ Finset.range (m + 1), errTerm i) ≤ errTerm 0 := by
    simpa only [timeTerm, negTerm, topSpace, errTerm, Nat.cast_zero, zero_mul,
      pow_zero, one_mul, mul_assoc] using hW
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hW'
  have hforceSum :
      (∑ i ∈ Finset.range m, forceTerm i) =
        beta * (∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3 := by
    dsimp only [forceTerm]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlowerSum :
      (∑ i ∈ Finset.range m, lowerBound i) =
        (∑ i ∈ Finset.range m, timeTerm i) -
          (∑ i ∈ Finset.range m, negTerm i) +
          (∑ i ∈ Finset.range m, errTerm i) +
          (∑ i ∈ Finset.range m, forceTerm i) := by
    simp only [lowerBound, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have htopNeg0 : 0 ≤ topNeg := by
    dsimp only [topNeg]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.1 m))
        (pow_nonneg hq0 (m + 1))) (B.hw_nonneg (m + 1) t ht x)
  have hassembled :
      (∑ i ∈ Finset.range m, lowerBound i) + topBound ≤
        errTerm 0 +
          (barTop + beta * (∑ i ∈ Finset.range m,
            towerFactCoeff m i * towerBarGood B.c C i)) * B.K ^ 3 := by
    rw [hlowerSum, hforceSum]
    dsimp only [topBound]
    nlinarith [hW', htopNeg0]
  have herr0 : errTerm 0 ≤
      9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := by
    have hcoef0 : 0 ≤
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (cut.err_nonneg n))
        (BernsteinTower.Gcoef_nonneg (I := I) B m 0)
    calc
      errTerm 0 =
          (9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0) * B.w 0 t x := by
        simp only [errTerm, cutErrCoeff, Nat.cast_zero, zero_add, pow_zero]
        ring
      _ ≤ (9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0) * B.K ^ 2 :=
        mul_le_mul_of_nonneg_left (B.hw0_bound t ht x) hcoef0
      _ = 9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2 := rfl
  rw [hsum]
  linarith [hsumBound, hassembled, herr0]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [SigmaCompactSpace M]
  [T2Space M] in
private theorem GfunCut_time_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (x : M) :
    DifferentiableWithinAt Real
      (fun s : Real ↦ GfunCut (I := I) B cut m n s x)
      (Set.Icc 0 B.T) t := by
  classical
  let τ : RealTimeInterval.RegularTime B.D :=
    ⟨t, B.hregular t ht htpos⟩
  set dvec : Nat → Real := fun i ↦ Classical.choose (B.hheat i τ x) with hdvec
  have hd : ∀ i : Nat,
      HasDerivWithinAt (fun s : Real ↦ B.w i s x) (dvec i)
        (Set.Icc 0 B.T) t := by
    intro i
    have hi := (Classical.choose_spec (B.hheat i τ x)).1
    have hi' : HasDerivWithinAt (fun s : Real ↦ B.w i s x) (dvec i)
        B.D.carrier t := by
      simpa only [hdvec, τ] using hi
    exact hi'.mono B.hslab
  let term : Nat → Real → Real := fun i s ↦
    BernsteinTower.Gcoef (I := I) B m i * s ^ i *
      (cut.chi n s x) ^ (i + 1) * B.w i s x
  have hterm : ∀ i ∈ Finset.range (m + 1),
      DifferentiableWithinAt Real (term i) (Set.Icc 0 B.T) t := by
    intro i _
    have hprod :=
      ((((hasDerivWithinAt_id t (Set.Icc 0 B.T)).pow i).differentiableWithinAt.mul
        ((cut.time_diff n t ht htpos x).pow (i + 1))).mul
          (hd i).differentiableWithinAt)
    simpa only [term, mul_assoc] using
      hprod.const_mul (BernsteinTower.Gcoef (I := I) B m i)
  rw [show (fun s : Real ↦ GfunCut (I := I) B cut m n s x) =
      (fun s : Real ↦ ∑ i ∈ Finset.range (m + 1), term i s) by
    funext s
    rw [GfunCut]]
  exact DifferentiableWithinAt.fun_sum hterm

omit [NeZero (Module.finrank Real E)] in
private theorem GfunCut_space_diff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (m n : Nat) {t : Real} (ht : t ∈ Set.Icc 0 B.T) (htpos : 0 < t)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (GfunCut (I := I) B cut m n t) x := by
  classical
  let f : Nat → M → Real := fun i y ↦
    (cut.chi n t y) ^ (i + 1) * B.w i t y
  let c : Nat → Real := fun i ↦
    BernsteinTower.Gcoef (I := I) B m i * t ^ i
  rw [show GfunCut (I := I) B cut m n t =
      (fun y : M ↦ ∑ i ∈ Finset.range (m + 1), c i * f i y) by
    funext y
    rw [GfunCut]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c, f]
    ring]
  exact mdifferentiableAt_finset_sum_smul (I := I)
    (Finset.range (m + 1)) f c x (fun i _ ↦ by
      exact ((cut.space_diff (n := n) ht x).pow (i + 1)).mul
        (B.hw_space i t ht htpos x))

namespace BernsteinTower

omit [NeZero (Module.finrank Real E)] in
/-- **Complete-noncompact Bernstein estimate from quantitative cutoffs.**

The cutoff family localizes the graded Bernstein polynomial to one compact
spatial set, while `TowerNormGradOn` absorbs the cutoff-gradient terms.  The
cutoff index is internal: exhaustion recovers the ordinary polynomial at the
requested point and `err n → 0` removes the remaining level-zero error. -/
theorem estimate_of_cutoff
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (cut : ShiCutoffData (I := I) G B.T)
    (hgrad : TowerNormGradOn (I := I) B) :
    ∀ m : Nat, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m IH =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      intro t ht _ x
      simp only [pow_zero, one_mul, towerConst_zero, one_pow]
      exact B.hw0_bound t ht x
    · classical
      set C : Nat → Real := towerConst B.c B.α with hC
      set beta : Real := towerBeta B.c B.α C m with hbeta
      have hbeta0 : 0 ≤ beta := by
        simpa only [hbeta, hC] using towerBeta_nonneg B.hc B.hα m
      set barTop : Real := towerBarTop B.c C m with hbarTop
      have hbarTop0 : 0 ≤ barTop := by
        simpa only [hbarTop, hC] using towerBarTop_nonneg B.hc B.α m
      set aBar : Real := beta * (Nat.factorial (m - 1) : Real) * B.K ^ 2
        with haBar
      set bCore : Real :=
        (barTop + beta * ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i) * B.K ^ 3
        with hbCore
      let bErr : Nat → Real := fun n ↦
        9 * cut.err n * BernsteinTower.Gcoef (I := I) B m 0 * B.K ^ 2
      let bBar : Nat → Real := fun n ↦ bCore + bErr n
      have haBar0 : 0 ≤ aBar := by
        rw [haBar]
        exact mul_nonneg
          (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
          (pow_nonneg (le_of_lt B.hK) 2)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range m,
          towerFactCoeff m i * towerBarGood B.c C i := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (towerFactCoeff_nonneg _ _)
          (by simpa only [hC] using towerBarGood_nonneg B.hc B.α i)
      have hbCore0 : 0 ≤ bCore := by
        rw [hbCore]
        exact mul_nonneg
          (add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0))
          (pow_nonneg (le_of_lt B.hK) 3)
      have hbErr0 : ∀ n, 0 ≤ bErr n := by
        intro n
        dsimp only [bErr]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (cut.err_nonneg n))
            (BernsteinTower.Gcoef_nonneg (I := I) B m 0))
          (pow_nonneg (le_of_lt B.hK) 2)
      have hbBar0 : ∀ n, 0 ≤ bBar n :=
        fun n ↦ add_nonneg hbCore0 (hbErr0 n)
      have htK_slab : ∀ s : Real, s ∈ Set.Icc 0 B.T → s * B.K ≤ B.α := by
        intro s hs
        have hsle : s ≤ B.α / B.K := le_trans hs.2 B.hTK
        calc
          s * B.K ≤ (B.α / B.K) * B.K :=
            mul_le_mul_of_nonneg_right hsle (le_of_lt B.hK)
          _ = B.α := div_mul_cancel₀ B.α (ne_of_gt B.hK)
      have hbound_cut : ∀ n : Nat,
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 →
          ∀ s : Real, s ∈ Set.Icc 0 B.T → ∀ y : M,
            GfunCut (I := I) B cut m n s y ≤ aBar + bBar n * s := by
        intro n hsmall
        let F : Real → M → Real := GfunCut (I := I) B cut m n
        let w : Real → M → Real := fun s y ↦ (aBar + bBar n * s) - F s y
        have hFtime : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            DifferentiableWithinAt Real (fun r : Real ↦ F r y)
              (Set.Icc 0 B.T) s := by
          intro s hs hspos y
          simpa only [F] using
            GfunCut_time_diff (I := I) B cut m n hs hspos y
        have hFspace : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I 𝓘(Real, Real) (F s) y := by
          intro s hs hspos y
          simpa only [F] using
            GfunCut_space_diff (I := I) B cut m n hs hspos y
        have hFgrad : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (F s) z) y := by
          intro s hs hspos y
          let f : Nat → M → Real := fun i z ↦
            (cut.chi n s z) ^ (i + 1) * B.w i s z
          let c : Nat → Real := fun i ↦
            BernsteinTower.Gcoef (I := I) B m i * s ^ i
          have hf : ∀ i ∈ Finset.range (m + 1), ∀ z : M,
              MDifferentiableAt I 𝓘(Real, Real) (f i) z := by
            intro i _ z
            exact ((cut.space_diff (n := n) hs z).pow (i + 1)).mul
              (B.hw_space i s hs hspos z)
          have hgradf : ∀ i ∈ Finset.range (m + 1),
              MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
                gradientFun (I := I) (G.metric s) (f i) z) y := by
            intro i _
            let qpow : M → Real := fun z ↦ (cut.chi n s z) ^ (i + 1)
            let wi : M → Real := B.w i s
            have hq_space : ∀ z : M,
                MDifferentiableAt I 𝓘(Real, Real) qpow z := by
              intro z
              simpa only [qpow] using (cut.space_diff (n := n) hs z).pow (i + 1)
            have hw_space : ∀ z : M,
                MDifferentiableAt I 𝓘(Real, Real) wi z := by
              intro z
              simpa only [wi] using B.hw_space i s hs hspos z
            have hq_grad : ∀ z : M,
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun u : M ↦
                  gradientFun (I := I) (G.metric s) qpow u) z := by
              intro z
              exact gradientFun_mdiffAt (I := I) (G.metric s)
                ((cut.space_smooth n s hs).pow (i + 1)) z
            have hw_grad : ∀ z : M,
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun u : M ↦
                  gradientFun (I := I) (G.metric s) wi u) z := by
              intro z
              simpa only [wi] using B.hw_grad i s hs hspos z
            have hprod_grad :
                MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
                  gradientFun (I := I) (G.metric s)
                    (fun u ↦ qpow u * wi u) z) y := by
              have hplain :
                  (fun z : M ↦ gradientFun (I := I) (G.metric s)
                    (fun u ↦ qpow u * wi u) z) =
                    (fun z : M ↦
                      qpow z • gradientFun (I := I) (G.metric s) wi z +
                      wi z • gradientFun (I := I) (G.metric s) qpow z) := by
                funext z
                exact gradientFun_mul (I := I) (G.metric s)
                  (hq_space z) (hw_space z)
              rw [show (T% fun z : M ↦ gradientFun (I := I) (G.metric s)
                  (fun u ↦ qpow u * wi u) z) =
                  (T% fun z : M ↦
                    qpow z • gradientFun (I := I) (G.metric s) wi z +
                    wi z • gradientFun (I := I) (G.metric s) qpow z) by
                funext z
                simpa using congrFun hplain z]
              exact mdifferentiableAt_add_section
                ((hq_space y).smul_section (hw_grad y))
                ((hw_space y).smul_section (hq_grad y))
            simpa only [f, qpow, wi] using hprod_grad
          rw [show F s =
              (fun z : M ↦ ∑ i ∈ Finset.range (m + 1), c i * f i z) by
            funext z
            change GfunCut (I := I) B cut m n s z = _
            rw [GfunCut]
            apply Finset.sum_congr rfl
            intro i _
            simp only [c, f]
            ring]
          exact mdiffAt_gradientFun_finset_sum_smul (I := I)
            (Finset.range (m + 1)) G s f c y hf hgradf
        have hFcont : ContinuousOn (fun p : Real × M ↦ F p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          simpa only [F] using
            (GfunCut_cont (I := I) B cut m n).mono (fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩)
        have hinit : ∀ y : M, F 0 y ≤ aBar := by
          intro y
          have h0mem : (0 : Real) ∈ Set.Icc 0 B.T :=
            ⟨le_rfl, le_of_lt B.hT⟩
          have hF0 : F 0 y =
              BernsteinTower.Gcoef (I := I) B m 0 * cut.chi n 0 y * B.w 0 0 y := by
            change GfunCut (I := I) B cut m n 0 y = _
            rw [GfunCut]
            rw [Finset.sum_eq_single 0]
            · simp
            · intro i _ hi0
              rcases Nat.eq_zero_or_pos i with hi | hi
              · exact absurd hi hi0
              · simp [zero_pow (by omega : i ≠ 0)]
            · intro h
              simp at h
          have hGc0 : BernsteinTower.Gcoef (I := I) B m 0 =
              beta * (Nat.factorial (m - 1) : Real) := by
            rw [BernsteinTower.Gcoef, if_neg (by omega : ¬ (0 : Nat) = m),
              towerFactCoeff]
            rw [Nat.factorial_zero, Nat.cast_one, div_one, ← hC, ← hbeta]
          have hchi := cut.range n 0 y h0mem
          have hw0 := B.hw_nonneg 0 0 h0mem y
          have hchi_w : cut.chi n 0 y * B.w 0 0 y ≤ B.K ^ 2 := by
            calc
              cut.chi n 0 y * B.w 0 0 y ≤ 1 * B.w 0 0 y :=
                mul_le_mul_of_nonneg_right hchi.2 hw0
              _ = B.w 0 0 y := one_mul _
              _ ≤ B.K ^ 2 := B.hw0_bound 0 h0mem y
          rw [hF0, hGc0, haBar]
          calc
            beta * (Nat.factorial (m - 1) : Real) * cut.chi n 0 y * B.w 0 0 y =
                (beta * (Nat.factorial (m - 1) : Real)) *
                  (cut.chi n 0 y * B.w 0 0 y) := by ring
            _ ≤ (beta * (Nat.factorial (m - 1) : Real)) * B.K ^ 2 :=
              mul_le_mul_of_nonneg_left hchi_w
                (mul_nonneg hbeta0 (Nat.cast_nonneg (Nat.factorial (m - 1))))
        have hw_out : ∀ s : Real, s ∈ Set.Icc 0 B.T →
            ∀ y : M, y ∉ cut.support n → 0 ≤ w s y := by
          intro s hs y hy
          dsimp only [w]
          rw [show F s y = 0 by
            exact GfunCut_off (I := I) B cut m n hs hy]
          simpa only [sub_zero] using
            add_nonneg haBar0 (mul_nonneg (hbBar0 n) hs.1)
        have hw_cont : ContinuousOn (fun p : Real × M ↦ w p.1 p.2)
            (Set.Icc 0 B.T ×ˢ cut.support n) := by
          have haffine : ContinuousOn
              (fun p : Real × M ↦ aBar + bBar n * p.1)
              (Set.Icc 0 B.T ×ˢ cut.support n) :=
            (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn
          simpa only [w] using haffine.sub hFcont
        have hw0 : ∀ y : M, 0 ≤ w 0 y := by
          intro y
          have hy := hinit y
          dsimp only [w]
          simpa only [mul_zero, add_zero] using sub_nonneg.mpr hy
        have hw_time : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            DifferentiableWithinAt Real (fun r : Real ↦ w r y)
              (Set.Icc 0 B.T) s := by
          intro s hs hspos y
          have haffine : DifferentiableWithinAt Real
              (fun r : Real ↦ aBar + bBar n * r) (Set.Icc 0 B.T) s :=
            (differentiableWithinAt_const aBar).add
              ((differentiableWithinAt_id' (𝕜 := Real)
                (s := Set.Icc 0 B.T) (x := s)).const_mul (bBar n))
          simpa only [w] using haffine.sub (hFtime s hs hspos y)
        have hw_mdiff : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I 𝓘(Real, Real) (w s) y := by
          intro s hs hspos y
          simpa only [w] using
            mdifferentiableAt_const.sub (hFspace s hs hspos y)
        have hw_grad : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s → ∀ y : M,
            MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (w s) z) y := by
          intro s hs hspos y
          have hplain :
              (fun z : M ↦ gradientFun (I := I) (G.metric s) (w s) z) =
                (fun z : M ↦ -gradientFun (I := I) (G.metric s) (F s) z) := by
            funext z
            calc
              gradientFun (I := I) (G.metric s) (w s) z =
                  gradientFun (I := I) (G.metric s)
                    (fun u : M ↦ aBar + bBar n * s) z -
                    gradientFun (I := I) (G.metric s) (F s) z := by
                exact gradientFun_sub (I := I) (G.metric s)
                  mdifferentiableAt_const (hFspace s hs hspos z)
              _ = -gradientFun (I := I) (G.metric s) (F s) z := by
                rw [gradientFun_const]
                simp
          rw [show (T% fun z : M ↦
              gradientFun (I := I) (G.metric s) (w s) z) =
              (T% fun z : M ↦
                -gradientFun (I := I) (G.metric s) (F s) z) by
            funext z
            simpa using congrFun hplain z]
          rw [show (T% fun z : M ↦
              -gradientFun (I := I) (G.metric s) (F s) z) =
              (T% ((-1 : Real) • fun z : M ↦
                gradientFun (I := I) (G.metric s) (F s) z)) by
            funext z
            simp]
          exact (hFgrad s hs hspos y).smul_const_section (a := (-1 : Real))
        have hw_negative : ∀ s : Real, s ∈ Set.Icc 0 B.T → 0 < s →
            ∀ y : M, w s y < 0 →
              0 ≤ parabolicOperatorWithDrift (I := I) G B.T
                (fun _ z ↦ (0 : TangentSpace I z)) w s y := by
          intro s hs hspos y _
          have huniq : UniqueDiffWithinAt Real (Set.Icc 0 B.T) s :=
            (uniqueDiffOn_Icc B.hT).uniqueDiffWithinAt hs
          have hop :
              parabolicOperatorWithDrift (I := I) G B.T
                  (fun _ z ↦ (0 : TangentSpace I z)) w s y =
                bBar n - parabolicOperatorWithDrift (I := I) G B.T
                  (fun _ z ↦ (0 : TangentSpace I z)) F s y := by
            simpa only [w] using
              parabolicOperatorWithDrift_affine_sub (I := I) G B.T
                (fun _ z ↦ (0 : TangentSpace I z)) F aBar (bBar n) s y
                huniq (hFtime s hs hspos y)
                (fun z ↦ hFspace s hs hspos z) (hFgrad s hs hspos y)
          have hsub := GfunCut_parabolic_le (I := I) B cut hmpos
            (hgrad.upTo m) hs hspos y
            (fun j hj ↦ IH j hj s hs hspos y) hsmall
          have hsub' : parabolicOperatorWithDrift (I := I) G B.T
              (fun _ z ↦ (0 : TangentSpace I z)) F s y ≤ bBar n := by
            simpa only [F, bBar, bCore, bErr] using hsub
          rw [hop]
          linarith
        have hw_nonneg := strict_barrier_cpt (I := I) G B.T (le_of_lt B.hT)
          (fun _ z ↦ (0 : TangentSpace I z)) w (cut.support n)
          (cut.support_compact n) hw_out hw_cont hw0 hw_time hw_mdiff hw_grad
          hw_negative
        intro s hs y
        have hw := hw_nonneg s hs y
        dsimp only [w] at hw
        linarith
      intro t ht htpos x
      have hwm_le_G : t ^ m * B.w m t x ≤ BernsteinTower.Gfun (I := I) B m t x := by
        rw [BernsteinTower.Gfun]
        have hm_mem : m ∈ Finset.range (m + 1) := by simp
        rw [← Finset.sum_erase_add _ _ hm_mem]
        have htop : BernsteinTower.Gcoef (I := I) B m m * t ^ m * B.w m t x =
            t ^ m * B.w m t x := by
          rw [BernsteinTower.Gcoef]
          simp
        rw [htop]
        have hrest : 0 ≤ ∑ i ∈ (Finset.range (m + 1)).erase m,
            BernsteinTower.Gcoef (I := I) B m i * t ^ i * B.w i t x := by
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg
            (mul_nonneg (BernsteinTower.Gcoef_nonneg (I := I) B m i)
              (pow_nonneg ht.1 i))
            (B.hw_nonneg i t ht x)
        linarith
      have hsmall_eventually : ∀ᶠ n in Filter.atTop,
          2 * cut.err n * B.T * cutErrCoeff m ≤ 1 := by
        filter_upwards [cut.cutErr_small m] with n hn
        have hm_cut := hn m (by simp)
        ring_nf at hm_cut ⊢
        linarith
      have hexhaust : ∀ᶠ n in Filter.atTop, cut.chi n t x = 1 := by
        obtain ⟨n₀, hn₀⟩ := cut.exhausts t x ht
        exact Filter.eventually_atTop.2 ⟨n₀, hn₀⟩
      have hbound_eventually : ∀ᶠ n in Filter.atTop,
          t ^ m * B.w m t x ≤ aBar + bBar n * t := by
        filter_upwards [hsmall_eventually, hexhaust] with n hsmall hchi
        have hcut := hbound_cut n hsmall t ht x
        rw [GfunCut_one (I := I) B cut hchi] at hcut
        exact hwm_le_G.trans hcut
      have hbErr_tendsto : Filter.Tendsto bErr Filter.atTop (nhds 0) := by
        simpa only [bErr, zero_mul, mul_zero] using
          (((cut.err_tendsto.const_mul 9).mul_const
            (BernsteinTower.Gcoef (I := I) B m 0)).mul_const (B.K ^ 2))
      have hrhs_tendsto : Filter.Tendsto
          (fun n ↦ aBar + bBar n * t) Filter.atTop (nhds (aBar + bCore * t)) := by
        have hconst : Filter.Tendsto (fun _ : Nat ↦ aBar + bCore * t)
            Filter.atTop (nhds (aBar + bCore * t)) := tendsto_const_nhds
        simpa only [bBar, add_mul, add_assoc, zero_mul, add_zero] using
          (hconst.add (hbErr_tendsto.mul_const t))
      have hlimit : t ^ m * B.w m t x ≤ aBar + bCore * t :=
        ge_of_tendsto hrhs_tendsto hbound_eventually
      have hfinal : aBar + bCore * t ≤ towerConstSq B.c B.α m * B.K ^ 2 := by
        rw [towerConstSq_pos B.c B.α hmpos, haBar, hbCore, ← hbeta, ← hC,
          ← hbarTop]
        have htK : t * B.K ≤ B.α := htK_slab t ht
        have hcoeff0 : 0 ≤ barTop + beta * ∑ i ∈ Finset.range m,
            towerFactCoeff m i * towerBarGood B.c C i :=
          add_nonneg hbarTop0 (mul_nonneg hbeta0 hsum0)
        have hKsq0 : 0 ≤ B.K ^ 2 := pow_nonneg (le_of_lt B.hK) 2
        nlinarith [htK, mul_nonneg hcoeff0 hKsq0]
      rw [towerConst_sq B.hc B.hα]
      exact hlimit.trans hfinal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Legacy unsupported frontier.**  This statement is too weak for a
complete-noncompact Bernstein argument: metric equivalence and a Ricci lower
bound do not produce quantitative evolving-metric cutoffs, and the abstract
tower does not expose the Kato estimate needed to absorb cutoff-gradient
terms.  Replace its caller by a localized theorem consuming generated cutoff
data and `TowerNormGradOn`; do not fill this proof under the present
interface. -/
theorem estimate_complete
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    {G : RealizedMetricFamily (I := I) (M := M) Real}
    (B : BernsteinTower (I := I) G)
    (Ceq Kric : Real) (hCeq : 1 ≤ Ceq) (hKric : 0 ≤ Kric)
    (hequiv : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        Ceq⁻¹ * ‖v‖ ^ 2 ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Ceq * ‖v‖ ^ 2)
    (hric : ∀ t : Real, t ∈ Set.Icc 0 B.T → ∀ x : M,
      ∀ v : TangentSpace I x,
        -Kric * (G.metric t).inner x v v ≤
          ricciTensor (I := I) (G.metric t) x v v) :
    ∀ m : ℕ, ∀ t : Real, t ∈ Set.Icc 0 B.T → 0 < t → ∀ x : M,
      t ^ m * B.w m t x ≤ (towerConst B.c B.α m) ^ 2 * B.K ^ 2 := by
  sorry

end BernsteinTower

end DifferentialGeometry.PDE.RicciFlow
