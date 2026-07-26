import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Fiber inequalities for the covariant tensor metric

`Tensor0SMetric.lean` builds the metric-induced inner product `inner0S` and
squared norm `normSq0S` on the covariant tensor fibers `Tensor0SSpace s I x`,
and records Cauchy--Schwarz (`inner0S_sq_le_mul`) and nonnegativity
(`normSq0S_nonneg`).  This file adds the bilinearity and inequality layer that
pointwise energy estimates consume:

* bilinearity and symmetry of `inner0S`;
* the binomial expansions `normSq0S_add` / `normSq0S_sub`;
* the Cauchy--Schwarz absolute-value form `abs_inner0S_le`;
* the doubling bounds `normSq0S_add_le` / `normSq0S_sub_le`;
* the coordinate-free Minkowski inequality `sqrt_normSq0S_add_le`.

Everything is derived from the linearity of the flat map underlying
`tensor0SMetricData` together with the two facts already proved in
`Tensor0SMetric.lean`; no component enumeration and no choice of frame is
involved, so all statements hold at an arbitrary point of an arbitrary rank.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Bilinearity and symmetry -/

/-- The metric-induced inner product on covariant tensor fibers is symmetric. -/
theorem inner0S_comm
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B = inner0S (I := I) g x s B A :=
  (tensor0SMetricData (I := I) g x s).inner_comm A B

/-- Additivity of `inner0S` in the first slot. -/
theorem inner0S_add_left
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (A + B) C =
      inner0S (I := I) g x s A C + inner0S (I := I) g x s B C := by
  unfold inner0S MetricFiberData.inner
  rw [map_add, LinearMap.add_apply]

/-- Additivity of `inner0S` in the second slot. -/
theorem inner0S_add_right
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (B + C) =
      inner0S (I := I) g x s A B + inner0S (I := I) g x s A C := by
  rw [inner0S_comm (I := I) g x s A (B + C), inner0S_add_left,
    inner0S_comm (I := I) g x s B A, inner0S_comm (I := I) g x s C A]

/-- Subtractivity of `inner0S` in the first slot. -/
theorem inner0S_sub_left
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (A - B) C =
      inner0S (I := I) g x s A C - inner0S (I := I) g x s B C := by
  unfold inner0S MetricFiberData.inner
  rw [map_sub, LinearMap.sub_apply]

/-- Subtractivity of `inner0S` in the second slot. -/
theorem inner0S_sub_right
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B C : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (B - C) =
      inner0S (I := I) g x s A B - inner0S (I := I) g x s A C := by
  rw [inner0S_comm (I := I) g x s A (B - C), inner0S_sub_left,
    inner0S_comm (I := I) g x s B A, inner0S_comm (I := I) g x s C A]

/-- Homogeneity of `inner0S` in the first slot. -/
theorem inner0S_smul_left
    (g : SmoothMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (c • A) B = c * inner0S (I := I) g x s A B := by
  unfold inner0S MetricFiberData.inner
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- Homogeneity of `inner0S` in the second slot. -/
theorem inner0S_smul_right
    (g : SmoothMetric I M) (x : M) (s : Nat) (c : Real)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A (c • B) = c * inner0S (I := I) g x s A B := by
  rw [inner0S_comm (I := I) g x s A (c • B), inner0S_smul_left,
    inner0S_comm (I := I) g x s B A]

/-! ### Quadratic expansions -/

/-- Binomial expansion of the squared fiber norm of a sum. -/
theorem normSq0S_add
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) =
      normSq0S (I := I) g x s A + 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_add_left, inner0S_add_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

/-- Binomial expansion of the squared fiber norm of a difference. -/
theorem normSq0S_sub
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) =
      normSq0S (I := I) g x s A - 2 * inner0S (I := I) g x s A B +
        normSq0S (I := I) g x s B := by
  simp only [normSq0S_eq_inner, inner0S_sub_left, inner0S_sub_right]
  rw [inner0S_comm (I := I) g x s B A]
  ring

/-- The squared fiber norm is invariant under negation. -/
theorem normSq0S_neg
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (-A) = normSq0S (I := I) g x s A := by
  have h : (-A : Tensor0SSpace s I x) = (-1 : Real) • A := by
    rw [neg_one_smul]
  rw [h]
  simp only [normSq0S_eq_inner]
  rw [inner0S_smul_left, inner0S_smul_right]
  ring

/-! ### Cauchy--Schwarz and the doubling bounds -/

/-- Cauchy--Schwarz in absolute-value form: the metric-induced inner product is
bounded by the product of the fiber norms. -/
theorem abs_inner0S_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    |inner0S (I := I) g x s A B| ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hcs := Real.sqrt_le_sqrt (inner0S_sq_le_mul (I := I) g x s A B)
  rwa [Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (normSq0S_nonneg (I := I) g x s A)] at hcs

/-- The polarization bound `2⟨A, B⟩ ≤ |A|² + |B|²`. -/
theorem two_inner0S_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    2 * inner0S (I := I) g x s A B ≤
      normSq0S (I := I) g x s A + normSq0S (I := I) g x s B := by
  have h := normSq0S_nonneg (I := I) g x s (A - B)
  rw [normSq0S_sub] at h
  linarith

/-- The polarization bound `-(|A|² + |B|²) ≤ 2⟨A, B⟩`. -/
theorem neg_two_inner0S_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    -(normSq0S (I := I) g x s A + normSq0S (I := I) g x s B) ≤
      2 * inner0S (I := I) g x s A B := by
  have h := normSq0S_nonneg (I := I) g x s (A + B)
  rw [normSq0S_add] at h
  linarith

/-- Doubling bound `|A + B|² ≤ 2|A|² + 2|B|²` for the metric fiber norm. -/
theorem normSq0S_add_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A + B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := two_inner0S_le (I := I) g x s A B
  rw [normSq0S_add]
  linarith

/-- Doubling bound `|A - B|² ≤ 2|A|² + 2|B|²` for the metric fiber norm. -/
theorem normSq0S_sub_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (A - B) ≤
      2 * normSq0S (I := I) g x s A + 2 * normSq0S (I := I) g x s B := by
  have h := neg_two_inner0S_le (I := I) g x s A B
  rw [normSq0S_sub]
  linarith

/-! ### Minkowski inequality -/

/-- **Fiber triangle inequality** (Minkowski), coordinate-free: the metric fiber
norm `√(normSq0S ·)` is subadditive. -/
theorem sqrt_normSq0S_add_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A + B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  have hA := normSq0S_nonneg (I := I) g x s A
  have hB := normSq0S_nonneg (I := I) g x s B
  have hsA : Real.sqrt (normSq0S (I := I) g x s A) ^ 2 =
      normSq0S (I := I) g x s A := Real.sq_sqrt hA
  have hsB : Real.sqrt (normSq0S (I := I) g x s B) ^ 2 =
      normSq0S (I := I) g x s B := Real.sq_sqrt hB
  have hcs : inner0S (I := I) g x s A B ≤
      Real.sqrt (normSq0S (I := I) g x s A) *
        Real.sqrt (normSq0S (I := I) g x s B) :=
    le_trans (le_abs_self _) (abs_inner0S_le (I := I) g x s A B)
  have hexp : (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 =
      normSq0S (I := I) g x s A +
        2 * (Real.sqrt (normSq0S (I := I) g x s A) *
          Real.sqrt (normSq0S (I := I) g x s B)) +
        normSq0S (I := I) g x s B := by
    rw [add_sq, hsA, hsB]; ring
  have key : normSq0S (I := I) g x s (A + B) ≤
      (Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B)) ^ 2 := by
    rw [normSq0S_add, hexp]
    linarith
  calc Real.sqrt (normSq0S (I := I) g x s (A + B))
      ≤ Real.sqrt ((Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B)) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (normSq0S (I := I) g x s A) +
          Real.sqrt (normSq0S (I := I) g x s B) :=
        Real.sqrt_sq (by positivity)

/-- Fiber triangle inequality for a difference. -/
theorem sqrt_normSq0S_sub_le
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g x s (A - B)) ≤
      Real.sqrt (normSq0S (I := I) g x s A) +
        Real.sqrt (normSq0S (I := I) g x s B) := by
  rw [sub_eq_add_neg]
  refine le_trans (sqrt_normSq0S_add_le (I := I) g x s A (-B)) ?_
  rw [normSq0S_neg]

end

end Tensor0SBundle
