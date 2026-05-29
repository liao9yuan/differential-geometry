import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Coordinate

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Comparing Covariant Tensor Norms In Diagonal Coordinates

This file contains the finite-sum algebra behind MSM135 Lemma 3.13 in the
covariant case.  The analytic/geometric producer that diagonalizes two
equivalent metrics at a point is intentionally kept separate.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section DiagonalCoordinate

variable {Idx : Type*} [DecidableEq Idx]
variable {x : M}

/-- Diagonal inverse-metric components in a basis. -/
def diagonalInvMetric (μ : Idx -> Real) : Idx -> Idx -> Real :=
  fun i j => if i = j then μ i else 0

/-- Identity inverse-metric components in a basis. -/
def identityInvMetric : Idx -> Idx -> Real :=
  diagonalInvMetric (fun _ : Idx => 1)

@[simp] theorem diagonalInvMetric_apply_self (μ : Idx -> Real) (i : Idx) :
    diagonalInvMetric μ i i = μ i := by
  simp [diagonalInvMetric]

@[simp] theorem identityInvMetric_apply_self (i : Idx) :
    identityInvMetric (Idx := Idx) i i = 1 := by
  simp [identityInvMetric]

theorem diagonalInvMetric_eq_zero_of_ne {μ : Idx -> Real} {i j : Idx}
    (hij : i ≠ j) :
    diagonalInvMetric μ i j = 0 := by
  simp [diagonalInvMetric, hij]

private theorem prod_diagonalInvMetric_eq_zero_of_ne
    {s : Nat} {μ : Idx -> Real} {I0 J0 : Fin s -> Idx}
    (hIJ : I0 ≠ J0) :
    (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 := by
  classical
  have hsome : exists a : Fin s, I0 a ≠ J0 a := by
    by_contra hnone
    apply hIJ
    funext a
    by_contra ha
    exact hnone ⟨a, ha⟩
  rcases hsome with ⟨a, ha⟩
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (diagonalInvMetric_eq_zero_of_ne (μ := μ) ha)

omit [DecidableEq Idx] in
private theorem prod_mu_le_pow
    {s : Nat} {μ : Idx -> Real} {C : Real}
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (I0 : Fin s -> Idx) :
    (∏ a : Fin s, μ (I0 a)) <= C ^ s := by
  calc
    (∏ a : Fin s, μ (I0 a)) <= ∏ _a : Fin s, C := by
          apply Finset.prod_le_prod
          · intro a _
            exact hμ_nonneg (I0 a)
          · intro a _
            exact hμ_le (I0 a)
    _ = C ^ s := by simp

variable [Fintype Idx]

/-- Coordinate squared norm for a diagonal inverse metric. -/
theorem coordInner0S_diagonal_eq_sum
    (s : Nat) (μ : Idx -> Real)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis =
      ∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, μ (I0 a)) *
          (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2 := by
  classical
  unfold coordInner0S
  apply Finset.sum_congr rfl
  intro I0 _
  rw [Finset.sum_eq_single I0]
  · simp [diagonalInvMetric, pow_two]
    ring
  · intro J0 _ hJ0
    have hprod :
        (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 :=
      prod_diagonalInvMetric_eq_zero_of_ne (μ := μ) (Ne.symm hJ0)
    rw [hprod]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ I0))

/-- Coordinate squared norm for the identity inverse metric. -/
theorem coordInner0S_identity_eq_sum_sq
    (s : Nat) (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis =
      ∑ I0 : Fin s -> Idx,
        (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2 := by
  classical
  change coordInner0S (I := I) (x := x) s (diagonalInvMetric (fun _ : Idx => 1))
      A A basis =
    ∑ I0 : Fin s -> Idx,
      (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2
  rw [coordInner0S_diagonal_eq_sum (I := I) (x := x) s (fun _ : Idx => 1) A basis]
  simp

/-- Diagonal-coordinate norm comparison for covariant tensors.

If every diagonal inverse component `μ_i` of `h^{-1}` is bounded by `C`, then
the squared covariant tensor norm defined using `h` is bounded by `C^s` times
the squared norm in a `g`-orthonormal coordinate basis.  This is the finite-sum
core of MSM135 Lemma 3.13 for `(0,s)` tensors. -/
theorem coordInner0S_diagonal_le_pow_identity
    (s : Nat) (μ : Idx -> Real) (C : Real)
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis <=
      C ^ s * coordInner0S (I := I) (x := x) s identityInvMetric A A basis := by
  classical
  rw [coordInner0S_diagonal_eq_sum (I := I) (x := x) s μ A basis,
    coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I0 _
  exact mul_le_mul_of_nonneg_right
    (prod_mu_le_pow (μ := μ) (C := C) hμ_nonneg hμ_le I0)
    (sq_nonneg _)

/-- Squared norm comparison for covariant tensors in a basis where the first
metric has identity inverse components and the second has diagonal inverse
components.

This is the invariant-norm version of the diagonal finite-sum estimate above.
For a `(0,s)` tensor it gives the squared estimate
`|A|_h^2 <= C^s |A|_g^2`, corresponding to MSM135 Lemma 3.13 after taking
square roots. -/
theorem normSq0S_diag_le
    (g h : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real) (C : Real)
    (hginv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (hhinv :
      MetricInverseInBasis (I := I) h x basis (diagonalInvMetric μ))
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) h x s A <= C ^ s * normSq0S (I := I) g x s A := by
  rw [normSq0S_eq_coord (I := I) h x s basis (diagonalInvMetric μ) hhinv A,
    normSq0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hginv A]
  exact coordInner0S_diagonal_le_pow_identity (I := I) (x := x) s μ C hμ_nonneg hμ_le A basis

end DiagonalCoordinate

end

end Tensor0SBundle
