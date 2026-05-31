import RicciFlower.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Connection-Difference Action On Mixed Tensor Components

This file contains the finite-dimensional component estimate used in MSM135
Chapter 4, Lemma "Norms of covariant derivatives of tensors, I".  The
geometric connection-change identity is proved elsewhere; here we only record
the algebraic action of a `(1,2)` connection-difference tensor on the upper and
lower slots of an `(r,s)` tensor.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]

/-- Tail of the lower slots after the derivative-direction slot of a
covariant derivative has been removed. -/
def connActLowerTail {s : Nat} (lower : Fin (s + 1) -> Idx) : Fin s -> Idx :=
  fun b => lower b.succ

/-- Component-level action of a `(1,2)` connection difference `A` on an
`(r,s)` tensor component array `T`.

The first lower slot of the output is the derivative direction.  The first sum
is the upper-index correction and the second sum is the lower-index correction,
matching the convention in MSM135 Chapter 4, equation following `lbl369`. -/
def connActComp {r s : Nat}
    (A : Idx -> Idx -> Idx -> Real)
    (T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) : Real :=
  (∑ a : Fin r, ∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)) -
    (∑ b : Fin s, ∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k))

/-- Coarse finite-dimensional constant for the component action bound. -/
def connActConst (r s : Nat) (A0 T0 : Real) : Real :=
  ((r + s : Nat) : Real) * ((Fintype.card Idx : Real) * (A0 * T0))

private theorem abs_inner_sum_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) (a : Fin r) :
    |∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)| <=
      (Fintype.card Idx : Real) * (A0 * T0) := by
  have hterm (k : Idx) :
      |A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <=
        A0 * T0 := by
    rw [abs_mul]
    exact mul_le_mul
      (hA (upper a) (lower 0) k)
      (hT (Function.update upper a k) (connActLowerTail lower))
      (abs_nonneg _)
      hA0
  calc
    |∑ k : Idx,
      A (upper a) (lower 0) k *
        T (Function.update upper a k) (connActLowerTail lower)|
        <= ∑ k : Idx,
          |A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun k : Idx =>
                A (upper a) (lower 0) k *
                  T (Function.update upper a k) (connActLowerTail lower))
    _ <= ∑ _k : Idx, A0 * T0 := by
          exact Finset.sum_le_sum (fun k _ => hterm k)
    _ = (Fintype.card Idx : Real) * (A0 * T0) := by
          simp

private theorem abs_inner_sum_lower_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) (b : Fin s) :
    |∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k)| <=
      (Fintype.card Idx : Real) * (A0 * T0) := by
  have hterm (k : Idx) :
      |A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <=
        A0 * T0 := by
    rw [abs_mul]
    exact mul_le_mul
      (hA k (lower 0) (lower b.succ))
      (hT upper (Function.update (connActLowerTail lower) b k))
      (abs_nonneg _)
      hA0
  calc
    |∑ k : Idx,
      A k (lower 0) (lower b.succ) *
        T upper (Function.update (connActLowerTail lower) b k)|
        <= ∑ k : Idx,
          |A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)| := by
          simpa using
            Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun k : Idx =>
                A k (lower 0) (lower b.succ) *
                  T upper (Function.update (connActLowerTail lower) b k))
    _ <= ∑ _k : Idx, A0 * T0 := by
          exact Finset.sum_le_sum (fun k _ => hterm k)
    _ = (Fintype.card Idx : Real) * (A0 * T0) := by
          simp

/-- Componentwise absolute-value estimate for the connection-difference
action.  It is deliberately coarse; the important point for F3 is that the
constant depends only on the tensor valence and model dimension. -/
theorem abs_connActComp_le {r s : Nat}
    {A0 T0 : Real} (hA0 : 0 <= A0)
    {A : Idx -> Idx -> Idx -> Real}
    {T : (Fin r -> Idx) -> (Fin s -> Idx) -> Real}
    (hA : forall i j k : Idx, |A i j k| <= A0)
    (hT : forall upper : Fin r -> Idx, forall lower : Fin s -> Idx,
      |T upper lower| <= T0)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp A T upper lower| <= connActConst (Idx := Idx) r s A0 T0 := by
  let B : Real := (Fintype.card Idx : Real) * (A0 * T0)
  have hupper_term (a : Fin r) :
      |∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <= B := by
    simpa [B] using
      abs_inner_sum_le (Idx := Idx) (r := r) (s := s)
        hA0 hA hT upper lower a
  have hlower_term (b : Fin s) :
      |∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <= B := by
    simpa [B] using
      abs_inner_sum_lower_le (Idx := Idx) (r := r) (s := s)
        hA0 hA hT upper lower b
  have hupper_sum :
      |∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)| <=
        (r : Real) * B := by
    calc
      |∑ a : Fin r, ∑ k : Idx,
        A (upper a) (lower 0) k *
          T (Function.update upper a k) (connActLowerTail lower)|
          <= ∑ a : Fin r, |∑ k : Idx,
            A (upper a) (lower 0) k *
              T (Function.update upper a k) (connActLowerTail lower)| := by
            simpa using
              Finset.abs_sum_le_sum_abs
                (s := Finset.univ)
                (f := fun a : Fin r => ∑ k : Idx,
                  A (upper a) (lower 0) k *
                    T (Function.update upper a k) (connActLowerTail lower))
      _ <= ∑ _a : Fin r, B := by
            exact Finset.sum_le_sum (fun a _ => hupper_term a)
      _ = (r : Real) * B := by
            simp
  have hlower_sum :
      |∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)| <=
        (s : Real) * B := by
    calc
      |∑ b : Fin s, ∑ k : Idx,
        A k (lower 0) (lower b.succ) *
          T upper (Function.update (connActLowerTail lower) b k)|
          <= ∑ b : Fin s, |∑ k : Idx,
            A k (lower 0) (lower b.succ) *
              T upper (Function.update (connActLowerTail lower) b k)| := by
            simpa using
              Finset.abs_sum_le_sum_abs
                (s := Finset.univ)
                (f := fun b : Fin s => ∑ k : Idx,
                  A k (lower 0) (lower b.succ) *
                    T upper (Function.update (connActLowerTail lower) b k))
      _ <= ∑ _b : Fin s, B := by
            exact Finset.sum_le_sum (fun b _ => hlower_term b)
      _ = (s : Real) * B := by
            simp
  have htri :
      |(∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) -
        (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k))| <=
        (r : Real) * B + (s : Real) * B := by
    calc
      |(∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)) -
        (∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k))|
          <=
        |∑ a : Fin r, ∑ k : Idx,
          A (upper a) (lower 0) k *
            T (Function.update upper a k) (connActLowerTail lower)| +
        |∑ b : Fin s, ∑ k : Idx,
          A k (lower 0) (lower b.succ) *
            T upper (Function.update (connActLowerTail lower) b k)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le
                (∑ a : Fin r, ∑ k : Idx,
                  A (upper a) (lower 0) k *
                    T (Function.update upper a k) (connActLowerTail lower))
                (-(∑ b : Fin s, ∑ k : Idx,
                  A k (lower 0) (lower b.succ) *
                    T upper (Function.update (connActLowerTail lower) b k)))
      _ <= (r : Real) * B + (s : Real) * B :=
            add_le_add hupper_sum hlower_sum
  calc
    |connActComp A T upper lower| <= (r : Real) * B + (s : Real) * B := by
      simpa [connActComp, B] using htri
    _ = connActConst (Idx := Idx) r s A0 T0 := by
      simp [connActConst, B, Nat.cast_add]
      ring

/-- Tensor-norm version of `abs_connActComp_le`, obtained by bounding each
component of the connection-difference tensor and of `T` by their full
orthonormal-basis norms. -/
theorem abs_connActTensor_le
    [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) {r s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace 1 2 I x) (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |connActComp
      (fun l i j =>
        componentRS (I := I) basis A (fun _ : Fin 1 => l)
          (fun q : Fin 2 => if q = 0 then i else j))
      (fun upper' lower' => componentRS (I := I) basis T upper' lower')
      upper lower| <=
      connActConst (Idx := Idx) r s
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 A))
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s T)) := by
  refine abs_connActComp_le (Idx := Idx)
    (A0 := Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2 A))
    (T0 := Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s T))
    (r := r) (s := s) (Real.sqrt_nonneg _) ?_ ?_ upper lower
  · intro i j k
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x 1 2 basis hinv A (fun _ : Fin 1 => i)
      (fun q : Fin 2 => if q = 0 then j else k)
  · intro upper' lower'
    exact abs_componentRS_le_sqrt_normSqRS
      (I := I) g x r s basis hinv T upper' lower'

end Components

end

end Tensor0SBundle
