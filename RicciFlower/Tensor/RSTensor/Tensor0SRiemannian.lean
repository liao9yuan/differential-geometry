import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Covariant Tensor Fibers

The metric on `T_x M` induces metrics on all covariant tensor powers.  The
construction is intrinsic on the fiber `Tensor0SSpace s I x`; coordinate
formulas are evaluation theorems for local frames.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MetricFiberData

variable {V W : Type*}

private def realFlatLinear : Real →ₗ[Real] Module.Dual Real Real where
  toFun := fun a =>
    { toFun := fun b => a * b
      map_add' := by
        intro b c
        ring
      map_smul' := by
        intro c b
        simp [smul_eq_mul, mul_left_comm] }
  map_add' := by
    intro a b
    ext
    simp
  map_smul' := by
    intro c a
    ext
    simp [smul_eq_mul]

/-- The standard metric on the real scalar fiber. -/
def real : MetricFiberData Real :=
  MetricFiberData.ofFlat realFlatLinear
    (by
      intro a b h
      have h1 := congrArg (fun φ : Module.Dual Real Real => φ 1) h
      simpa [realFlatLinear] using h1)
    (by
      intro a b
      change a * b = b * a
      ring)
    (by
      intro a
      change 0 <= a * a
      nlinarith [sq_nonneg a])

/-- Pull a metric back along a linear equivalence. -/
def pullback [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (e : V ≃ₗ[Real] W) (D : MetricFiberData W) : MetricFiberData V where
  flat := e.trans (D.flat.trans e.dualMap)
  symm := by
    intro v w
    change D.flat (e v) (e w) = D.flat (e w) (e v)
    exact D.symm (e v) (e w)
  nonneg := by
    intro v
    change 0 <= D.flat (e v) (e v)
    exact D.nonneg (e v)

/-- The Hilbert-Schmidt metric on a finite-dimensional Hom fiber.

Expected construction: the flat map sends `A` to the functional
`B ↦ tr(A† ∘ B)`, where `A†` is the metric adjoint built from `DV` and `DW`.
The proof obligation is that this flat map is symmetric and positive
semidefinite, hence gives genuine metric data on `V →L[Real] W`. -/
def hom [NormedAddCommGroup V] [NormedSpace Real V] [FiniteDimensional Real V]
    [NormedAddCommGroup W] [NormedSpace Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →L[Real] W) := by
  -- The intended proof is the finite-dimensional Hilbert-Schmidt metric
  -- `⟨A,B⟩ = tr(A†B)`, with positivity from a metric-orthonormal basis.
  sorry

end MetricFiberData

/-- The scalar metric on `(0,0)` tensor fibers. -/
def scalarMetricData (_g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
      (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toLinearEquiv)
    MetricFiberData.real

/-- One recursive step for the metric on covariant tensor powers.

Using `tensor0S_curry`, a `(0,s+1)` tensor is a linear map
`T_x M ->L Tensor0SSpace s I x`.  The metric is the Hilbert-Schmidt metric
from the tangent metric and the already constructed metric on `(0,s)` tensors. -/
def tensor0SMetricStep
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) := by
  -- Expected proof: transport across `tensor0S_curry s x`, then use
  -- `MetricFiberData.hom (tangentMetricData g x).metric D` for the
  -- Hilbert-Schmidt metric on `T_x M ->L Tensor0SSpace s I x`.
  sorry

/-- The Riemannian metric on covariant `s`-tensor fibers, constructed
recursively from `g`. -/
def tensor0SMetricData (g : SmoothMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) g x
  | 1 => cotangentMetricData (I := I) g x
  | s + 2 =>
      tensor0SMetricStep (I := I) g x (s + 1) (tensor0SMetricData g x (s + 1))

/-- Metric-induced inner product on covariant tensor fibers. -/
def inner0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) : Real :=
  (tensor0SMetricData (I := I) g x s).inner A B

/-- Metric flat map on covariant tensor fibers. -/
def flat0S
    (g : SmoothMetric I M) (x : M) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[Real] Module.Dual Real (Tensor0SSpace s I x) :=
  (tensor0SMetricData (I := I) g x s).flat

/-- Squared norm of a covariant tensor. -/
def normSq0S
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) : Real :=
  inner0S (I := I) g x s A A

@[simp] theorem normSq0S_eq_inner
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A = inner0S (I := I) g x s A A := by
  rfl

/-- The `(0,1)` tensor metric agrees with the cotangent metric. -/
theorem inner0S_one_eq_cotangent
    (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) :
    inner0S (I := I) g x 1 α β =
      cotangentInner (I := I) g x α β := by
  rfl

/-- Component of a covariant tensor in a pointwise frame. -/
def tensor0SComponent {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) : Real :=
  A (fun a => frame (slots a))

@[simp] theorem tensor0SComponent_apply {Idx : Type*} {s : Nat} {x : M}
    (A : Tensor0SSpace s I x)
    (frame : Idx -> TangentSpace I x)
    (slots : Fin s -> Idx) :
    tensor0SComponent (I := I) A frame slots =
      A (fun a => frame (slots a)) := by
  rfl

/-- Coordinate contraction for the covariant tensor metric. -/
def coordInner0S
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) *
      tensor0SComponent (I := I) A (fun i => basis i) I0 *
        tensor0SComponent (I := I) B (fun i => basis i) J0

/-- Coordinate formula for the covariant tensor metric in a basis.

This is the general tensor-power contraction theorem. The `s = 1` theorem is
proved in `CotangentRiemannian`; the `s = 2` form used by Bochner is exposed
below. The remaining proof is finite-dimensional tensor-basis induction. -/
theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  -- Expected proof: induction on `s`; the step expands through
  -- `tensor0S_curry`, applies the Hilbert-Schmidt metric on Hom fibers, and
  -- uses the cotangent coordinate formula for the new covariant slot.
  sorry

/-- Coordinate formula for the covariant tensor squared norm. -/
theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A basis := by
  rw [normSq0S_eq_inner, inner0S_eq_coord (I := I) g x s basis gInv hinv]

/-- The `(0,2)` coordinate formula in the nested-index form used by Ricci
calculations. -/
theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  -- Expected proof: specialize `inner0S_eq_coord` to `s = 2` and reindex
  -- functions `Fin 2 -> Idx` by pairs of indices.
  sorry

/-- Coordinate squared norms are independent of the chosen frame realization,
because both coordinate sums equal the intrinsic norm. -/
theorem coord_normSq0S_eq_coord
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    (A : Tensor0SSpace s I x) :
    coordInner0S (I := I) (x := x) s gInv₁ A A basis₁ =
      coordInner0S (I := I) (x := x) s gInv₂ A A basis₂ := by
  rw [← normSq0S_eq_coord (I := I) g x s basis₁ gInv₁ hinv₁ A,
    ← normSq0S_eq_coord (I := I) g x s basis₂ gInv₂ hinv₂ A]

end

end Tensor0SBundle
