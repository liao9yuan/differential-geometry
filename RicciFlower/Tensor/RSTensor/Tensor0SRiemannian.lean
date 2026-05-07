import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap

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

/-- The Hilbert-Schmidt flat map on a finite-dimensional algebraic Hom fiber.

Expected construction: the flat map sends `A` to the functional
`B ↦ tr(A† ∘ B)`, where `A†` is the metric adjoint built from `DV` and `DW`.
The proof obligation is that this flat map is symmetric and positive
semidefinite, hence gives genuine metric data on `V →ₗ[Real] W`.

We use algebraic Hom here because the metric is fiberwise. Continuous Hom
models are connected to this one by finite-dimensional continuity equivalences
at the tensor-curry boundary. -/
private def homFlatLinear [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    (V →ₗ[Real] W) →ₗ[Real] Module.Dual Real (V →ₗ[Real] W) where
  toFun A :=
    { toFun := fun B =>
        LinearMap.trace Real V
          ((MetricFiberData.adjoint DV DW A).comp B)
      map_add' := by
        intro B C
        simp [LinearMap.comp_add, map_add]
      map_smul' := by
        intro c B
        simp [LinearMap.comp_smul, map_smul] }
  map_add' := by
    intro A B
    ext C
    have hdual :
        (A + B).dualMap = A.dualMap + B.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((A + B).dualMap).comp DW.flat.toLinearMap)).comp C) =
        LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (A.dualMap.comp DW.flat.toLinearMap)).comp C) +
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (B.dualMap.comp DW.flat.toLinearMap)).comp C)
    rw [hdual]
    simp [LinearMap.add_comp, LinearMap.comp_add, map_add]
  map_smul' := by
    intro c A
    ext B
    have hdual :
        (c • A).dualMap = c • A.dualMap := by
      ext φ x
      simp
    change
      LinearMap.trace Real V
          ((DV.flat.symm.toLinearMap.comp
            (((c • A).dualMap).comp DW.flat.toLinearMap)).comp B) =
        c *
          LinearMap.trace Real V
            ((DV.flat.symm.toLinearMap.comp
              (A.dualMap.comp DW.flat.toLinearMap)).comp B)
    rw [hdual]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, map_smul]

private theorem hom_nonneg [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    Function.Injective (homFlatLinear DV DW) ∧
      (forall A B : V →ₗ[Real] W,
        homFlatLinear DV DW A B = homFlatLinear DV DW B A) ∧
      (forall A : V →ₗ[Real] W, 0 <= homFlatLinear DV DW A A) := by
  -- The intended proof is the finite-dimensional Hilbert-Schmidt metric:
  -- choose a metric-dual basis, rewrite `tr(A†B)` as a finite sum of
  -- component products, then use the resulting sum-of-squares formula for
  -- injectivity and nonnegativity. Symmetry follows from the same coordinate
  -- formula, or equivalently from trace invariance under metric adjoint.
  sorry

def hom [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (DV : MetricFiberData V) (DW : MetricFiberData W) :
    MetricFiberData (V →ₗ[Real] W) :=
  MetricFiberData.ofFlat (homFlatLinear DV DW)
    (hom_nonneg DV DW).1
    (hom_nonneg DV DW).2.1
    (hom_nonneg DV DW).2.2

end MetricFiberData

/-- The scalar metric on `(0,0)` tensor fibers. -/
def scalarMetricData (_g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 0 I x) :=
  MetricFiberData.pullback
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x).toLinearEquiv.trans
      (continuousMultilinearCurryFin0 Real (TangentSpace I x) Real).toLinearEquiv)
    MetricFiberData.real

/-- Algebraic currying map for covariant tensor fibers.

The bundle model gives continuous multilinear maps. For the fiberwise metric
construction we only need the algebraic curried linear map, obtained by
currying the model tensor and translating back to the bundle fiber. -/
private def tensor0S_curryLinearMap (s : Nat) (x : M) :
    Tensor0SSpace (s + 1) I x →ₗ[Real]
      (TangentSpace I x →ₗ[Real] Tensor0SSpace s I x) where
  toFun T :=
    { toFun := fun X =>
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).symm
          (((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x T).curryLeft) X)
      map_add' := by
        intro X Y
        apply (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).injective
        ext v
        simpa [ContinuousMultilinearMap.curryLeft_apply, Fin.update_cons_zero] using
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x T).map_update_add
            (Fin.cons X v) 0 X Y)
      map_smul' := by
        intro c X
        apply (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).injective
        ext v
        simpa [ContinuousMultilinearMap.curryLeft_apply, Fin.update_cons_zero] using
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x T).map_update_smul
            (Fin.cons X v) 0 c X) }
  map_add' := by
    intro A B
    ext X v
    change
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x (A + B))
          (Fin.cons X v)) =
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x A)
            (Fin.cons X v)) +
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x B)
            (Fin.cons X v))
    simp
  map_smul' := by
    intro c A
    ext X v
    change
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x (c • A))
          (Fin.cons X v)) =
        c *
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x A)
            (Fin.cons X v))
    simp

/-- The algebraic currying map is bijective.

This is the fiberwise content of the already-defined continuous currying
equivalence `tensor0S_curry`. The proof should be a direct unpacking of that
equivalence, but Lean currently needs local topological instances for the Hom
target that are not exported cleanly for these bundle fibers. -/
private theorem tensor0S_curryLinearMap_bijective (s : Nat) (x : M) :
    Function.Bijective (tensor0S_curryLinearMap (I := I) (M := M) s x) := by
  sorry

private def tensor0S_curryLinearEquiv (s : Nat) (x : M) :
    Tensor0SSpace (s + 1) I x ≃ₗ[Real]
      (TangentSpace I x →ₗ[Real] Tensor0SSpace s I x) :=
  LinearEquiv.ofBijective
    (tensor0S_curryLinearMap (I := I) (M := M) s x)
    (tensor0S_curryLinearMap_bijective (I := I) (M := M) s x)

/-- One recursive step for the metric on covariant tensor powers.

Using `tensor0S_curryLinearMap`, a `(0,s+1)` tensor is a linear map
`T_x M -> Tensor0SSpace s I x`.  The metric is the Hilbert-Schmidt metric
from the tangent metric and the already constructed metric on `(0,s)` tensors. -/
def tensor0SMetricStep
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) :=
  MetricFiberData.pullback
    (tensor0S_curryLinearEquiv (I := I) (M := M) s x)
    (MetricFiberData.hom (tangentMetricData (I := I) g x).metric D)

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
