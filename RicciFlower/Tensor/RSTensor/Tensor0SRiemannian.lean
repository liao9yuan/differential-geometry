import RicciFlower.Tensor.RSTensor.CotangentRiemannian

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

/-- The scalar metric on `(0,0)` tensor fibers. -/
def scalarMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 0 I x) := by
  -- Expected proof: identify `Tensor0SSpace 0 I x` with `ℝ` by
  -- `continuousMultilinearCurryFin0`, then transport the usual scalar metric.
  sorry

/-- One recursive step for the metric on covariant tensor powers.

Using `tensor0S_curry`, a `(0,s+1)` tensor is a linear map
`T_x M ->L Tensor0SSpace s I x`.  The metric is the Hilbert-Schmidt metric
from the tangent metric and the already constructed metric on `(0,s)` tensors. -/
def tensor0SMetricStep
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (D : MetricFiberData (Tensor0SSpace s I x)) :
    MetricFiberData (Tensor0SSpace (s + 1) I x) := by
  -- Expected proof: transport across `tensor0S_curry s x`, then use
  -- `tr(A†B)` for maps `T_x M -> Tensor0SSpace s I x`.
  sorry

/-- The Riemannian metric on covariant `s`-tensor fibers, constructed
recursively from `g`. -/
def tensor0SMetricData (g : SmoothMetric I M) (x : M) :
    (s : Nat) -> MetricFiberData (Tensor0SSpace s I x)
  | 0 => scalarMetricData (I := I) g x
  | s + 1 =>
      tensor0SMetricStep (I := I) g x s (tensor0SMetricData g x s)

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
  sorry

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
    (frame : Idx -> TangentSpace I x) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) *
      tensor0SComponent (I := I) A frame I0 *
        tensor0SComponent (I := I) B frame J0

/-- Coordinate formula for the covariant tensor metric. -/
theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real)
    (_hinv : MetricInverseInFrame (I := I) g x frame gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B frame := by
  -- Expected proof: expand `A` and `B` in the tensor product basis dual to
  -- `frame`, use the product definition of the tensor-power metric, and
  -- contract each cotangent slot with the inverse metric.
  sorry

/-- Coordinate formula for the covariant tensor squared norm. -/
theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInFrame (I := I) g x frame gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A frame := by
  rw [normSq0S_eq_inner, inner0S_eq_coord (I := I) g x s frame gInv hinv]

/-- The `(0,2)` coordinate formula in the nested-index form used by Ricci
calculations. -/
theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (frame : Idx -> TangentSpace I x)
    (gInv : Idx -> Idx -> Real)
    (_hinv : MetricInverseInFrame (I := I) g x frame gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then frame i else frame j) *
            B (fun a : Fin 2 => if a = 0 then frame k else frame l) := by
  -- Expected proof: specialize `inner0S_eq_coord` to `s = 2` and reindex
  -- functions `Fin 2 -> Idx` by pairs of indices.
  sorry

/-- Coordinate squared norms are independent of the chosen frame realization,
because both coordinate sums equal the intrinsic norm. -/
theorem coord_normSq0S_eq_coord
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (frame₁ : Idx₁ -> TangentSpace I x)
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInFrame (I := I) g x frame₁ gInv₁)
    (frame₂ : Idx₂ -> TangentSpace I x)
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInFrame (I := I) g x frame₂ gInv₂)
    (A : Tensor0SSpace s I x) :
    coordInner0S (I := I) (x := x) s gInv₁ A A frame₁ =
      coordInner0S (I := I) (x := x) s gInv₂ A A frame₂ := by
  rw [← normSq0S_eq_coord (I := I) g x s frame₁ gInv₁ hinv₁ A,
    ← normSq0S_eq_coord (I := I) g x s frame₂ gInv₂ hinv₂ A]

end

end Tensor0SBundle
