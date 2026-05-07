import RicciFlower.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metric Data on Fibers

This file contains the finite-dimensional pointwise metric interface used by
the tensor bundle layer.  It does not construct tensor-power metrics by
choice.  Instead, later files take explicit metric-extension data tied to a
given Riemannian metric.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

/-- Metric data on a finite-dimensional real vector-space fiber, packaged by
its flat isomorphism.  Symmetry and nonnegativity are included because this is
intended to model a genuine pointwise inner product, not just an arbitrary
linear equivalence to the dual. -/
structure MetricFiberData (V : Type*) [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] where
  flat : V ≃ₗ[Real] Module.Dual Real V
  symm : forall v w : V, flat v w = flat w v
  nonneg : forall v : V, 0 <= flat v v

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm

/-- Build metric data from an injective flat map into the dual. -/
def ofFlat
    (flat : V →ₗ[Real] Module.Dual Real V)
    (hinj : Function.Injective flat)
    (hsymm : forall v w : V, flat v w = flat w v)
    (hnonneg : forall v : V, 0 <= flat v v) :
    MetricFiberData V where
  flat := LinearMap.linearEquivOfInjective flat hinj dual_finrank_eq
  symm := hsymm
  nonneg := hnonneg

/-- Inner product associated to a metric flat isomorphism. -/
def inner (D : MetricFiberData V) (v w : V) : Real :=
  D.flat v w

/-- Sharp isomorphism associated to `MetricFiberData`. -/
def sharp (D : MetricFiberData V) : Module.Dual Real V ≃ₗ[Real] V :=
  D.flat.symm

@[simp] theorem inner_apply (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.flat v w := by
  rfl

theorem inner_comm (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.inner w v := by
  exact D.symm v w

theorem inner_nonneg (D : MetricFiberData V) (v : V) :
    0 <= D.inner v v := by
  exact D.nonneg v

end MetricFiberData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Tensor-folder alias for a smooth Riemannian metric on `TM`. -/
abbrev SmoothMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ⊤ E (TangentSpace I : M -> Type _)

/-- The tangent flat map induced by a smooth Riemannian metric. -/
def tangentFlatLinear (g : SmoothMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

@[simp] theorem tangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinear (I := I) g x v w = g.inner x v w := by
  rfl

/-- The tangent flat map is injective by positive-definiteness. -/
theorem tangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (tangentFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

/-- The tangent flat equivalence induced by a smooth Riemannian metric. -/
def tangentFlatEquiv (g : SmoothMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinear (I := I) g x)
    (tangentFlatLinear_injective (I := I) g x)
    MetricFiberData.dual_finrank_eq

@[simp] theorem tangentFlatEquiv_apply
    (g : SmoothMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatEquiv (I := I) g x v w = g.inner x v w := by
  rfl

/-- Explicit pointwise metric data on `T_x M` tied to the Riemannian metric `g`.

This is an interface, not an existence theorem.  The eventual construction
should fill `metric` with the flat map induced by `g.inner`. -/
structure TangentMetricData
    (g : SmoothMetric I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y

/-- The tangent metric data constructed from the Riemannian metric. -/
def tangentMetricData (g : SmoothMetric I M) (x : M) :
    TangentMetricData (I := I) g x where
  metric :=
    { flat := tangentFlatEquiv (I := I) g x
      symm := by
        intro X Y
        exact g.symm x X Y
      nonneg := by
        intro X
        by_cases hX : X = 0
        · simp [hX]
        · exact le_of_lt (g.pos x X hX) }
  realizes_inner := by
    intro X Y
    rfl

namespace TangentMetricData

@[simp] theorem inner_eq
    {g : SmoothMetric I M} {x : M} (D : TangentMetricData (I := I) g x)
    (X Y : TangentSpace I x) :
    D.metric.inner X Y = g.inner x X Y :=
  D.realizes_inner X Y

end TangentMetricData

end

end Tensor0SBundle
