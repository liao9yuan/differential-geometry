/-
Copyright (c) 2026 Differential Geometry Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Realization.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection

/-!
# Realization: Levi-Civita (Metric Compatibility and Torsion-Free)

This file connects Mathlib's concrete metric compatibility for a `CovariantDerivative`
to the Synthetic layer's `IsMetricCompatible` and `IsLeviCivita` conditions.

Given a Mathlib `CovariantDerivative cov` on TM and a `ContMDiffRiemannianMetric g`,
if the Mathlib-level metric compatibility holds (the directional derivative of the
inner product decomposes via the connection), then the Synthetic layer's abstract
`IsMetricCompatible` condition holds.

Combined with the torsion-free result from `Connection.lean`, this gives `IsLeviCivita`.

## Main definitions

* `concreteMetricDuality` : assembles the full `MetricDuality` from `Metric.lean` components
* `IsMetricCompatibleMathlib` : Mathlib-level metric compatibility predicate
* `concreteMetricCompat` : Mathlib metric compat implies Synthetic `IsMetricCompatible`
* `concreteIsLeviCivita` : combines metric compat + torsion-free into `IsLeviCivita`

## Strategy

The Synthetic `IsMetricCompatible emb conn met` says:
```
  forall X Y Z, (emb.embed X)(met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)
```

The LHS is the directional derivative of `g(Y,Z)` along X.
The RHS is `g(nabla_X Y, Z) + g(Y, nabla_X Z)`.

The Mathlib-level hypothesis `IsMetricCompatibleMathlib` asserts exactly the
pointwise identity that connects these.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle SyntheticTensor CovariantDerivative

section LeviCivitaRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-! ### concreteMetricDuality: assembling MetricDuality from Metric.lean components -/

/-- The full `MetricDuality` structure assembled from the components proved in `Metric.lean`.

Given a `ContMDiffRiemannianMetric g` on the tangent bundle, this packages:
* `g_tensor` : the metric as a (0,2)-tensor (`concreteGTensor`)
* `symm_tensor` : symmetry (`concreteGTensor_symm`)
* `g_inv` : the inverse metric (`concreteGInv`)
* `eq_of_forall_g_eq` : nondegeneracy (`concreteGTensor_nondegenerate`)
* `inverse_eval` : `g^{-1}(alpha, flat(Y)) = alpha(Y)` (`concreteGInv_inverse_eval`)
* `sharp_spec` : every covector is in the image of flat (`concreteGTensor_sharp_spec`) -/
noncomputable def concreteMetricDuality
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    MetricDuality (R_ I M) (V_ I M) where
  g_tensor := concreteGTensor I M g
  symm_tensor := concreteGTensor_symm I M g
  g_inv := concreteGInv I M g
  eq_of_forall_g_eq := concreteGTensor_nondegenerate I M g
  inverse_eval Y α := concreteGInv_inverse_eval I M g Y α
  sharp_spec α := concreteGTensor_sharp_spec I M g α

/-- The `g` field of `concreteMetricDuality` evaluates pointwise to the inner product. -/
theorem concreteMetricDuality_g_eval
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y : V_ I M) (x : M) :
    (concreteMetricDuality I M g).g X Y x = g.inner x (X x) (Y x) := by
  simp [concreteMetricDuality, MetricDuality.g, concreteGTensor_eval_pt]

/-! ### Mathlib-level metric compatibility -/

/-- Mathlib-level metric compatibility for a `CovariantDerivative` and a Riemannian metric.

This states that the directional derivative of the inner product decomposes via the
connection: for all smooth sections X, Y, Z and all points x,

```
  vectorFieldAction X (met.g Y Z) x = g.inner x (cov Y x (X x)) (Z x)
                                     + g.inner x (Y x) (cov Z x (X x))
```

The LHS is `extDerivFun (fun y => g.inner y (Y y) (Z y)) x (X x)`, i.e., the
directional derivative of the smooth function `y mapsto g_y(Y_y, Z_y)` along X. -/
def IsMetricCompatibleMathlib
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) : Prop :=
  ∀ (X Y Z : V_ I M) (x : M),
    vectorFieldAction I M X
      ⟨fun y => g.inner y (Y y) (Z y), by
        intro x₀
        have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
            (fun x => (⟨x, g.inner x⟩ :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) :=
          g.contMDiff.of_le le_top
        have hgX : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
            (fun x => (⟨x, g.inner x (Y x)⟩ :
              TotalSpace (E →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] ℝ))) x₀ :=
          ContMDiffAt.clm_bundle_apply hg.contMDiffAt Y.contMDiff.contMDiffAt
        have hgXY : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
            (fun x => (⟨x, g.inner x (Y x) (Z x)⟩ :
              TotalSpace ℝ (fun _ : M => ℝ))) x₀ :=
          ContMDiffAt.clm_bundle_apply hgX Z.contMDiff.contMDiffAt
        simp only [contMDiffAt_totalSpace] at hgXY
        exact hgXY.2⟩ x =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x))

/-- If the Mathlib-level metric compatibility holds, then the Synthetic layer's
`IsMetricCompatible` condition holds.

The proof is pointwise: at each `x : M`, the Synthetic `IsMetricCompatible` identity
```
  (emb.embed X)(met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)
```
reduces (after unfolding definitions) to exactly the Mathlib hypothesis. -/
theorem concreteMetricCompat
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleMathlib I M cov g) :
    IsMetricCompatible (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) := by
  intro X Y Z
  apply ContMDiffMap.ext; intro x
  -- Unfold both sides to pointwise expressions
  -- LHS: ((concreteDerivationEmbedding I M).embed X) ((concreteMetricDuality I M g).g Y Z) x
  -- = (embedLinearMap I M X) ((concreteMetricDuality I M g).g Y Z) x
  -- = (embedDeriv I M X) ((concreteMetricDuality I M g).g Y Z) x
  -- = (vectorFieldActionSmooth I M X ((concreteMetricDuality I M g).g Y Z)) x
  -- = vectorFieldAction I M X ((concreteMetricDuality I M g).g Y Z) x
  -- The key is that (concreteMetricDuality I M g).g Y Z is the smooth function
  -- whose underlying function is fun y => g.inner y (Y y) (Z y)
  -- RHS: ((concreteMetricDuality I M g).g (concreteConn I M cov X Y) Z
  --      + (concreteMetricDuality I M g).g Y (concreteConn I M cov X Z)) x
  -- = g.inner x (concreteConn I M cov X Y x) (Z x)
  --   + g.inner x (Y x) (concreteConn I M cov X Z x)
  -- = g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x))

  -- The LHS unfolds to vectorFieldAction applied to met.g Y Z
  -- met.g Y Z is a ContMDiffMap whose underlying function matches the one in IsMetricCompatibleMathlib
  have h_lhs : ((concreteDerivationEmbedding I M).embed X
      ((concreteMetricDuality I M g).g Y Z)) x =
      vectorFieldAction I M X ((concreteMetricDuality I M g).g Y Z) x := by
    rfl
  rw [h_lhs]
  -- The RHS unfolds using concreteMetricDuality_g_eval and concreteConn_apply
  have h_rhs : ((concreteMetricDuality I M g).g (concreteConn I M cov X Y) Z +
      (concreteMetricDuality I M g).g Y (concreteConn I M cov X Z)) x =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) := by
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval,
        concreteConn_apply, concreteConn_apply]
  rw [h_rhs]
  -- Now need: vectorFieldAction I M X ((concreteMetricDuality I M g).g Y Z) x = RHS
  -- The key: (concreteMetricDuality I M g).g Y Z has the same underlying function as the
  -- smooth function in the IsMetricCompatibleMathlib hypothesis
  -- vectorFieldAction only depends on the underlying function (via extDerivFun)
  have h_fn_eq : ((concreteMetricDuality I M g).g Y Z : M → ℝ) =
      (fun y => g.inner y (Y y) (Z y)) := by
    ext y; exact concreteMetricDuality_g_eval I M g Y Z y
  -- vectorFieldAction uses extDerivFun which only depends on the underlying function
  simp only [vectorFieldAction]
  -- Now LHS is extDerivFun ((concreteMetricDuality I M g).g Y Z) x (X x)
  -- and we need to show this equals the RHS.
  -- Since the underlying functions are equal, extDerivFun gives the same result.
  -- extDerivFun is defined using mfderiv, which depends only on the germ of the function.
  -- Since the underlying functions are pointwise equal everywhere, they are equal.
  have : ((concreteMetricDuality I M g).g Y Z : M → ℝ) =
      (fun y => g.inner y (Y y) (Z y)) := h_fn_eq
  rw [this]
  exact h_mc X Y Z x

/-- If the Mathlib `CovariantDerivative` is both metric-compatible and torsion-free,
then the Synthetic `IsLeviCivita` condition holds.

`IsLeviCivita emb conn met` is defined as
`IsMetricCompatible emb conn met /\ IsTorsionFree emb conn`. -/
theorem concreteIsLeviCivita
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleMathlib I M cov g)
    (h_tf : cov.torsion = 0) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) :=
  ⟨concreteMetricCompat I M cov g h_mc,
   concreteConn_torsion_free I M cov h_tf⟩

end LeviCivitaRealization

end
