import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Realization.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended
import DifferentialGeometry.ForMathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

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
* `metricPairingSmooth` : the smooth function `x ↦ g_x(X_x,Y_x)`
* `metricCompatibilityDefect` : the `g`-parameterized compatibility defect
* `IsMetricCompatibleWithMetric` : vanishing of that defect
* `concreteMetricCompat` : explicit metric compat implies Synthetic `IsMetricCompatible`
* `concreteIsLeviCivita` : combines metric compat + torsion-free into `IsLeviCivita`

## Strategy

The Synthetic `IsMetricCompatible emb conn met` says:
```
  forall X Y Z, (emb.embed X)(met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)
```

The LHS is the directional derivative of `g(Y,Z)` along X.
The RHS is `g(nabla_X Y, Z) + g(Y, nabla_X Z)`.

The realization-level hypothesis `IsMetricCompatibleWithMetric` asserts exactly the
pointwise identity that connects these.

## Relation to the ForMathlib metric-connection API

`DifferentialGeometry.ForMathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric`
packages metric compatibility as `CovariantDerivative.compatibilityTensor = 0`,
using an `InnerProductSpace` instance on each fiber. This realization file keeps
the metric explicit as a `Bundle.ContMDiffRiemannianMetric g`. That avoids
choosing global ownership of the tangent-fiber inner-product instances in the
synthetic layer.

The intended bridge is:

* if a `CovariantDerivative` is constructed using the same fiber
  norm/module/topology instance package as ForMathlib's metric-connection API,
  and the ForMathlib fiber `inner` is proved pointwise equal to `g.inner`, then
  the product-rule theorem behind `CovariantDerivative.IsCompatible` should
  discharge `IsMetricCompatibleWithMetric`;
* after that, `concreteMetricCompat` and `concreteIsLeviCivita` are the
  synthetic-facing entry points.

We do not install the `RiemannianBundle` induced by `g` globally in this file:
doing so also introduces fiber `NormedAddCommGroup`/module/topology instances,
which can make a previously constructed `CovariantDerivative` live over a
definitionally different bundle instance package.
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

/-! ### Metric compatibility, parameterized by an explicit Riemannian metric -/

/-- The smooth function `x ↦ g_x(X_x,Y_x)`.

This packages the metric pairing once, so compatibility predicates do not need
to carry an inline smoothness proof for every pair of sections. -/
noncomputable def metricPairingSmooth
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y : V_ I M) : R_ I M :=
  (concreteMetricDuality I M g).g X Y

/-- Pointwise evaluation of `metricPairingSmooth`. -/
theorem metricPairingSmooth_apply
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y : V_ I M) (x : M) :
    metricPairingSmooth I M g X Y x = g.inner x (X x) (Y x) :=
  concreteMetricDuality_g_eval I M g X Y x

/-- The smooth metric-compatibility defect of a covariant derivative:

`X(g(Y,Z)) - (g(∇_X Y,Z) + g(Y,∇_X Z))`.

This is the realization-layer analogue of a metric-compatibility tensor, but it
is parameterized by an explicit `ContMDiffRiemannianMetric g`. It therefore
does not force the tangent bundle's module/norm structure to be owned by an
`InnerProductSpace` instance. -/
noncomputable def metricCompatibilityDefect
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Z : V_ I M) : R_ I M :=
  vectorFieldActionSmooth I M X (metricPairingSmooth I M g Y Z) -
    (metricPairingSmooth I M g (concreteConn I M cov X Y) Z +
      metricPairingSmooth I M g Y (concreteConn I M cov X Z))

/-- Pointwise evaluation of `metricCompatibilityDefect`.

This is the explicit-`g` analogue of ForMathlib's
`CovariantDerivative.compatibilityTensor_apply`: it exposes the product-rule
defect
`X(g(Y,Z)) - g(∇_X Y,Z) - g(Y,∇_X Z)` at a point. -/
theorem metricCompatibilityDefect_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y Z : V_ I M) (x : M) :
    metricCompatibilityDefect I M cov g X Y Z x =
      vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x -
        (g.inner x (cov Y x (X x)) (Z x) +
          g.inner x (Y x) (cov Z x (X x))) := by
  simp [metricCompatibilityDefect, metricPairingSmooth, vectorFieldActionSmooth,
    concreteConn_apply, concreteMetricDuality_g_eval]

/-- Metric compatibility of a `CovariantDerivative` with an explicit
`ContMDiffRiemannianMetric`.

This is the preferred realization-layer API. It is deliberately `g`-parameterized
instead of using the `InnerProductSpace` typeclass on tangent fibers. -/
def IsMetricCompatibleWithMetric
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) : Prop :=
  ∀ X Y Z : V_ I M, metricCompatibilityDefect I M cov g X Y Z = 0

/-- Pointwise product-rule form of `IsMetricCompatibleWithMetric`. -/
theorem IsMetricCompatibleWithMetric.apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleWithMetric I M cov g)
    (X Y Z : V_ I M) (x : M) :
    vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) := by
  have hzero := congrArg (fun f : R_ I M => f x) (h_mc X Y Z)
  have hsub :
      vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x -
        (g.inner x (cov Y x (X x)) (Z x) +
          g.inner x (Y x) (cov Z x (X x))) = 0 := by
    simpa [metricCompatibilityDefect, metricPairingSmooth, vectorFieldActionSmooth,
      concreteConn_apply, concreteMetricDuality_g_eval] using hzero
  exact sub_eq_zero.mp hsub

/-- Backwards-compatible name for the old realization metric-compatibility
predicate. New code should use `IsMetricCompatibleWithMetric`. -/
def IsMetricCompatibleMathlib
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) : Prop :=
  IsMetricCompatibleWithMetric I M cov g

/-- Pointwise product-rule form of the backwards-compatible predicate. -/
theorem IsMetricCompatibleMathlib.apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleMathlib I M cov g)
    (X Y Z : V_ I M) (x : M) :
    vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) :=
  IsMetricCompatibleWithMetric.apply I M cov g h_mc X Y Z x

/-! ### Bridge note for ForMathlib's `CovariantDerivative.IsCompatible` -/

/-- If one locally installs the `RiemannianBundle` induced by `g`, the fiber
inner product selected by typeclass inference is the explicit metric field
`g.inner`.

This is the agreement fact behind the intended bridge to ForMathlib's
`CovariantDerivative.IsCompatible`. The full bridge cannot be stated for an
already constructed `cov : CovariantDerivative I E (TangentSpace I)` without
also controlling the whole tangent-fiber norm/module/topology instance package:
installing `RiemannianBundle` locally changes those inferred instances too. -/
theorem metricInner_eq_g_inner_of_local_riemannianBundle
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
      inner ℝ v w) = g.inner x v w := by
  rfl

/-! The following theorem upgrades the explicit metric-compatibility predicate to
the synthetic `IsMetricCompatible` structure. -/

/-!
Historical note: this file used to expose only a pointwise predicate named
`IsMetricCompatibleMathlib`, with an inline smoothness proof for the metric
pairing in the predicate body. The `metricCompatibilityDefect` API above is the
same mathematical content packaged as a smooth function.
-/

/-- If explicit metric compatibility holds, then the Synthetic layer's
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
    (h_mc : IsMetricCompatibleWithMetric I M cov g) :
    IsMetricCompatible (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) := by
  intro X Y Z
  apply ContMDiffMap.ext; intro x
  have h_lhs : ((concreteDerivationEmbedding I M).embed X
      ((concreteMetricDuality I M g).g Y Z)) x =
      vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x := by
    rfl
  rw [h_lhs]
  have h_rhs : ((concreteMetricDuality I M g).g (concreteConn I M cov X Y) Z +
      (concreteMetricDuality I M g).g Y (concreteConn I M cov X Z)) x =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) := by
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval,
        concreteConn_apply, concreteConn_apply]
  rw [h_rhs]
  exact IsMetricCompatibleWithMetric.apply I M cov g h_mc X Y Z x

/-- If the Mathlib `CovariantDerivative` is both metric-compatible and torsion-free,
then the Synthetic `IsLeviCivita` condition holds.

`IsLeviCivita emb conn met` is defined as
`IsMetricCompatible emb conn met /\ IsTorsionFree emb conn`. -/
theorem concreteIsLeviCivita
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleWithMetric I M cov g)
    (h_tf : cov.torsion = 0) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) :=
  ⟨concreteMetricCompat I M cov g h_mc,
   concreteConn_torsion_free I M cov h_tf⟩

/-- P1-facing name for the concrete Levi-Civita bridge.

This is the entry point used by the contracted-Bianchi/Section 12 realization
pipeline: a concrete `CovariantDerivative` whose explicit metric-compatibility
defect vanishes and whose torsion is zero realizes the synthetic
`IsLeviCivita` predicate for `concreteConn` and `concreteMetricDuality`.

The theorem deliberately keeps the metric compatibility hypothesis in the
explicit-`g` form `IsMetricCompatibleWithMetric`. A direct wrapper from the
ForMathlib `CovariantDerivative.IsLeviCivitaConnection` API still needs an
agreement theorem showing that the fiber `inner` selected by typeclass
inference is the same instance package used to construct `cov`. -/
theorem concreteLeviCivita_of_metricCompatible_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_mc : IsMetricCompatibleWithMetric I M cov g)
    (h_tf : cov.torsion = 0) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) :=
  concreteIsLeviCivita I M cov g h_mc h_tf

end LeviCivitaRealization

section ForMathlibLeviCivitaBridge

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- Bridge from the ForMathlib PR-style metric-compatibility predicate to the
explicit-metric predicate used by this realization file.

The extra hypothesis `h_inner` is the only metric-choice agreement needed: it
says the `RiemannianBundle` inner product selected by typeclass inference is
the same pointwise pairing as the chosen `ContMDiffRiemannianMetric g`. -/
theorem isMetricCompatibleWithMetric_of_forMathlib_isCompatibleConnection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_inner : ∀ x (v w : TangentSpace I x), g.inner x v w = inner ℝ v w)
    (hcompat : cov.IsCompatibleConnection) :
    IsMetricCompatibleWithMetric I M cov g := by
  intro X Y Z
  apply ContMDiffMap.ext
  intro x
  rw [metricCompatibilityDefect_apply]
  have h := hcompat (X : ∀ x : M, TangentSpace I x)
    (Y : ∀ x : M, TangentSpace I x)
    (Z : ∀ x : M, TangentSpace I x) x
  have hprod :
      CovariantDerivative.product (I := I) (M := M)
        (Y : ∀ x : M, TangentSpace I x) (Z : ∀ x : M, TangentSpace I x) =
        fun y => g.inner y (Y y) (Z y) := by
    funext y
    simp only [CovariantDerivative.product]
    exact (h_inner y (Y y) (Z y)).symm
  have hprod_left :
      CovariantDerivative.product (I := I) (M := M)
        (fun y => cov Y y (X y)) (Z : ∀ x : M, TangentSpace I x) =
        fun y => g.inner y (cov Y y (X y)) (Z y) := by
    funext y
    simp only [CovariantDerivative.product]
    exact (h_inner y (cov Y y (X y)) (Z y)).symm
  have hprod_right :
      CovariantDerivative.product (I := I) (M := M)
        (Y : ∀ x : M, TangentSpace I x) (fun y => cov Z y (X y)) =
        fun y => g.inner y (Y y) (cov Z y (X y)) := by
    funext y
    simp only [CovariantDerivative.product]
    exact (h_inner y (Y y) (cov Z y (X y))).symm
  rw [hprod, hprod_left, hprod_right] at h
  change vectorFieldAction I M X (metricPairingSmooth I M g Y Z) x -
      (g.inner x (cov Y x (X x)) (Z x) +
        g.inner x (Y x) (cov Z x (X x))) = 0
  have hmetricfun :
      (fun y => g.inner y (Y y) (Z y)) =
        fun y => metricPairingSmooth I M g Y Z y := by
    funext y
    rw [metricPairingSmooth_apply]
  rw [hmetricfun] at h
  unfold vectorFieldAction
  simpa [sub_eq_add_neg] using sub_eq_zero.mpr h

/-- A PR-style metric-compatible, torsion-free concrete covariant derivative is
synthetic Levi-Civita for the explicitly chosen metric `g`, once the chosen
metric agrees with the `RiemannianBundle` inner product. -/
theorem concreteLeviCivita_of_forMathlib_metricCompatible_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_inner : ∀ x (v w : TangentSpace I x), g.inner x v w = inner ℝ v w)
    (hcompat : cov.IsCompatibleConnection)
    (h_tf : cov.torsion = 0) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) :=
  concreteLeviCivita_of_metricCompatible_torsionFree I M cov g
    (isMetricCompatibleWithMetric_of_forMathlib_isCompatibleConnection
      I M cov g h_inner hcompat)
    h_tf

end ForMathlibLeviCivitaBridge

-- ============================================================
-- Koszul formula construction: instantiating Synthetic layer
-- ============================================================

section KoszulRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev V_k := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_k := C^∞⟮I, M; ℝ⟯

/-! ### Invertible (2 : C^∞(M, ℝ))

The constant function `1/2` provides the two-sided inverse of `2` in `C^∞(M, ℝ)`.
We lift `Invertible (2 : ℝ)` through `algebraMap`. -/

/-- `2 : C^∞(M, ℝ)` is invertible (with inverse the constant function `1/2`).
Constructed by mapping `Invertible (2 : ℝ)` through `algebraMap ℝ C^∞(M, ℝ)`. -/
private theorem two_smooth_eval (x : M) : (2 : R_k I M) x = (2 : ℝ) := by
  have h2a : (2 : R_k I M) * (1 : R_k I M) = (2 : R_k I M) := mul_one _
  have h_two_eq : (2 : R_k I M) = (1 : R_k I M) + (1 : R_k I M) := by norm_num
  have := DFunLike.congr_fun h_two_eq x
  simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply] at this
  linarith

noncomputable instance invertible2SmoothFunctions :
    Invertible (2 : R_k I M) where
  invOf := algebraMap ℝ (R_k I M) (1/2 : ℝ)
  invOf_mul_self := by
    apply ContMDiffMap.ext; intro x
    have : (algebraMap ℝ (R_k I M) (1/2 : ℝ) * (2 : R_k I M)) x =
        (1/2 : ℝ) * (2 : R_k I M) x := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num
  mul_invOf_self := by
    apply ContMDiffMap.ext; intro x
    have : ((2 : R_k I M) * algebraMap ℝ (R_k I M) (1/2 : ℝ)) x =
        (2 : R_k I M) x * (1/2 : ℝ) := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num

/-! ### Koszul connection in the concrete setting -/

/-- The Koszul connection on smooth tangent sections, constructed by applying the
Synthetic layer's `koszul_connection` to the concrete `DerivationEmbedding` and
`MetricDuality`. -/
noncomputable def concreteKoszulConnection
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    V_k I M → V_k I M → V_k I M :=
  koszul_connection (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)

/-! ### Koszul connection is Levi-Civita -/

/-- The concrete Koszul connection is the Levi-Civita connection: it is both
metric-compatible and torsion-free. This follows directly from the Synthetic
layer's `levi_civita_exists`. -/
theorem concreteKoszulIsLeviCivita
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteKoszulConnection I M g)
      (concreteMetricDuality I M g) :=
  levi_civita_exists (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
    (char_ne_2_smooth_functions I M)

/-! ### Connection linearity properties -/

/-- Right-additivity of the Koszul connection. -/
theorem concreteKoszul_add_right
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y₁ Y₂ : V_k I M) :
    concreteKoszulConnection I M g X (Y₁ + Y₂) =
    concreteKoszulConnection I M g X Y₁ + concreteKoszulConnection I M g X Y₂ :=
  koszul_connection_add_right (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
    X Y₁ Y₂

/-- Left-additivity of the Koszul connection. -/
theorem concreteKoszul_add_left
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X₁ X₂ Z : V_k I M) :
    concreteKoszulConnection I M g (X₁ + X₂) Z =
    concreteKoszulConnection I M g X₁ Z + concreteKoszulConnection I M g X₂ Z :=
  koszul_connection_add_left (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
    X₁ X₂ Z

/-- Left scalar multiplication for the Koszul connection. -/
theorem concreteKoszul_smul_left
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (f : R_k I M) (X Z : V_k I M) :
    concreteKoszulConnection I M g (f • X) Z =
    f • concreteKoszulConnection I M g X Z :=
  koszul_connection_smul_left (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
    f X Z

/-- Leibniz rule for the Koszul connection. -/
theorem concreteKoszul_leibniz
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X : V_k I M) (f : R_k I M) (Y : V_k I M) :
    concreteKoszulConnection I M g X (f • Y) =
    (concreteDerivationEmbedding I M).embed X f • Y +
    f • concreteKoszulConnection I M g X Y :=
  koszul_connection_leibniz (concreteDerivationEmbedding I M) (concreteMetricDuality I M g)
    (char_ne_2_smooth_functions I M) X f Y

/-! ### Uniqueness: any Levi-Civita connection equals the Koszul connection -/

/-- Any connection that is both metric-compatible and torsion-free must equal
the Koszul connection. This is the concrete instantiation of
`levi_civita_unique` from the Synthetic layer. -/
theorem concreteKoszul_unique
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (conn : V_k I M → V_k I M → V_k I M)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R_k I M) Y,
      conn X (f • Y) = (concreteDerivationEmbedding I M).embed X f • Y + f • conn X Y)
    (h_mc : IsMetricCompatible (concreteDerivationEmbedding I M) conn (concreteMetricDuality I M g))
    (h_tf : IsTorsionFree (concreteDerivationEmbedding I M) conn)
    (X Y : V_k I M) :
    conn X Y = concreteKoszulConnection I M g X Y :=
  levi_civita_unique (concreteDerivationEmbedding I M) conn ha hal hl
    (concreteMetricDuality I M g) (char_ne_2_smooth_functions I M) h_mc h_tf X Y

end KoszulRealization

end
