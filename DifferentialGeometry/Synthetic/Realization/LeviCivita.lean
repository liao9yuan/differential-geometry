/-
Copyright (c) 2026 Differential Geometry Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DifferentialGeometry.Synthetic.Realization.Connection
import DifferentialGeometry.Synthetic.Realization.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended

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
