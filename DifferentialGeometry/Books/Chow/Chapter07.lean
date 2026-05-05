import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import DifferentialGeometry.Synthetic.Operator.LieDerivative
import DifferentialGeometry.Synthetic.Realization.LeviCivita
import DifferentialGeometry.Synthetic.Geometry.Riemannian.Basic

/-!
# Chow, Chapter 7: Riemannian Manifolds

This is a book-ordered Lean companion to Chapter 7 of Chow's lectures.

The file should read like the textbook: sections and declarations follow the
book order.  Low-level implementation work is hidden by importing Mathlib and
the project libraries.  In particular, the Riemannian metric used here is
Mathlib's smooth bundle metric
`Bundle.ContMDiffRiemannianMetric`; we only add book-facing notation and
definitions around it.

The reusable project does not import this file.  It is a reader-facing layer,
not a dependency of the core geometry API.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open BigOperators
open scoped Bundle ContDiff Manifold Topology ENNReal
open Bundle CovariantDerivative SyntheticTensor

namespace SyntheticGeometry
namespace Chow
namespace Chapter07

noncomputable section

/-! ## 7.1 Riemannian metrics -/

section Section_7_1_RiemannianMetrics

/-! ### Definition of a Riemannian metric -/

section DefinitionOfARiemannianMetric

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/--
The book's Riemannian metric, implemented as Mathlib's smooth Riemannian metric
on the tangent bundle.
-/
abbrev RiemannianMetric :=
  Bundle.ContMDiffRiemannianMetric I ω E (fun x : M => TangentSpace I x)

namespace RiemannianMetric

/-- Metric pairing `g_x(V,W)`. -/
def pairing (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V W : TangentSpace I x) : Real :=
  g.inner x V W

theorem symmetric (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V W : TangentSpace I x) :
    g.pairing x V W = g.pairing x W V :=
  g.symm x V W

theorem positive_definite (g : RiemannianMetric (I := I) (M := M))
    (x : M) {V : TangentSpace I x} (hV : V ≠ 0) :
    0 < g.pairing x V V :=
  g.pos x V hV

theorem add_left (g : RiemannianMetric (I := I) (M := M))
    (x : M) (U V W : TangentSpace I x) :
    g.pairing x (U + V) W = g.pairing x U W + g.pairing x V W := by
  simp [pairing]

theorem smul_left (g : RiemannianMetric (I := I) (M := M))
    (x : M) (c : Real) (V W : TangentSpace I x) :
    g.pairing x (c • V) W = c * g.pairing x V W := by
  simp [pairing]

private theorem zero_left (g : RiemannianMetric (I := I) (M := M))
    (x : M) (W : TangentSpace I x) :
    g.pairing x 0 W = 0 := by
  simpa using g.smul_left x (0 : Real) (0 : TangentSpace I x) W

/-- Squared norm `g_x(V,V)`. -/
def normSq (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V : TangentSpace I x) : Real :=
  g.pairing x V V

@[simp] theorem normSq_zero (g : RiemannianMetric (I := I) (M := M))
    (x : M) :
    g.normSq x 0 = 0 := by
  simp [normSq, zero_left]

theorem normSq_pos_of_ne_zero (g : RiemannianMetric (I := I) (M := M))
    (x : M) {V : TangentSpace I x} (hV : V ≠ 0) :
    0 < g.normSq x V :=
  g.positive_definite x hV

theorem normSq_nonneg (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V : TangentSpace I x) :
    0 <= g.normSq x V := by
  by_cases hV : V = 0
  · subst V
    simp
  · exact le_of_lt (g.normSq_pos_of_ne_zero x hV)

/-- Norm `|V| = sqrt(g_x(V,V))`. -/
noncomputable def norm (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V : TangentSpace I x) : Real :=
  Real.sqrt (g.normSq x V)

@[simp] theorem norm_zero (g : RiemannianMetric (I := I) (M := M))
    (x : M) :
    g.norm x 0 = 0 := by
  simp [norm]

theorem norm_sq (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V : TangentSpace I x) :
    g.norm x V ^ 2 = g.normSq x V := by
  rw [norm]
  exact Real.sq_sqrt (g.normSq_nonneg x V)

/--
Angle between two tangent vectors.  The definition is total because Lean's real
division is total; geometrically the intended nondegenerate case is
`V ≠ 0` and `W ≠ 0`.
-/
noncomputable def angle (g : RiemannianMetric (I := I) (M := M))
    (x : M) (V W : TangentSpace I x) : Real :=
  Real.arccos (g.pairing x V W / (g.norm x V * g.norm x W))

end RiemannianMetric

end DefinitionOfARiemannianMetric

/-! ### The metric in local coordinates -/

section TheMetricInLocalCoordinates

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [Module.Finite Real E] [FiniteDimensional Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Local notation for the chart coordinate vector field `∂/∂x^i`. -/
local notation "∂/∂x[" x₀ ", " i "]" =>
  Bundle.Trivialization.localFrame
    (trivializationAt E (TangentSpace I : M → Type _) x₀)
    (Module.finBasis Real E) i

/--
The coordinate frame `∂/∂x^i` is Mathlib's local frame attached to the
tangent-bundle trivialization and the model-space basis.
-/
theorem tangent_localFrame_isLocalFrameOn (x₀ : M) :
    IsLocalFrameOn I E ∞
      (fun i => ∂/∂x[x₀, i])
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
  (trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
    I ∞ (Module.finBasis Real E)

/-- The coordinate components `g_ij = g(∂/∂x^i, ∂/∂x^j)` are symmetric. -/
theorem localFrame_metricComponent_symmetric
    (g : RiemannianMetric (I := I) (M := M)) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (i j : Fin (Module.finrank Real E)) :
    g.pairing x (∂/∂x[x₀, i] x) (∂/∂x[x₀, j] x) =
      g.pairing x (∂/∂x[x₀, j] x) (∂/∂x[x₀, i] x) := by
  have _ :
      ∂/∂x[x₀, i] x =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).basisAt
          (Module.finBasis Real E) hx i :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_apply_of_mem_baseSet
      (b := Module.finBasis Real E) (i := i)
      (hx := hx)
  exact g.symmetric x _ _

/-
Equation (7.4), `g = Σ g_ij dx^i ⊗ dx^j`, is the tensor-basis reconstruction
of the same bilinear form.  The later local-coordinate calculations in this
lecture use `g_ij`, `g^{ij}`, and derivatives of `g_ij` directly, so this book
file keeps the formal surface at the component level instead of adding a
separate `dx^i ⊗ dx^j` reconstruction API here.
-/

end TheMetricInLocalCoordinates

/-! ### Riemannian length and distance -/

section RiemannianLengthAndDistance

open Manifold Set

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [forall x : M, ENorm (TangentSpace I x)]
  [forall x : M, ENormSMulClass Real (TangentSpace I x)]

/-- Smoothness on a closed real interval, matching Mathlib's path-length API. -/
def SmoothOnIcc (I : ModelWithCorners Real E H)
    (gamma : Real -> M) (a b : Real) : Prop :=
  ContMDiffOn 𝓘(Real) I 1 gamma (Icc a b)

/-- Book notation `len(gamma)` for Mathlib's Riemannian path length. -/
noncomputable def length
    (I : ModelWithCorners Real E H) (gamma : Real -> M) (a b : Real) :
    ENNReal :=
  Manifold.pathELength I gamma a b

/-- Book notation `d(x,y)` for Mathlib's Riemannian extended distance. -/
noncomputable def distance
    (I : ModelWithCorners Real E H) (x y : M) : ENNReal :=
  Manifold.riemannianEDist I x y

end RiemannianLengthAndDistance

/-! ### Isometries -/

section Isometries

variable
  {EN HN N EM HM M : Type*}
  [NormedAddCommGroup EN] [NormedSpace Real EN] [CompleteSpace EN]
  [NormedAddCommGroup EM] [NormedSpace Real EM] [CompleteSpace EM]
  [TopologicalSpace HN] {IN : ModelWithCorners Real EN HN}
  [TopologicalSpace HM] {IM : ModelWithCorners Real EM HM}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

/-- Pullback metric value `(F^* g)(V,W) = g(dF(V), dF(W))`. -/
noncomputable def pullbackMetric
    (targetMetric : RiemannianMetric (I := IM) (M := M))
    (F : N -> M) (y : N) (V W : TangentSpace IN y) : Real :=
  targetMetric.pairing (F y)
    (mfderiv IN IM F y V) (mfderiv IN IM F y W)

theorem pullbackMetric_symmetric
    (targetMetric : RiemannianMetric (I := IM) (M := M))
    (F : N -> M) (y : N) (V W : TangentSpace IN y) :
    pullbackMetric targetMetric F y V W =
      pullbackMetric targetMetric F y W V :=
  targetMetric.symmetric (F y)
    (mfderiv IN IM F y V) (mfderiv IN IM F y W)

/-- The differential form of `F^* g = h`. -/
noncomputable def IsometryByPullback
    (sourceMetric : RiemannianMetric (I := IN) (M := N))
    (targetMetric : RiemannianMetric (I := IM) (M := M))
    (F : N -> M) : Prop :=
  forall (y : N) (V W : TangentSpace IN y),
    pullbackMetric targetMetric F y V W = sourceMetric.pairing y V W

theorem IsometryByPullback.apply
    {sourceMetric : RiemannianMetric (I := IN) (M := N)}
    {targetMetric : RiemannianMetric (I := IM) (M := M)}
    {F : N -> M}
    (h : IsometryByPullback sourceMetric targetMetric F)
    (y : N) (V W : TangentSpace IN y) :
    targetMetric.pairing (F y)
      (mfderiv IN IM F y V) (mfderiv IN IM F y W) =
        sourceMetric.pairing y V W :=
  h y V W

end Isometries

/-! ### Metric duality between the tangent and cotangent bundles -/

section MetricDualityBetweenTangentAndCotangent

/-
The musical isomorphisms are already Mathlib constructions once a tangent
fiber carries the inner-product instance induced by a Riemannian metric:
`InnerProductSpace.toDualMap` is `♭`, and `InnerProductSpace.toDual.symm` is
`♯`.  This book file does not wrap them in new definitions.
-/

end MetricDualityBetweenTangentAndCotangent

end Section_7_1_RiemannianMetrics

/-! ## 7.2 Covariant differentiation -/

section Section_7_2_CovariantDifferentiation

/-! ### Definition of the Levi-Civita connection -/

section DefinitionOfTheLeviCivitaConnection

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local notation "𝒳" => Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
local notation "∇[" cov "](" X ", " Y ")" => concreteConn I M cov X Y

/-- `∇_X (Y + Z) = ∇_X Y + ∇_X Z`. -/
theorem connection_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : 𝒳) :
    ∇[cov](X, Y + Z) = ∇[cov](X, Y) + ∇[cov](X, Z) :=
  concreteConn_add_right I M cov X Y Z

/-- `∇_(X+Y) Z = ∇_X Z + ∇_Y Z`. -/
theorem connection_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : 𝒳) :
    ∇[cov](X + Y, Z) = ∇[cov](X, Z) + ∇[cov](Y, Z) :=
  concreteConn_add_left I M cov X Y Z

/-- `∇_(fX) Z = f ∇_X Z`. -/
theorem connection_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (f : C^∞⟮I, M; Real⟯) (X Z : 𝒳) :
    ∇[cov](f • X, Z) = f • ∇[cov](X, Z) :=
  concreteConn_smul_left I M cov f X Z

/-- `∇_X (fY) = X(f)Y + f∇_X Y`. -/
theorem connection_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : 𝒳) (f : C^∞⟮I, M; Real⟯) (Y : 𝒳) :
    ∇[cov](X, f • Y) =
      vectorFieldActionSmooth I M X f • Y + f • ∇[cov](X, Y) :=
  concreteConn_leibniz I M cov X f Y

/--
Metric compatibility in the book's product-rule form:
`X(g(Y,Z)) = g(∇_X Y,Z) + g(Y,∇_X Z)`.
-/
theorem metric_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : RiemannianMetric (I := I) (M := M))
    (h_mc : IsMetricCompatibleMathlib I M cov g)
    (X Y Z : 𝒳) (x : M) :
    ((concreteDerivationEmbedding I M).embed X
        ((concreteMetricDuality I M g).g Y Z)) x =
      g.pairing x (∇[cov](X, Y) x) (Z x) +
        g.pairing x (Y x) (∇[cov](X, Z) x) := by
  have h_syn := concreteMetricCompat I M cov g h_mc
  have hx := congrArg (fun f => f x) (h_syn X Y Z)
  simpa [RiemannianMetric.pairing, concreteConn_apply, concreteMetricDuality_g_eval] using hx

/-- Torsion-free means `∇_X Y - ∇_Y X = [X,Y]`. -/
theorem torsion_free_connection_identity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (h_tf : cov.torsion = 0)
    {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x :=
  cov.torsion_eq_zero_iff.mp h_tf hX hY

/--
The concrete realization of the Levi-Civita condition: a smooth tangent-bundle
covariant derivative that is metric-compatible and torsion-free is Levi-Civita.
-/
theorem isLeviCivita_of_metricCompatible_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (g : RiemannianMetric (I := I) (M := M))
    (h_mc : IsMetricCompatibleMathlib I M cov g)
    (h_tf : cov.torsion = 0) :
    IsLeviCivita (concreteDerivationEmbedding I M)
      (concreteConn I M cov) (concreteMetricDuality I M g) :=
  concreteIsLeviCivita I M cov g h_mc h_tf

end DefinitionOfTheLeviCivitaConnection

/-! ### The Levi-Civita connection in local coordinates -/

section TheLeviCivitaConnectionInLocalCoordinates

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [Module.Finite Real E] [FiniteDimensional Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Local notation for the chart coordinate vector field `∂/∂x^i`. -/
local notation "∂/∂x[" x₀ ", " i "]" =>
  Bundle.Trivialization.localFrame
    (trivializationAt E (TangentSpace I : M → Type _) x₀)
    (Module.finBasis Real E) i

/--
The local-coordinate definition of the Christoffel symbols: the coefficients
of `∇_{∂/∂x^i} ∂/∂x^j` in the coordinate frame.  We leave them as Mathlib
local-frame coefficients rather than introducing a new `Γ` definition.
-/
theorem connection_localFrame_expansion
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (i j : Fin (Module.finrank Real E)) :
    cov (∂/∂x[x₀, j]) x (∂/∂x[x₀, i] x) =
      ∑ k : Fin (Module.finrank Real E),
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame_coeff
          I (Module.finBasis Real E) k x
          (cov (∂/∂x[x₀, j]) x (∂/∂x[x₀, i] x))) •
            ∂/∂x[x₀, k] x := by
  simpa using
    (trivializationAt E (TangentSpace I : M → Type _) x₀).eq_sum_localFrame_coeff_smul
      (I := I) (b := Module.finBasis Real E)
      (s := fun y : M => cov (∂/∂x[x₀, j]) y (∂/∂x[x₀, i] y))
      (x' := x) hx

end TheLeviCivitaConnectionInLocalCoordinates

/-! ### The covariant derivative of covariant tensors -/

section TheCovariantDerivativeOfCovariantTensors

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- For a one-form, `(∇_X α)(Y) = X(α(Y)) - α(∇_X Y)`. -/
theorem covariantDerivative_oneForm_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) (α : V →ₗ[R] R) :
    nabla_dual emb conn ha hl X α Y =
      (emb.embed X) (α Y) - α (conn X Y) := rfl

/--
For a covariant two-tensor,
`(∇_X T)(U,W) = X(T(U,W)) - T(∇_X U,W) - T(U,∇_X W)`.
-/
theorem covariantDerivative_twoTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X U W : V) (T : TensorData R V 0 2) :
    nabla_tensor emb conn ha hl X T ![U, W] ![] =
      (emb.embed X) (T ![U, W] ![]) -
        T ![conn X U, W] ![] - T ![U, conn X W] ![] :=
  nabla_02_eval emb conn ha hl X T U W

end TheCovariantDerivativeOfCovariantTensors

/-! ### Parallel tensors -/

section ParallelTensors

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Metric compatibility is the tensor statement `∇g = 0`. -/
theorem metric_parallel
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X : V) :
    nabla_tensor emb conn ha hl X met.g_tensor = 0 :=
  nabla_g_zero emb conn ha hl met h_mc X

end ParallelTensors

/-! ### The Lie derivative on Riemannian manifolds -/

section TheLieDerivativeOnRiemannianManifolds

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- `L_X g(Y,Z) = g(∇_Y X,Z) + g(Y,∇_Z X)`. -/
theorem lieDerivative_metric_formula
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (conn : V → V → V)
    (h_lc : IsLeviCivita emb conn met)
    (X Y Z : V) :
    lieDerivMetric emb met X Y Z =
      met.g (conn Y X) Z + met.g Y (conn Z X) :=
  lieDerivMetric_eq_nabla emb met conn h_lc.1 h_lc.2 X Y Z

/-- A zero Lie derivative gives the Killing equation. -/
theorem killing_equation_of_lieDerivative_zero
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (conn : V → V → V)
    (h_lc : IsLeviCivita emb conn met)
    (X : V) (hX : ∀ Y Z : V, lieDerivMetric emb met X Y Z = 0)
    (Y Z : V) :
    met.g (conn Y X) Z + met.g Y (conn Z X) = 0 := by
  rw [← lieDerivative_metric_formula emb met conn h_lc X Y Z]
  exact hX Y Z

end TheLieDerivativeOnRiemannianManifolds

end Section_7_2_CovariantDifferentiation

/-! ## 7.3 Geodesics -/

section Section_7_3_Geodesics

/-! ### Covariant derivative along a map -/

section CovariantDerivativeAlongAMap

variable
  {EN HN N EM HM M : Type*}
  [NormedAddCommGroup EN] [NormedSpace Real EN]
  [TopologicalSpace HN] {IN : ModelWithCorners Real EN HN}
  [TopologicalSpace N] [ChartedSpace HN N]
  [NormedAddCommGroup EM] [NormedSpace Real EM]
  [TopologicalSpace HM] {IM : ModelWithCorners Real EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

/--
A vector field along a map `F : N -> M` is a dependent function
`p ↦ V p ∈ T_{F p}M`.
-/
abbrev VectorFieldAlong (F : N -> M) :=
  forall p : N, TangentSpace IM (F p)

/-- A usual vector field is exactly a vector field along the identity map. -/
theorem vectorFieldAlong_id :
    VectorFieldAlong (IM := IM) (fun x : M => x) =
      (forall x : M, TangentSpace IM x) := rfl

/-- Ambient vector fields restrict to vector fields along `F`. -/
def restrictVectorFieldAlong (F : N -> M)
    (Vbar : forall x : M, TangentSpace IM x) :
    VectorFieldAlong (IM := IM) F :=
  fun p => Vbar (F p)

@[simp] theorem restrictVectorFieldAlong_apply
    (F : N -> M) (Vbar : forall x : M, TangentSpace IM x) (p : N) :
    restrictVectorFieldAlong (IM := IM) F Vbar p = Vbar (F p) := rfl

/-- The differential `dF(Y)` as a vector field along `F`. -/
noncomputable def differentialAlong (F : N -> M)
    (Y : forall p : N, TangentSpace IN p) :
    VectorFieldAlong (IM := IM) F :=
  fun p => mfderiv IN IM F p (Y p)

@[simp] theorem differentialAlong_apply
    (F : N -> M) (Y : forall p : N, TangentSpace IN p) (p : N) :
    differentialAlong (IN := IN) (IM := IM) F Y p =
      mfderiv IN IM F p (Y p) := rfl

end CovariantDerivativeAlongAMap

/-! ### Covariant derivative along a path -/

section CovariantDerivativeAlongAPath

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The velocity field `t ↦ gamma'(t)` as a vector field along a path. -/
noncomputable def pathVelocity (gamma : Real -> M) :
    VectorFieldAlong (N := Real) (IM := I) gamma :=
  fun t => mfderiv 𝓘(Real) I gamma t 1

@[simp] theorem pathVelocity_apply (gamma : Real -> M) (t : Real) :
    pathVelocity (I := I) gamma t = mfderiv 𝓘(Real) I gamma t 1 := rfl

end CovariantDerivativeAlongAPath

/-! ### Parallel vector fields along maps -/

section ParallelVectorFieldsAlongMaps

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {RM : RiemannianManifoldData k R V}

/-- The covariant derivative along a curve satisfies the Leibniz rule. -/
theorem covariantDerivativeAlong_smul
    (curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM)
    (f : A) (X : Gamma) :
    curve.covDeriv (f • X) = curve.scalarDeriv f • X + f • curve.covDeriv X :=
  curve.covDeriv_smul f X

/-- Metric product rule along a curve. -/
theorem metricProductRule_along
    (curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM)
    (X Y : Gamma) :
    curve.scalarDeriv (curve.metric X Y) =
      curve.metric (curve.covDeriv X) Y + curve.metric X (curve.covDeriv Y) :=
  curve.metric_compat X Y

/-- A vector field along a curve is parallel iff its covariant derivative vanishes. -/
theorem parallelAlong_iff
    (curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM)
    (X : Gamma) :
    Riemannian.IsParallelAlong curve X ↔ curve.covDeriv X = 0 := Iff.rfl

/-- Inner products of parallel fields along a curve are constant. -/
theorem scalarDeriv_metric_eq_zero_of_parallel
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM}
    {X Y : Gamma}
    (hX : Riemannian.IsParallelAlong curve X)
    (hY : Riemannian.IsParallelAlong curve Y) :
    curve.scalarDeriv (curve.metric X Y) = 0 :=
  Riemannian.scalarDeriv_metric_eq_zero_of_parallel hX hY

end ParallelVectorFieldsAlongMaps

/-! ### Definition of geodesic -/

section DefinitionOfGeodesic

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {RM : RiemannianManifoldData k R V}

/-- An affinely parametrized geodesic has parallel velocity. -/
theorem affineGeodesic_iff_velocity_parallel
    (curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM) :
    Riemannian.IsAffineGeodesic curve ↔
      Riemannian.IsParallelAlong curve curve.velocity := Iff.rfl

/-- In coordinates, an affinely parametrized geodesic satisfies the usual ODE. -/
theorem geodesic_coordinate_equation
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM} {n : Nat}
    (coord : Riemannian.CoordinateCurveData curve n)
    (hgeo : Riemannian.IsAffineGeodesic curve) (a : Fin n) :
    coord.accelerationCoord a + coord.christoffelQuadratic a = 0 :=
  Riemannian.coordinate_geodesic_equation coord hgeo a

/-- Affinely parametrized geodesics have constant squared speed. -/
theorem hasConstantSpeed_of_affineGeodesic
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM}
    (hgeo : Riemannian.IsAffineGeodesic curve) :
    Riemannian.HasConstantSpeed curve :=
  Riemannian.hasConstantSpeed_of_affineGeodesic hgeo

/--
The book's unparametrized geodesic condition is represented here by
`IsPregeodesic`: acceleration is pointwise tangent to the velocity.
-/
theorem isPregeodesic_of_affineGeodesic
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM}
    (hgeo : Riemannian.IsAffineGeodesic curve) :
    Riemannian.IsPregeodesic curve :=
  Riemannian.isPregeodesic_of_affineGeodesic hgeo

/-- A solved initial-value problem supplies an affinely parametrized geodesic. -/
theorem geodesicSolution_isAffineGeodesic
    {Point Tangent : Type*}
    {initial : Riemannian.GeodesicInitialData Point Tangent}
    (sol :
      Riemannian.GeodesicSolutionData
        (A := A) (Gamma := Gamma) (M := RM) Point Tangent initial) :
    Riemannian.IsAffineGeodesic sol.curve :=
  sol.geodesic

end DefinitionOfGeodesic

end Section_7_3_Geodesics

/-! ## 7.4 First variation of arc length -/

section Section_7_4_FirstVariationOfArcLength

/-! ### One-parameter families of paths -/

section OneParameterFamiliesOfPaths

variable
  {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A one-parameter family of paths, written `gamma v t = gamma_v(t)`. -/
abbrev OneParameterFamilyOfPaths :=
  Real -> Real -> M

/-- The path `gamma_v` from a one-parameter family. -/
def familyPath (gamma : OneParameterFamilyOfPaths (M := M)) (v : Real) : Real -> M :=
  fun t => gamma v t

/-- The tangent field `T(t,v) = ∂_t gamma_v(t)` along the path `gamma_v`. -/
noncomputable def familyTangentField
    (gamma : OneParameterFamilyOfPaths (M := M)) (v : Real) :
    VectorFieldAlong (N := Real) (IM := I) (familyPath gamma v) :=
  pathVelocity (I := I) (familyPath gamma v)

/-- The variation field `V(t,v) = ∂_v gamma_v(t)` along the path `gamma_v`. -/
noncomputable def familyVariationField
    (gamma : OneParameterFamilyOfPaths (M := M)) (v : Real) :
    VectorFieldAlong (N := Real) (IM := I) (familyPath gamma v) :=
  fun t => mfderiv 𝓘(Real) I (fun w : Real => gamma w t) v 1

@[simp] theorem familyPath_apply
    (gamma : OneParameterFamilyOfPaths (M := M)) (v t : Real) :
    familyPath gamma v t = gamma v t := rfl

@[simp] theorem familyTangentField_apply
    (gamma : OneParameterFamilyOfPaths (M := M)) (v t : Real) :
    familyTangentField (I := I) gamma v t =
      mfderiv 𝓘(Real) I (familyPath gamma v) t 1 := rfl

@[simp] theorem familyVariationField_apply
    (gamma : OneParameterFamilyOfPaths (M := M)) (v t : Real) :
    familyVariationField (I := I) gamma v t =
      mfderiv 𝓘(Real) I (fun w : Real => gamma w t) v 1 := rfl

/-- The arc-length functional of the family, using Mathlib's path length. -/
noncomputable def familyLength
    (gamma : OneParameterFamilyOfPaths (M := M)) (a b v : Real) : ENNReal :=
  length I (familyPath gamma v) a b

end OneParameterFamiliesOfPaths

/-! ### First variation of arc length formula -/

section FirstVariationFormula

variable {R : Type*} [CommRing R]

/--
If the boundary term vanishes, the first variation formula reduces to the
interior term.
-/
theorem firstVariationFormula_fixedEndpoints
    {firstVariation interior boundary : R}
    (h_formula : firstVariation = -interior + boundary)
    (h_boundary : boundary = 0) :
    firstVariation = -interior := by
  rw [h_formula, h_boundary, add_zero]

/--
For a geodesic variation with fixed initial point, the first variation is the
terminal boundary pairing.
-/
theorem firstVariationFormula_geodesic_fixedInitial
    {firstVariation interior initialBoundary terminalBoundary : R}
    (h_formula : firstVariation = -interior + (terminalBoundary - initialBoundary))
    (h_geodesic : interior = 0)
    (h_initial : initialBoundary = 0) :
    firstVariation = terminalBoundary := by
  rw [h_formula, h_geodesic, h_initial]
  ring

end FirstVariationFormula

/-! ### Geodesics are critical points of the arc length functional -/

section GeodesicsAreCriticalPoints

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {RM : RiemannianManifoldData k R V}

/-- Fermat's theorem for the one-parameter length functional. -/
theorem firstVariation_eq_zero_of_localMin
    {lengthAt : Real -> Real} {firstVariation : Real}
    (hmin : IsLocalMin lengthAt 0)
    (hderiv : HasDerivAt lengthAt firstVariation 0) :
    firstVariation = 0 :=
  Riemannian.firstVariation_eq_zero_of_localMin hmin hderiv

/--
The Euler-Lagrange output of the first variation formula gives the affine
geodesic equation.
-/
theorem isAffineGeodesic_of_firstVariationStationary
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM}
    (hnondeg : Riemannian.AlongMetricNondegenerate curve)
    (hstationary : Riemannian.FirstVariationStationary curve) :
    Riemannian.IsAffineGeodesic curve :=
  Riemannian.isAffineGeodesic_of_firstVariationStationary hnondeg hstationary

end GeodesicsAreCriticalPoints

/-! ### Minimal geodesics -/

section MinimalGeodesics

open Manifold Set

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {RM : RiemannianManifoldData k R V}

variable
  {E H X : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [forall x : X, ENormSMulClass Real (TangentSpace I x)]

/--
A smooth path realizing the Riemannian distance is length-minimizing among
smooth competitors with the same endpoints.
-/
theorem isLengthMinimizingOnIcc_of_realizes_riemannianEDist
    {path : Real -> X} {a b : Real}
    (hab : a <= b)
    (hpath : Riemannian.SmoothOnIcc I path a b)
    (hrealizes : Riemannian.RealizesRiemannianEDist I path a b) :
    Riemannian.IsLengthMinimizingOnIcc I path a b :=
  Riemannian.isLengthMinimizingOnIcc_of_realizes_riemannianEDist
    (I := I) hab hpath hrealizes

/--
This is the formal bridge used by the text's statement that distance-realizing
smooth paths are geodesics.  The remaining analytic input is isolated as
`LengthMinimizingGivesFirstVariationStationarity`.
-/
theorem isAffineGeodesic_of_realizes_riemannianEDist
    {path : Real -> X} {a b : Real}
    {curve : Riemannian.AlongCurveData (A := A) (Gamma := Gamma) RM}
    (hab : a <= b)
    (hpath : Riemannian.SmoothOnIcc I path a b)
    (hrealizes : Riemannian.RealizesRiemannianEDist I path a b)
    (hnondeg : Riemannian.AlongMetricNondegenerate curve)
    (hfirstVariation :
      Riemannian.LengthMinimizingGivesFirstVariationStationarity I path a b curve) :
    Riemannian.IsAffineGeodesic curve :=
  Riemannian.isAffineGeodesic_of_realizes_riemannianEDist
    (I := I) hab hpath hrealizes hnondeg hfirstVariation

end MinimalGeodesics

end Section_7_4_FirstVariationOfArcLength

end

end Chapter07
end Chow
end SyntheticGeometry
