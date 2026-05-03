import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.CurvatureAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Dimension-Three Pinching Interfaces

This module names the positivity and pinching targets used in Hamilton's
three-dimensional positive Ricci theorem.
-/

open SyntheticTensor

section PinchingDefinitions

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Positive Ricci curvature as a pointwise quadratic-form condition. -/
def RicciPositive
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) : Prop :=
  forall X, 0 < ricciForm_tensor emb conn ha hal hsl hl atr ![X, X] ![]

/-- A Ricci pinching cone written in quadratic-form form. -/
def RicciPinched
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (delta : R) : Prop :=
  forall X,
    delta * ScalarCurvature emb conn ha hal hsl hl atr met * met.g X X <=
      ricciForm_tensor emb conn ha hal hsl hl atr ![X, X] ![]

/-- Named algebraic terms for Hamilton's improved pinching calculation. -/
structure HamiltonPinchingTerms (R : Type*) where
  P : R
  Q : R
  scalar : R
  tracefreeNorm : R

/-- Interface for the lower bound on the cubic reaction term. -/
def PinchingReactionLowerBound {R : Type*} [Preorder R]
    (terms : HamiltonPinchingTerms R) (lower : R) : Prop :=
  lower <= terms.Q

/-- Interface for the final improved pinching estimate. -/
def ImprovedPinchingEstimate {R : Type*} [Preorder R] (P bound : R) : Prop :=
  P <= bound

theorem improved_pinching_from_interface {R : Type*} [Preorder R] (P bound : R)
    (h : ImprovedPinchingEstimate P bound) :
    P <= bound :=
  h

end PinchingDefinitions

