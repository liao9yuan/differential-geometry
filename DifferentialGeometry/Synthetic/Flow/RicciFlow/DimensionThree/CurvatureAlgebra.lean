import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Three-Dimensional Curvature Algebra Interfaces

The Hamilton theorem in `RicciFlow/main.tex` uses curvature identities special
to dimension three. This file records those targets without committing the
project to a concrete finite-dimensional basis API yet.
-/

open SyntheticTensor

section DimensionThree

/-- Marker for the three-dimensional algebra layer. -/
structure IsDimensionThree (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] : Prop where
  curvature_operator_rank_three : True

end DimensionThree

section CurvatureIdentities

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Interface for the 3D formula expressing Riemann curvature through Ricci and scalar curvature. -/
def RiemannFromRicciFormula
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (_ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (_hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (_hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (_hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (rhs : V -> V -> V -> V -> R) : Prop :=
  forall X Y Z W, met.g (Rm emb conn X Y Z) W = rhs X Y Z W

/-- Numerator of sectional curvature; denominator normalization is a later bridge target. -/
noncomputable def sectional_curvature_numerator
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (X Y : V) : R :=
  met.g (Rm emb conn X Y Y) X

/-- Nonnegative Ricci curvature as a pointwise quadratic-form condition. -/
def NonnegativeRicci [Preorder R]
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) : Prop :=
  forall X, 0 <= ricciForm_tensor emb conn ha hal hsl hl atr ![X, X] ![]

/-- Interface for the estimate that, in dimension three, nonnegative Ricci controls Riemann. -/
def CurvatureControlledByRicci [Preorder R]
    (rmNorm ricciNorm constant : R) : Prop :=
  rmNorm <= constant * ricciNorm

theorem curvature_control_from_interface [Preorder R]
    (rmNorm ricciNorm constant : R)
    (h : CurvatureControlledByRicci rmNorm ricciNorm constant) :
    rmNorm <= constant * ricciNorm :=
  h

end CurvatureIdentities
