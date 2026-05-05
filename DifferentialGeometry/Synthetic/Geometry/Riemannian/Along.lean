import DifferentialGeometry.Synthetic.Axioms

/-!
# Fields Along a Riemannian Curve

This file adds the first curve-level interface used by the synthetic
Riemannian geometry layer.  The project does not yet model points, curves, or
pullback bundles concretely, so the covariant derivative along a curve is
introduced as explicit data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SyntheticGeometry
namespace Riemannian

section Along

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]

/--
Data for vector fields along a fixed curve in a Riemannian manifold.

`R` is the ambient scalar algebra, `V` is the ambient vector-field module,
`A` is the scalar algebra along the curve, and `Gamma` is the module of vector
fields along the curve.
-/
structure AlongCurveData (M : RiemannianManifoldData k R V) where
  /-- Pull back ambient scalar functions to scalar functions along the curve. -/
  scalarPullback : RingHom R A
  /-- Differentiate scalar functions along the curve parameter. -/
  scalarDeriv : A -> A
  /-- Restrict ambient vector fields to vector fields along the curve. -/
  restrict : V -> Gamma
  restrict_add : forall X Y : V, restrict (X + Y) = restrict X + restrict Y
  restrict_smul :
    forall (f : R) (X : V), restrict (f • X) = scalarPullback f • restrict X
  /-- The velocity field `gamma'` along the curve. -/
  velocity : Gamma
  /-- Covariant derivative along the curve. -/
  covDeriv : Gamma -> Gamma
  covDeriv_add :
    forall X Y : Gamma, covDeriv (X + Y) = covDeriv X + covDeriv Y
  covDeriv_smul :
    forall (f : A) (X : Gamma),
      covDeriv (f • X) = scalarDeriv f • X + f • covDeriv X
  /-- Pullback of the Riemannian metric to vector fields along the curve. -/
  metric : Gamma -> Gamma -> A
  metric_symm : forall X Y : Gamma, metric X Y = metric Y X
  metric_add_left :
    forall X Y Z : Gamma, metric (X + Y) Z = metric X Z + metric Y Z
  metric_smul_left :
    forall (f : A) (X Y : Gamma), metric (f • X) Y = f * metric X Y
  metric_restrict :
    forall X Y : V, metric (restrict X) (restrict Y) = scalarPullback (M.met.g X Y)
  /-- Metric compatibility along the curve. -/
  metric_compat :
    forall X Y : Gamma,
      scalarDeriv (metric X Y) = metric (covDeriv X) Y + metric X (covDeriv Y)

variable {M : RiemannianManifoldData k R V}

theorem AlongCurveData.restrict_zero
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) :
    curve.restrict 0 = 0 := by
  have h := curve.restrict_add 0 0
  simp only [zero_add] at h
  have h' : curve.restrict 0 + 0 = curve.restrict 0 + curve.restrict 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem AlongCurveData.covDeriv_zero
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) :
    curve.covDeriv 0 = 0 := by
  simpa using curve.covDeriv_smul (0 : A) (0 : Gamma)

theorem AlongCurveData.metric_zero_left
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (Y : Gamma) :
    curve.metric 0 Y = 0 := by
  simpa using curve.metric_smul_left (0 : A) (0 : Gamma) Y

theorem AlongCurveData.metric_add_right
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (X Y Z : Gamma) :
    curve.metric X (Y + Z) = curve.metric X Y + curve.metric X Z := by
  rw [curve.metric_symm X (Y + Z), curve.metric_add_left,
    curve.metric_symm Y X, curve.metric_symm Z X]

theorem AlongCurveData.metric_smul_right
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (f : A) (X Y : Gamma) :
    curve.metric X (f • Y) = f * curve.metric X Y := by
  rw [curve.metric_symm X (f • Y), curve.metric_smul_left,
    curve.metric_symm Y X]

theorem AlongCurveData.metric_zero_right
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (X : Gamma) :
    curve.metric X 0 = 0 := by
  rw [curve.metric_symm X 0, curve.metric_zero_left]

end Along

end Riemannian
end SyntheticGeometry
