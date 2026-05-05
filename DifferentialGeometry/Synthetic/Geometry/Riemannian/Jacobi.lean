import DifferentialGeometry.Synthetic.Geometry.Riemannian.Geodesic

/-!
# Synthetic Jacobi Fields

This file introduces Jacobi fields once a curve has an along-curve covariant
derivative and a curvature term along the curve.  The curvature term is kept as
data for now; a later realization layer can connect it to `Rm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SyntheticGeometry
namespace Riemannian

section Jacobi

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {M : RiemannianManifoldData k R V}

/-- Curvature operator restricted to vector fields along a curve. -/
structure CurvatureAlongData
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) where
  curvatureAlong : Gamma -> Gamma -> Gamma -> Gamma
  curvature_add_left :
    forall X Y Z W : Gamma,
      curvatureAlong (X + Y) Z W = curvatureAlong X Z W + curvatureAlong Y Z W
  curvature_smul_left :
    forall (f : A) (X Y Z : Gamma),
      curvatureAlong (f • X) Y Z = f • curvatureAlong X Y Z

/--
Jacobi operator along a curve:

`J |-> D_t(D_t J) + R(J, gamma') gamma'`.
-/
def jacobiOperator
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (curv : CurvatureAlongData curve) (J : Gamma) : Gamma :=
  curve.covDeriv (curve.covDeriv J) +
    curv.curvatureAlong J curve.velocity curve.velocity

/-- A Jacobi field is a field killed by the Jacobi operator. -/
def IsJacobiField
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (curv : CurvatureAlongData curve) (J : Gamma) : Prop :=
  jacobiOperator curv J = 0

theorem isJacobiField_iff_jacobiOperator_eq_zero
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (curv : CurvatureAlongData curve) (J : Gamma) :
    IsJacobiField curv J <-> jacobiOperator curv J = 0 :=
  Iff.rfl

/-- Initial data for the Jacobi equation along a fixed curve. -/
structure JacobiInitialData where
  value : Gamma
  covDerivValue : Gamma

end Jacobi

end Riemannian
end SyntheticGeometry
