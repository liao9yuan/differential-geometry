import DifferentialGeometry.Synthetic.Geometry.Riemannian.Along

/-!
# Synthetic Geodesics

This file gives the first geodesic definitions on top of
`AlongCurveData`.  It follows the lecture-level order: parallel fields along a
curve, affine geodesics, constant speed, and the coordinate geodesic equation
as an interface theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SyntheticGeometry
namespace Riemannian

section Geodesic

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {M : RiemannianManifoldData k R V}

/-- A field along a curve is parallel when its covariant derivative vanishes. -/
def IsParallelAlong (curve : AlongCurveData (A := A) (Gamma := Gamma) M)
    (X : Gamma) : Prop :=
  curve.covDeriv X = 0

/-- An affinely parametrized geodesic is a curve whose velocity is parallel. -/
def IsAffineGeodesic (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  IsParallelAlong curve curve.velocity

/-- Squared speed of a curve, expressed in the scalar algebra along the curve. -/
def speedSquared (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : A :=
  curve.metric curve.velocity curve.velocity

theorem scalarDeriv_metric_eq_zero_of_parallel
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    {X Y : Gamma}
    (hX : IsParallelAlong curve X) (hY : IsParallelAlong curve Y) :
    curve.scalarDeriv (curve.metric X Y) = 0 := by
  unfold IsParallelAlong at hX hY
  rw [curve.metric_compat, hX, hY,
    curve.metric_zero_left Y, curve.metric_zero_right X, zero_add]

theorem scalarDeriv_speedSquared_eq_zero_of_geodesic
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (h : IsAffineGeodesic curve) :
    curve.scalarDeriv (speedSquared curve) = 0 := by
  simpa [speedSquared, IsAffineGeodesic] using
    scalarDeriv_metric_eq_zero_of_parallel (curve := curve) h h

/--
Coordinate data for a curve.  The field
`component_covDeriv_velocity` records the usual coordinate formula

`(D_t gamma')^a = acceleration^a + Gamma^a_{ij} velocity^i velocity^j`.
-/
structure CoordinateCurveData
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (n : Nat) where
  component : Gamma →ₗ[A] (Fin n -> A)
  velocityCoord : Fin n -> A
  accelerationCoord : Fin n -> A
  christoffelAlong : Fin n -> Fin n -> Fin n -> A
  component_velocity :
    component curve.velocity = velocityCoord
  component_covDeriv_velocity :
    forall a : Fin n,
      component (curve.covDeriv curve.velocity) a =
        accelerationCoord a +
          Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : Fin n =>
              christoffelAlong a i j * velocityCoord i * velocityCoord j))

def CoordinateCurveData.christoffelQuadratic
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M} {n : Nat}
    (coord : CoordinateCurveData curve n) (a : Fin n) : A :=
  Finset.univ.sum (fun i : Fin n =>
    Finset.univ.sum (fun j : Fin n =>
      coord.christoffelAlong a i j * coord.velocityCoord i * coord.velocityCoord j))

theorem coordinate_geodesic_equation
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M} {n : Nat}
    (coord : CoordinateCurveData curve n)
    (hgeo : IsAffineGeodesic curve) (a : Fin n) :
    coord.accelerationCoord a + coord.christoffelQuadratic a = 0 := by
  unfold IsAffineGeodesic IsParallelAlong at hgeo
  have hcomp := coord.component_covDeriv_velocity a
  rw [hgeo] at hcomp
  simpa [CoordinateCurveData.christoffelQuadratic] using hcomp.symm

/-- Initial data for a geodesic initial-value problem. -/
structure GeodesicInitialData (Point Tangent : Type*) where
  point : Point
  velocity : Tangent

/--
A solved geodesic initial-value problem.  The realization predicates keep this
interface independent of a later concrete point/curve model.
-/
structure GeodesicSolutionData
    (Point Tangent : Type*)
    (initial : GeodesicInitialData Point Tangent) where
  curve : AlongCurveData (A := A) (Gamma := Gamma) M
  realizesPoint : Prop
  realizesVelocity : Prop
  geodesic : IsAffineGeodesic curve

end Geodesic

end Riemannian
end SyntheticGeometry
