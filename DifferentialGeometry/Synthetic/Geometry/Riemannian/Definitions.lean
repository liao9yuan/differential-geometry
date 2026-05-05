import DifferentialGeometry.Synthetic.Geometry.Riemannian.Jacobi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Concrete Riemannian Definitions

This file is deliberately definitions-first.  It records notions from Chow
lecture 7 that can be stated now without introducing theorem-provider APIs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ContDiff Manifold Topology

namespace SyntheticGeometry
namespace Riemannian

section SyntheticCurveDefinitions

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {M : RiemannianManifoldData k R V}

/-- A curve has constant speed when the derivative of `g(gamma', gamma')` vanishes. -/
def HasConstantSpeed (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  curve.scalarDeriv (speedSquared curve) = 0

/-- A unit-speed curve satisfies `g(gamma', gamma') = 1`. -/
def IsUnitSpeed (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  speedSquared curve = 1

/--
A pregeodesic has acceleration everywhere tangent to its own velocity:
`D_t gamma' = lambda gamma'`.
-/
def IsPregeodesic (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  exists lambda : A, curve.covDeriv curve.velocity = lambda • curve.velocity

/-- A vector field along a curve is normal to the velocity field. -/
def IsNormalAlong
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (X : Gamma) : Prop :=
  curve.metric X curve.velocity = 0

/-- A vector field along a curve is tangential if it is a scalar multiple of velocity. -/
def IsTangentialAlong
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) (X : Gamma) : Prop :=
  exists f : A, X = f • curve.velocity

/-- Nondegeneracy of the pulled-back metric on fields along this curve. -/
def AlongMetricNondegenerate
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  forall X : Gamma, (forall Y : Gamma, curve.metric X Y = 0) -> X = 0

/--
The Euler-Lagrange stationarity condition obtained from the first variation
formula after the fundamental lemma: the acceleration pairs to zero with every
field along the curve.
-/
def FirstVariationStationary
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  forall W : Gamma, curve.metric (curve.covDeriv curve.velocity) W = 0

theorem hasConstantSpeed_of_affineGeodesic
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (hgeo : IsAffineGeodesic curve) :
    HasConstantSpeed curve :=
  scalarDeriv_speedSquared_eq_zero_of_geodesic hgeo

theorem isPregeodesic_of_affineGeodesic
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (hgeo : IsAffineGeodesic curve) :
    IsPregeodesic curve := by
  refine ⟨0, ?_⟩
  unfold IsAffineGeodesic IsParallelAlong at hgeo
  rw [hgeo]
  simp

theorem isAffineGeodesic_of_firstVariationStationary
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (hnondeg : AlongMetricNondegenerate curve)
    (hstationary : FirstVariationStationary curve) :
    IsAffineGeodesic curve := by
  unfold IsAffineGeodesic IsParallelAlong
  exact hnondeg (curve.covDeriv curve.velocity) hstationary

/-- A Jacobi field with specified initial value and initial covariant derivative. -/
def HasJacobiInitialData
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (curv : CurvatureAlongData curve) (J : Gamma)
    (initial : JacobiInitialData (Gamma := Gamma)) : Prop :=
  IsJacobiField curv J /\
    J = initial.value /\
      curve.covDeriv J = initial.covDerivValue

end SyntheticCurveDefinitions

section MathlibPathDefinitions

open Manifold Set

variable
  {E H X : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [forall x : X, ENormSMulClass Real (TangentSpace I x)]

/-- Smoothness on a closed real interval, matching the hypotheses of `pathELength`. -/
def SmoothOnIcc (I : ModelWithCorners Real E H) (gamma : Real -> X) (a b : Real) : Prop :=
  ContMDiffOn 𝓘(ℝ) I 1 gamma (Icc a b)

/-- The Riemannian extended length of a real-parametrized path on `[a,b]`. -/
noncomputable def PathLength (I : ModelWithCorners Real E H)
    (gamma : Real -> X) (a b : Real) : ENNReal :=
  Manifold.pathELength I gamma a b

/-- The Riemannian extended distance defined as the infimum of smooth path lengths. -/
noncomputable def RiemannianEDist (I : ModelWithCorners Real E H)
    (x y : X) : ENNReal :=
  Manifold.riemannianEDist I x y

/-- A path realizes the Riemannian distance between its endpoints. -/
def RealizesRiemannianEDist (I : ModelWithCorners Real E H)
    (gamma : Real -> X) (a b : Real) : Prop :=
  PathLength I gamma a b = RiemannianEDist I (gamma a) (gamma b)

/-- A smooth segment is length-minimizing among smooth competitors with the same endpoints. -/
def IsLengthMinimizingOnIcc (I : ModelWithCorners Real E H)
    (gamma : Real -> X) (a b : Real) : Prop :=
  SmoothOnIcc I gamma a b /\
    forall eta : Real -> X,
      SmoothOnIcc I eta a b ->
        eta a = gamma a ->
          eta b = gamma b ->
            PathLength I gamma a b <= PathLength I eta a b

theorem length_le_competitor_of_realizes_riemannianEDist
    {gamma eta : Real -> X} {a b : Real}
    (hab : a <= b)
    (hrealizes : RealizesRiemannianEDist I gamma a b)
    (heta : SmoothOnIcc I eta a b)
    (ha : eta a = gamma a)
    (hb : eta b = gamma b) :
    PathLength I gamma a b <= PathLength I eta a b := by
  rw [hrealizes]
  unfold RiemannianEDist PathLength
  exact Manifold.riemannianEDist_le_pathELength
    (I := I) (γ := eta) heta ha hb hab

theorem isLengthMinimizingOnIcc_of_realizes_riemannianEDist
    {gamma : Real -> X} {a b : Real}
    (hab : a <= b)
    (hgamma : SmoothOnIcc I gamma a b)
    (hrealizes : RealizesRiemannianEDist I gamma a b) :
    IsLengthMinimizingOnIcc I gamma a b := by
  refine ⟨hgamma, ?_⟩
  intro eta heta ha hb
  exact length_le_competitor_of_realizes_riemannianEDist
    (I := I) hab hrealizes heta ha hb

/--
Fermat's theorem for a one-parameter length functional: if the length has a
local minimum at the base variation and is differentiable there, the first
variation is zero.
-/
theorem firstVariation_eq_zero_of_localMin
    {lengthAt : Real -> Real} {firstVariation : Real}
    (hmin : IsLocalMin lengthAt 0)
    (hderiv : HasDerivAt lengthAt firstVariation 0) :
    firstVariation = 0 :=
  hmin.hasDerivAt_eq_zero hderiv

end MathlibPathDefinitions

section DistanceRealizingToGeodesic

open Manifold Set

variable {k R V A Gamma : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [Invertible (2 : R)]
variable [CommRing A]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [AddCommGroup Gamma] [Module A Gamma]
variable {M : RiemannianManifoldData k R V}

variable
  {E H X : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [forall x : X, ENormSMulClass Real (TangentSpace I x)]

/--
The precise remaining geometric gap in the statement
"distance-realizing smooth paths are geodesics":
length-minimality must imply the first-variation stationarity condition for
the concrete along-curve model.
-/
def LengthMinimizingGivesFirstVariationStationarity
    (I : ModelWithCorners Real E H) (path : Real -> X) (a b : Real)
    (curve : AlongCurveData (A := A) (Gamma := Gamma) M) : Prop :=
  IsLengthMinimizingOnIcc I path a b -> FirstVariationStationary curve

theorem isAffineGeodesic_of_realizes_riemannianEDist
    {path : Real -> X} {a b : Real}
    {curve : AlongCurveData (A := A) (Gamma := Gamma) M}
    (hab : a <= b)
    (hpath : SmoothOnIcc I path a b)
    (hrealizes : RealizesRiemannianEDist I path a b)
    (hnondeg : AlongMetricNondegenerate curve)
    (hfirstVariation :
      LengthMinimizingGivesFirstVariationStationarity I path a b curve) :
    IsAffineGeodesic curve := by
  have hmin : IsLengthMinimizingOnIcc I path a b :=
    isLengthMinimizingOnIcc_of_realizes_riemannianEDist
      (I := I) hab hpath hrealizes
  exact isAffineGeodesic_of_firstVariationStationary hnondeg
    (hfirstVariation hmin)

end DistanceRealizingToGeodesic

end Riemannian
end SyntheticGeometry
