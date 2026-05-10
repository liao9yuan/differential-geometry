import RicciFlower.Realized.LeviCivita.Koszul
import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.CoordinateFrame

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Torsion-Free Calculus

Concrete consequences of mathlib's torsion tensor for RicciFlower
Levi-Civita packages.
-/

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle
open Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Pointwise torsion-free equation:
`nabla_X Y - nabla_Y X = [X,Y]`. -/
theorem torsion_free_at_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (htf : IsTorsionFreeAt (I := I) cov x)
    {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x := by
  unfold IsTorsionFreeAt at htf
  have hzero :=
    congrArg
      (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
        T (X x) (Y x))
      htf
  change cov.torsion x (X x) (Y x) = 0 at hzero
  rw [cov.torsion_apply hX hY] at hzero
  exact sub_eq_zero.mp hzero

/-- Global torsion-free equation at a point. -/
theorem torsion_free_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x :=
  torsion_free_at_apply (I := I) (htf x) hX hY

/-- Family torsion-free equation at a flow time. -/
theorem torsion_free_family_apply
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (htf : IsTorsionFreeFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    G.connectionAt t Y x (X x) - G.connectionAt t X x (Y x) =
      VectorField.mlieBracket I X Y x :=
  torsion_free_apply (I := I) (htf t) hX hY

/-! ## Coordinate proof for the Koszul connection -/

/-- The Koszul scalar is symmetric in coordinate-frame directions at the
coordinate base point. -/
theorem koszulScalar_coordinateFrame_symm
    (g : SmoothRiemannianMetric I M)
    (x0 : M) (i j : CoordinateIdx E)
    (Z : (p : M) -> TangentSpace I p) :
    (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 i)
          (coordinateFrameAt (I := I) x0 j) Z x0 =
      (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 j)
          (coordinateFrameAt (I := I) x0 i) Z x0 :=
  sub_eq_zero.mp (by
    simpa [coordinateFrameAt_bracket_zero (I := I) x0 i j] using
      koszulScalar_swap_sub (I := I) g (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j) Z x0)

/-- In the coordinate frame, the torsion coefficients are exactly the skew
Christoffel coefficients, because coordinate frame brackets vanish at the
base point. -/
theorem coordinate_torsion_coeff_eq_christoffel_skew
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (i j k : CoordinateIdx E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
        (cov.torsion x0
          (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0)) =
      christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k -
        christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k := by
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have h := Coordinates.torsion_coeff_eq_christoffel_skew
    (I := I) cov (coordinateFrameAt (I := I) x0) hframe i j k
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
  rw [coordinateFrameAt_bracket_zero (I := I) x0 i j] at h
  simpa [hframe] using h

/-- The Koszul connection is symmetric on coordinate-frame basis vectors. -/
theorem leviCivitaConnectionOfMetric_coordinateFrame_apply_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx E) :
    (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 j) x0)
        (coordinateFrameAt (I := I) x0 i x0) =
        (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 i) x0)
        (coordinateFrameAt (I := I) x0 j x0) := by
  apply metricFlatLinear_injective (I := I) g x0
  ext v
  have hleft := leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (I := I) g (coordinateFrameAt (I := I) x0 i)
    (coordinateFrameAt (I := I) x0 j) x0
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j) v
  have hright := leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (I := I) g (coordinateFrameAt (I := I) x0 j)
    (coordinateFrameAt (I := I) x0 i) x0
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 j)
    (coordinateFrameAt_mdifferentiableAt (I := I) x0 i) v
  have hK := koszulScalar_coordinateFrame_symm (I := I) g x0 i j
    (tangentConstAt (I := I) x0 v)
  simpa [metricFlatLinear_apply] using hleft.trans (hK.trans hright.symm)

/-- Coordinate-frame Christoffel symbols of the Koszul connection are symmetric
in the lower two coordinate indices. -/
theorem leviCivitaConnectionOfMetric_coordinate_christoffel_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j k : CoordinateIdx E) :
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k := by
  unfold christoffelSymbolInFrame
  rw [leviCivitaConnectionOfMetric_coordinateFrame_apply_symm (I := I) g x0 i j]

/-- The Koszul connection has zero torsion on coordinate-frame basis vectors. -/
theorem leviCivitaConnectionOfMetric_coordinate_torsion_basis_zero
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx E) :
    (leviCivitaConnectionOfMetric (I := I) g).torsion x0
        (coordinateFrameAt (I := I) x0 i x0)
        (coordinateFrameAt (I := I) x0 j x0) = 0 := by
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  let hx : x0 ∈ coordinateFrameSet (I := I) x0 :=
    coordinateFrameAt_mem (I := I) x0
  apply (hframe.toBasisAt hx).repr.injective
  ext k
  have hcoeff :
      hframe.coeff k x0
          ((leviCivitaConnectionOfMetric (I := I) g).torsion x0
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) = 0 := by
    rw [coordinate_torsion_coeff_eq_christoffel_skew
      (I := I) (leviCivitaConnectionOfMetric (I := I) g) x0 i j k]
    rw [leviCivitaConnectionOfMetric_coordinate_christoffel_symm (I := I) g x0 i j k]
    ring
  simpa [hframe, hx, IsLocalFrameOn.coeff] using hcoeff

/-- The Koszul-constructed connection is torsion-free. -/
theorem leviCivitaConnectionOfMetric_isTorsionFree
    (g : SmoothRiemannianMetric I M) :
    IsTorsionFree (I := I) (leviCivitaConnectionOfMetric (I := I) g) := by
  intro x
  change (leviCivitaConnectionOfMetric (I := I) g).torsion x = 0
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let B := coordinateFrameAt_toBasis (I := I) x
  have hu : u = ∑ i : CoordinateIdx E, B.repr u i • B i :=
    (B.sum_repr u).symm
  have hv : v = ∑ j : CoordinateIdx E, B.repr v j • B j :=
    (B.sum_repr v).symm
  rw [hu, hv]
  simp [B, coordinateFrameAt_toBasis_apply,
    leviCivitaConnectionOfMetric_coordinate_torsion_basis_zero]

/-- The Koszul-constructed connection satisfies the RicciFlower Levi-Civita
predicate. -/
theorem leviCivitaConnectionOfMetric_isLeviCivita
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g :=
  isLeviCivita_of_parts (I := I)
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g)

end LeviCivita
end Realized
end RicciFlower
