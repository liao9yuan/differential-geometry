import RicciFlower.Realized.LeviCivita.Koszul
import RicciFlower.Realized.LeviCivita.MetricCompatibility
import RicciFlower.Realized.LeviCivita.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Levi-Civita Uniqueness on Smooth Inputs

The bundled `CovariantDerivative` type is total on raw sections, including
non-smooth sections.  The geometric uniqueness theorem therefore identifies
Levi-Civita connections on differentiable vector-field inputs and tangent
directions, not as literal total functions on all raw section inputs.
-/

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Smooth-input uniqueness of the Levi-Civita connection for a fixed metric.

This is the geometrically meaningful uniqueness statement for mathlib's
`CovariantDerivative`: two smooth Levi-Civita connections agree on every
differentiable vector-field input and every tangent direction. -/
def LeviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _),
    CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ->
      CovariantDerivative.ContMDiffCovariantDerivative cov' ∞ ->
        IsLeviCivita (I := I) cov g ->
          IsLeviCivita (I := I) cov' g ->
            forall {x : M} (Y : (p : M) -> TangentSpace I p),
              MDiffAt (T% Y) x ->
                forall v : TangentSpace I x,
                  cov Y x v = cov' Y x v

/-- Koszul identity for any connection satisfying the Levi-Civita predicates. -/
theorem leviCivita_inner_eq_half_koszul
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hlc : IsLeviCivita (I := I) cov g)
    {X Y Z : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (cov Y x (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  have hmc := metricCompatible_of_isLeviCivita (I := I) hlc
  have htf := torsionFree_of_isLeviCivita (I := I) hlc
  have hXYZ := metric_compatible_apply (I := I) hmc X Y Z hX hY hZ
  have hYZX := metric_compatible_apply (I := I) hmc Y Z X hY hZ hX
  have hZXY := metric_compatible_apply (I := I) hmc Z X Y hZ hX hY
  have htYZ := torsion_free_apply (I := I) htf (X := Y) (Y := Z) hY hZ
  have htZX := torsion_free_apply (I := I) htf (X := Z) (Y := X) hZ hX
  have htXY := torsion_free_apply (I := I) htf (X := X) (Y := Y) hX hY
  change directionalDeriv (I := I) X
      (fun y : M => g.inner y (Y y) (Z y)) x =
    g.inner x (cov Y x (X x)) (Z x) +
      g.inner x (Y x) (cov Z x (X x)) at hXYZ
  change directionalDeriv (I := I) Y
      (fun y : M => g.inner y (Z y) (X y)) x =
    g.inner x (cov Z x (Y x)) (X x) +
      g.inner x (Z x) (cov X x (Y x)) at hYZX
  change directionalDeriv (I := I) Z
      (fun y : M => g.inner y (X y) (Y y)) x =
    g.inner x (cov X x (Z x)) (Y x) +
      g.inner x (X x) (cov Y x (Z x)) at hZXY
  unfold koszulScalar
  rw [hXYZ, hYZX, hZXY, ← htYZ, ← htZX, ← htXY]
  simp only [map_sub]
  rw [g.symm x (cov Z x (Y x)) (X x)]
  rw [g.symm x (Z x) (cov X x (Y x))]
  rw [g.symm x (cov X x (Z x)) (Y x)]
  rw [g.symm x (X x) (cov Y x (Z x))]
  rw [g.symm x (Y x) (cov Z x (X x))]
  rw [← g.symm x (cov Y x (X x)) (Z x)]
  ring

/-- Two smooth Levi-Civita connections agree on differentiable vector-field
inputs.  The smoothness hypotheses are part of the geometric uniqueness API;
the proof only uses the Levi-Civita calculus identities at the point. -/
theorem leviCivita_apply_eq_of_smooth
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (_hcovSmooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (_hcov'Smooth : CovariantDerivative.ContMDiffCovariantDerivative cov' ∞)
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  simp only [metricFlatLinear_apply]
  let Z : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x v
  have hZ : MDiffAt (T% Z) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x v
  have hleft := leviCivita_inner_eq_half_koszul
    (I := I) (cov := cov) (g := g) hcov
    (X := X) (Y := Y) (Z := Z) hX hY hZ
  have hright := leviCivita_inner_eq_half_koszul
    (I := I) (cov := cov') (g := g) hcov'
    (X := X) (Y := Y) (Z := Z) hX hY hZ
  have hZx : Z x = v := by
    change tangentConstAt (I := I) x v x = v
    rw [tangentConstAt_self]
  rw [hZx] at hleft hright
  exact hleft.trans hright.symm

/-- Descended tangent-direction form of smooth Levi-Civita uniqueness. -/
theorem leviCivita_apply_eq_of_smooth_direction
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hcovSmooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (hcov'Smooth : CovariantDerivative.ContMDiffCovariantDerivative cov' ∞)
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {x : M} (Y : (p : M) -> TangentSpace I p)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    cov Y x v = cov' Y x v := by
  let X : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x v
  have hX : MDiffAt (T% X) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x v
  have h := leviCivita_apply_eq_of_smooth
    (I := I) (cov := cov) (cov' := cov') (g := g)
    hcovSmooth hcov'Smooth hcov hcov' (X := X) (Y := Y) hX hY
  have hXx : X x = v := by
    change tangentConstAt (I := I) x v x = v
    rw [tangentConstAt_self]
  rw [hXx] at h
  exact h

/-- The smooth-input uniqueness package is realized by the Koszul formula. -/
theorem leviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) :
    LeviCivitaConnectionUniqueOnSmooth (I := I) g := by
  intro cov cov' hcovSmooth hcov'Smooth hcov hcov' x Y hY v
  exact leviCivita_apply_eq_of_smooth_direction
    (I := I) (cov := cov) (cov' := cov') (g := g)
    hcovSmooth hcov'Smooth hcov hcov' (x := x) Y hY v

end LeviCivita
end Realized
end RicciFlower
