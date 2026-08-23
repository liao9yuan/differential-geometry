import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi

set_option autoImplicit false

/-!
# L-conjugate points

This file defines L-conjugacy through singularity of the initial-tangent
differential of Perelman's L-exponential map.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- A positive backward time is L-conjugate along an initial tangent when the
initial-tangent differential of the L-exponential map is not injective. -/
def IsLConj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Prop :=
  (Z, tau) ∈ lExpPosDom S T x ∧
    ¬ Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- L-conjugacy is equivalent to a nonzero vector in the kernel of the
initial-tangent differential of the L-exponential map. -/
theorem isLConj_iff
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          mfderiv 𝓘(Real, E) I
            (fun W : E => lExp S T x W tau) Z V = 0 := by
  unfold IsLConj
  set f := mfderiv 𝓘(Real, E) I
    (fun W : E => lExp S T x W tau) Z
  refine and_congr_right fun _ => ?_
  have hker : Function.Injective (fun V : E => f V) ↔
      ∀ V : E, f V = 0 → V = 0 := by
    constructor
    · intro hinj V hV
      exact hinj (hV.trans (map_zero f).symm)
    · intro hzero V W hVW
      apply sub_eq_zero.mp
      apply hzero
      change f V = f W at hVW
      calc
        f (V - W) = f V - f W := map_sub f V W
        _ = 0 := sub_eq_zero.mpr hVW
  rw [hker]
  push Not
  constructor
  · rintro ⟨V, hVzero, hVne⟩
    exact ⟨V, hVne, hVzero⟩
  · rintro ⟨V, hVne, hVzero⟩
    exact ⟨V, hVzero, hVne⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- L-conjugacy is equivalent to a nonzero initial-tangent Jacobi field that
vanishes at the specified square-root time. -/
theorem isLConj_iff_jac
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    IsLConj S T x Z tau ↔
      (Z, tau) ∈ lExpPosDom S T x ∧
        ∃ V : E, V ≠ 0 ∧
          lRegJacobiField S T x Z V (Real.sqrt tau) = 0 := by
  rw [isLConj_iff]
  refine and_congr_right fun _ => ?_
  refine exists_congr fun V => and_congr_right fun _ => ?_
  rw [← lExpJacobi_eq]
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- At a positive-domain point that is not L-conjugate, the initial-tangent
differential of the L-exponential map is injective. -/
theorem lExpDeriv_inj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Injective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  by_contra hinj
  exact hconj ⟨hdom, hinj⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- In finite dimension, the nonconjugate initial-tangent differential of the
L-exponential map is surjective. -/
theorem lExpDeriv_surj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConj S T x Z tau) :
    Function.Surjective fun V : E =>
      mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V := by
  exact LinearMap.surjective_of_injective
    (lExpDeriv_inj S T x Z tau hdom hconj)

end DifferentialGeometry.PDE.RicciFlow.Perelman
