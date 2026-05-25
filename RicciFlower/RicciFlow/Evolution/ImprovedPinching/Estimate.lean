import RicciFlower.RicciFlow.Evolution.ImprovedPinching.Wrappers
import RicciFlower.RicciFlow.Evolution.RicciPreservation

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Improved pinching estimate

This file contains the native Section 10 estimate layer following Hamilton's
Lemma 10.6.  The theorem here is domain-aware on the Ricci-flow time carrier;
the all-real display functions are only carrier extensions used by high-level
Hamilton endpoint wrappers.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Section 10 display weight `R^{-epsilon}`. -/
def pinchWeight (scalar : Real -> M -> Real) (epsilon : Real) :
    Real -> M -> Real :=
  fun t x => scalar t x ^ (-epsilon)

/-- Domain-aware form of Hamilton's improved pinching estimate. -/
def PinchEstimateOn
    (tracefreeRicciNormSq scalar weight : Real -> M -> Real)
    (C : Real) (U : Set Real) : Prop :=
  ∀ t : Real, t ∈ U -> ∀ x : M,
    tracefreeRicciNormSq t x / scalar t x ^ 2 ≤ C * weight t x

/-- Extend a scalar field by zero away from the flow carrier. -/
def carrierZeroExt
    (D : Realized.RealTimeInterval) (f : Real -> M -> Real) :
    Real -> M -> Real := by
  classical
  exact fun t x => if t ∈ D.carrier then f t x else 0

/-- Extend scalar curvature by one away from the flow carrier, so display
denominators outside the solution domain are harmless. -/
def carrierScalarExt
    (D : Realized.RealTimeInterval) (scalar : Real -> M -> Real) :
    Real -> M -> Real := by
  classical
  exact fun t x => if t ∈ D.carrier then scalar t x else 1

/-- Extend the Hamilton decay weight by zero away from the flow carrier. -/
def carrierWeightExt
    (D : Realized.RealTimeInterval) (scalar : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real := by
  classical
  exact fun t x =>
    if t ∈ D.carrier then pinchWeight (M := M) scalar epsilon t x else 0

/-- Carrier-extension turns a domain-aware estimate into an all-real display
estimate. -/
theorem pinchEstimate_ext
    {D : Realized.RealTimeInterval}
    {tracefreeRicciNormSq scalar : Real -> M -> Real}
    {epsilon C : Real}
    (h : PinchEstimateOn (M := M) tracefreeRicciNormSq scalar
      (pinchWeight (M := M) scalar epsilon) C D.carrier) :
    PinchEstimateOn (M := M)
      (carrierZeroExt (M := M) D tracefreeRicciNormSq)
      (carrierScalarExt (M := M) D scalar)
      (carrierWeightExt (M := M) D scalar epsilon) C Set.univ := by
  intro t _ht x
  by_cases htD : t ∈ D.carrier
  · simpa [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD] using
      h t htD x
  · simp [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD]

/-- Native Section 10 improved pinching estimate for a smooth three-dimensional
Ricci flow.

The proof frontier is the post-Lemma-10.6 scalar maximum-principle step:
one must convert Section 9 Ricci nonnegativity and shifted pinching into the
pointwise ordered-eigenvalue `PinchEigen3` context, use `pinchEvol_book` to
obtain the drifted scalar subsolution inequality, and apply the scalar WMP on
compact subintervals. -/
theorem pinchEstimate_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega : Real} (h0ω : 0 < omega)
    (hD : D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hpinch :
      ∃ delta : Real,
        0 < delta ∧ delta < (1 : Real) / 3 ∧
          ∀ T : Real, 0 ≤ T -> T < omega ->
            PinchPres (I := I) (M := M)
              (fun t : Real => S.base.metric t)
              (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
              S.scalar T delta)
    (hric :
      ∀ T : Real, 0 ≤ T -> T < omega ->
        Realized.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
          (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          (Set.Icc 0 T)) :
    ∃ epsilon C : Real,
      0 < epsilon ∧ epsilon < 1 ∧ 0 ≤ C ∧
        PinchEstimateOn (M := M)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          S.scalar (pinchWeight (M := M) S.scalar epsilon) C D.carrier := by
  classical
  -- The missing proof is the scalar-WMP application after the checked 10.6
  -- evolution identity and the checked 10.7/10.8 reaction algebra.
  sorry

/-- All-real display form of `pinchEstimate_sol`, obtained by extending the
canonical Section 10 fields away from the flow carrier. -/
theorem pinchEstimate_display_sol
    {D : Realized.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) I]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {omega : Real} (h0ω : 0 < omega)
    (hD : D = Realized.RealTimeInterval.closedOpen 0 omega h0ω)
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hscalar : ∀ t : Real, t ∈ D.carrier -> ∀ x : M, 0 < S.scalar t x)
    (hpinch :
      ∃ delta : Real,
        0 < delta ∧ delta < (1 : Real) / 3 ∧
          ∀ T : Real, 0 ≤ T -> T < omega ->
            PinchPres (I := I) (M := M)
              (fun t : Real => S.base.metric t)
              (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
              S.scalar T delta)
    (hric :
      ∀ T : Real, 0 ≤ T -> T < omega ->
        Realized.TwoTensorFamilyNonnegativeOn (I := I) (M := M)
          (Realized.twoTensorSecToFamily (I := I) (M := M) S.ricci)
          (Set.Icc 0 T)) :
    ∃ tracefreeRicciNormSq scalar weight : Real -> M -> Real, ∃ C : Real,
      PinchEstimateOn (M := M) tracefreeRicciNormSq scalar weight C Set.univ := by
  classical
  rcases pinchEstimate_sol (I := I) (M := M) S hS h0ω hD hdim hscalar
      hpinch hric with
    ⟨epsilon, C, _heps0, _heps1, _hC, hest⟩
  refine ⟨
    carrierZeroExt (M := M) D (tfRicNormSq S.scalar (ricciNorm (I := I) S)),
    carrierScalarExt (M := M) D S.scalar,
    carrierWeightExt (M := M) D S.scalar epsilon,
    C, ?_⟩
  intro t _ht x
  by_cases htD : t ∈ D.carrier
  · simpa [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD] using
      hest t htD x
  · simp [carrierZeroExt, carrierScalarExt, carrierWeightExt, htD]

end RicciFlow
end RicciFlower
