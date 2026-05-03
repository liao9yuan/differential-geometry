import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.BlowUp

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Compactness and Noncollapsing Interfaces

This file names the global black boxes used in the blow-up-limit part of
Hamilton's theorem.
-/

open SyntheticTensor

section CompactnessInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A sequence of pointed Ricci flows, abstracting the parabolic rescaling setup. -/
structure PointedRicciFlowSequence (Index : Type*) where
  flow : Index -> RicciFlowData k R V Time A

/-- Candidate compactness limit. -/
structure RicciFlowLimitCandidate where
  flow : RicciFlowData k R V Time A
  isLimit : Prop

/-- Hamilton-Cheeger-Gromov compactness as a black-box extraction interface. -/
class HamiltonCompactnessTheorem (Index : Type*) where
  extract_limit :
    PointedRicciFlowSequence k R V Time A Index ->
      Nonempty (RicciFlowLimitCandidate k R V Time A)

/-- Perelman's noncollapsing theorem as an interface. -/
class PerelmanNoncollapsing where
  IsKappaNoncollapsed : RicciFlowData k R V Time A -> Prop
  noncollapsed : forall D : RicciFlowData k R V Time A, IsKappaNoncollapsed D

/-- Myers-type compactness conclusion needed for the final contradiction. -/
class MyersTheoremInterface (Input Output : Type*) where
  conclusion : Input -> Output -> Prop
  exists_output : forall input, Nonempty { output : Output // conclusion input output }

end CompactnessInterfaces

