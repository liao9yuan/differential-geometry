import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.Pinching
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.Compactness
import DifferentialGeometry.Synthetic.Analysis.Parabolic.ScalarMaximumPrinciple
import DifferentialGeometry.Synthetic.Analysis.Parabolic.TensorMaximumPrinciple

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton's Three-Manifold Theorem: Assembly Target

This module records the final theorem interface for `RicciFlow/main.tex`. The
analytic and global inputs are supplied by the maximum-principle, blow-up, and
compactness interfaces.
-/

open SyntheticTensor

section HamiltonThreeManifold

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Data needed to state Hamilton's positive Ricci theorem in the synthetic layer. -/
structure HamiltonThreeManifoldInput where
  data : RicciFlowData k R V Time A
  dimensionThree : IsDimensionThree (R := R) (V := V)
  compactInitialManifold : Prop
  positiveRicciInitial : Prop

/-- Target geometric conclusion. A concrete manifold realization can refine this. -/
structure HamiltonThreeManifoldConclusion where
  sphericalSpaceForm : Prop

/-- Black-box bundle for the final assembly theorem while global analysis is axiomatized. -/
class HamiltonThreeManifoldBlackBoxes where
  conclusion : HamiltonThreeManifoldInput k R V Time A -> HamiltonThreeManifoldConclusion
  proves_spherical_space_form :
    forall input : HamiltonThreeManifoldInput k R V Time A,
      (conclusion input).sphericalSpaceForm

theorem hamilton_three_manifold_from_black_boxes
    [H : HamiltonThreeManifoldBlackBoxes k R V Time A]
    (input : HamiltonThreeManifoldInput k R V Time A) :
    (H.conclusion input).sphericalSpaceForm :=
  H.proves_spherical_space_form input

end HamiltonThreeManifold

