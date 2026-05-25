import RicciFlower.HCGCompactness.RicciFlowConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Compactness Theorem Interface

This is the RicciFlower-native theorem shape corresponding to MSM135 Chapter 3,
Theorem "Compactness for solutions".  The proof is intentionally left at the
single global metric compactness frontier.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Hamilton--Cheeger--Gromov compactness for pointed Ricci flows.

A sequence of complete pointed Ricci-flow solutions on a common real time
interval, with uniform curvature bounds on compact time windows and
basepoint injectivity/noncollapse input, admits a smoothly convergent pointed
subsequence.  The missing proof is the Riemannian Cheeger--Gromov compactness,
direct-limit/exhaustion construction, and Arzela--Ascoli upgrade to smooth
spacetime convergence. -/
theorem hamiltonCompactness
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (_hcomplete : CompleteInput (I := I) X)
    (_hcurv : CurvBoundInput (I := I) X)
    (_hinj : InjInput (I := I) X)
    (_hnoncollapse : NoncollapseInput (I := I) X) :
    CompactnessConclusion (I := I) X := by
  -- Real frontier: MSM135 Ch4 metric compactness, direct limits, and
  -- compact-open smooth Arzela--Ascoli for the pulled-back Ricci flows.
  sorry

end HCGCompactness
end RicciFlower
