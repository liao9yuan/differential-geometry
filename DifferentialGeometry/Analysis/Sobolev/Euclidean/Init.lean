import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.External.DeGiorgi.WholeSpaceSobolev
import DifferentialGeometry.External.DeGiorgi.Poincare
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximation
import DifferentialGeometry.External.DeGiorgi.Holder.PublicEstimate
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients
import DifferentialGeometry.External.DeGiorgi.WeakFormulation
import DifferentialGeometry.External.DeGiorgi.SobolevChainRule

/-!
# Euclidean Sobolev API facade

Project-internal facade re-exporting the Euclidean Sobolev / elliptic-regularity
API consumed by the rest of the project. Downstream code should import this
file rather than reaching directly into the vendored library tree.
-/

namespace DifferentialGeometry.Sobolev.Euclidean

-- Weak-derivative predicates.
export DeGiorgi (HasWeakPartialDeriv HasWeakGrad HasWeakDiv)

-- Sobolev-membership witnesses.
export DeGiorgi (MemW1p MemW1pWitness MemW01p)

-- Whole-space Sobolev inequality.
export DeGiorgi (sobolev_smooth sobolev_of_approx C_gns)

-- Poincaré inequality on the unit ball.
export DeGiorgi (C_poinc_val poincare_unitBall_W1p_public)

-- Sobolev–Poincaré inequality on the unit ball.
export DeGiorgi (sobolev_poincare_unitBall)

-- Hölder regularity for homogeneous weak solutions.
export DeGiorgi (holder_Moser_of_homogeneousWeakSolution)

-- Elliptic coefficient framework.
export DeGiorgi (EllipticCoeff)

-- Weak-formulation API for homogeneous and non-homogeneous solutions.
export DeGiorgi (IsHomogeneousWeakSolution IsSolution)

-- Sobolev chain rule.
export DeGiorgi (sobolev_chain_rule_unitBall sobolev_chain_rule)

end DifferentialGeometry.Sobolev.Euclidean
