/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar Curvature Evolution

This file records the scalar-curvature simplification in MSM110 Chapter 6,
Section 1.  The full geometric inputs are kept explicit: one hypothesis is the
pre-Bianchi Ricci-flow scalar evolution, and the second is the contracted
Bianchi reduction that turns it into the heat-type scalar equation.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- MSM110 Chapter 6, Section 1, equation
`eq:scalar_curvature_ricci_flow_one`.

This is the scalar-curvature evolution immediately after substituting
`∂t g = -2 Ric`, before applying the contracted Bianchi identity:
`∂t R = 2 ΔR - 2 Q + 2 |Ric|²`, where `Q` denotes the contracted second
derivative term `g^{jk} g^{pq} ∇_q ∇_j R_{kp}`. -/
def ScalarPreBianchiEvolutionEquationOn
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x +
        2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

/-- The contracted-Bianchi simplification used in MSM110 Chapter 6, Section 1:
`2 ΔR - 2 Q = ΔR`. -/
def ScalarContractedBianchiReductionOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x =
      scalarLap (t : Real) x

/-- Contracted second-Bianchi identity in the scalar-curvature calculation:
the twice-contracted Ricci Hessian term is half the scalar Laplacian. -/
def ScalarSecondDerivativeContractedBianchiOn
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : Realized.RealTimeInterval.RegularTime D) (x : M),
    contractedRicciHessian (t : Real) x =
      (1 / 2 : Real) * scalarLap (t : Real) x

/-- The scalar contracted-Bianchi identity supplies the algebraic reduction
`2 ΔR - 2 Q = ΔR` used in MSM110 Chapter 6.1. -/
theorem scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    {D : Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian := by
  intro t x
  rw [hbianchi t x]
  ring

/-- MSM110 Chapter 6, Section 1, equation `eq:scalar_curv_evolu`.

The scalar curvature heat equation follows from the pre-Bianchi scalar
evolution and the contracted-Bianchi reduction. -/
theorem scalarEvolutionEquationOn_of_contractedBianchi
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq := by
  intro t x
  exact (hpre t x).congr_deriv (by
    rw [hbianchi t x])

/-- Book-facing name for MSM110 Chapter 6, Section 1,
`eq:scalar_curv_evolu`. -/
theorem msm110_ch6_1_scalar_curvature_evolution
    {D : Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  scalarEvolutionEquationOn_of_contractedBianchi
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi

end RicciFlow
end RicciFlower
