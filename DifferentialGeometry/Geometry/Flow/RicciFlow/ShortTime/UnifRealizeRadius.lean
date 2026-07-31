import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif

/-!
# The class-uniform realization radius inside the six-number solve

`lowreg_partial_sol_of_bounds` (`ShortTime/UnifClassBounds.lean`) exports the closed horizon
`lowregHorizon Ctop B0 B1 D ρ P` of the order-one low-regularity Ricci--DeTurck solve, with
`P` — the radius on which the metric-realization bound holds — supplied as a hypothesis.  For
a single metric that `P` came from `realize_at_thr`, whose radius is a `Classical.choose`
witness and therefore useless for a class-level floor.

Brick E5 replaces it: `unifRealizeRad Cpt Fc d = θ(d) / hs2OpC Cpt Fc d`
(`Analysis/Spectral/Tensor/Estimates/H2PointwiseUnif.lean`) is a closed number in the
fibre-Morrey input `Cpt`, the curvature-jet family `Fc` and `d = finrank ℝ E`, and its two
slots in `lowreg_partial_sol_of_bounds` are already discharged there:

* `hP` is `unifRealizeRad_pos`;
* `hreal` is `realize_at_unif`, verbatim, at
  `δ := deTurckArmContractionThreshold'' (finrank ℝ E)`.

What remains here is the consequence for the horizon: at that radius the closed horizon is
positive for every metric of the class, so the `Λ`-uniform horizon floor is reduced to the
five remaining numbers `Ctop, B0, B1, D, ρ` (bricks E6/E7) — `P` is no longer a source of
`g₀`-dependence.  Combining with `lowregHorizon_mono`, class bounds on those five numbers
turn `lowregHorizon_unif_pos` into a single positive time valid for the whole class.
-/

noncomputable section

open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- **The closed horizon at the class-uniform realization radius is positive.**

The `P`-slot of `lowreg_partial_sol_of_bounds` filled with the closed
`unifRealizeRad Cpt Fc d = θ(d) / hs2OpC Cpt Fc d`.  Everything on the right depends only on
`(Cpt, Fc, d)` and the five coefficient numbers, so two metrics of the same `Λ`-class sharing
the fibre-Morrey input `Cpt` and the curvature-jet family `Fc` get the SAME horizon; by
`lowregHorizon_mono` any class bounds `Ctop ≤ Ctop*`, `B0 ≤ B0*`, `B1 ≤ B1*`, `D ≤ D*`,
`ρ* ≤ ρ` then floor every member's existence time by this one number. -/
theorem lowregHorizon_unif_pos {Ctop B0 B1 D ρ Cpt : ℝ} {Fc : ℕ → ℝ} (d : ℕ)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hCpt : 0 ≤ Cpt) (hFc : ∀ p, 0 ≤ Fc p) :
    0 < lowregHorizon Ctop B0 B1 D ρ (unifRealizeRad Cpt Fc d) :=
  lowregHorizon_pos hCtop hB0 hB1 hD hρ (unifRealizeRad_pos hCpt hFc d)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
