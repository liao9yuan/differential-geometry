import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifMorreyTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvActionZero

/-!
# The class-uniform realization radius inside the six-number solve

`lowreg_partial_sol_of_bounds` (`ShortTime/UnifClassBounds.lean`) exports the closed horizon
`lowregHorizon Ctop B0 B1 D ρ P` of the order-one low-regularity Ricci--DeTurck solve, with
`P` — the radius on which the metric-realization bound holds — supplied as a hypothesis.  For
a single metric that `P` came from `realize_at_thr`, whose radius is a `Classical.choose`
witness and therefore useless for a class-level floor.

Brick E5 replaces it by the finite-action radius
`actionRealizeRad (morreyTwoC gBase Λ) (unifPtCurvZeroC d Λ Kb₀ Kb₁) d`.
The two coefficients are explicit class constants: rank-two Morrey uses only comparability
and metric jets through order two, while the order-zero curvature action uses jets through
order three and two fixed-background curvature caps.  Its two realization slots are
discharged by:

* `hP` is `actionRealizeRad_pos`;
* `hreal` is `realize_at_action`, at
  `δ := deTurckArmContractionThreshold'' (finrank ℝ E)`.

The all-order `unifRealizeRad` / `realize_at_unif` theorem retained below is compatibility
API, not the live low-regularity route.

What remains here is the consequence for the horizon: at that radius the closed horizon is
positive for every metric of the class, so the `Λ`-uniform horizon floor is reduced to the
five remaining numbers `Ctop, B0, B1, D, ρ` (bricks E6/E7) — `P` is no longer a source of
`g₀`-dependence.  Combining with `lowregHorizon_mono`, class bounds on those five numbers
turn `lowregHorizon_unif_pos` into a single positive time valid for the whole class.
-/

noncomputable section

open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Explicit finite-action realization package -/

/-- The two scalar slots supplied by the class-uniform realization producer.

The data is kept separate from its class-uniform proof: `threshold` indexes the
fibre realization statement, while `radius` is the lower radius inserted into
the six-number low-regularity horizon. -/
structure LowRegRealizeData where
  threshold : ℝ
  radius : ℝ

/-- One threshold/radius pair realizes every metric in the order-three class.

This is only the realization face of `IsLowBoundsAt`; the A2, affine, and
nonlinearity coefficients remain separate producers. -/
structure IsLowRealizeUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (R : LowRegRealizeData) : Prop where
  threshold_nonneg : 0 ≤ R.threshold
  threshold_lt : R.threshold < 1
  radius_pos : 0 < R.radius
  realize : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ R.radius →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) R.threshold

/-- The closed threshold/radius pair built from the rank-two Morrey and
curvature-action constants. -/
noncomputable def lowRealizeData
    (gBase : SmoothRiemannianMetric I M) (Λ Kb₀ Kb₁ : ℝ) : LowRegRealizeData where
  threshold := deTurckArmContractionThreshold'' (Module.finrank ℝ E)
  radius := actionRealizeRad (morreyTwoC (I := I) (M := M) gBase Λ)
    (unifPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁)
    (Module.finrank ℝ E)

/-- Supplied fixed-background curvature caps produce one explicit realization
package for every three-dimensional metric in the order-three class. -/
theorem lowRealize_unif_of
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    IsLowRealizeUnif (I := I) (M := M) gBase Λ
      (lowRealizeData (I := I) (M := M) gBase Λ Kb₀ Kb₁) := by
  have hMorreyDim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hmorrey⟩ :=
    morreyTwoC_spec (I := I) (M := M) gBase (le_trans zero_le_one hΛ) hMorreyDim
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)).le
  · exact deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)
  · exact actionRealizeRad_pos hCpt
      (unifPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁)
      (Module.finrank ℝ E)
  · intro g hEq hjet T hT
    have hjet1 := hjet 1 (by norm_num)
    have hjet2 := hjet 2 (by norm_num)
    have hjet3 := hjet 3 (by norm_num)
    have hcomp : ∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v :=
      fun x v => hEq.2 x (Set.mem_univ x) v
    have hact := unifCurvAction0_of (I := I) (M := M) gBase g hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
    have hreal := realize_at_action (I := I) (M := M) hDim g hact hCpt
      (hmorrey g hEq hjet1 hjet2)
    simpa only [lowRealizeData] using hreal T hT

/-- Every fixed background admits an explicit class-uniform realization
package; its two curvature caps are selected before the class metric varies. -/
theorem exists_lowRealize
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ R : LowRegRealizeData,
      IsLowRealizeUnif (I := I) (M := M) gBase Λ R := by
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  exact ⟨lowRealizeData (I := I) (M := M) gBase Λ Kb₀ Kb₁,
    lowRealize_unif_of (I := I) (M := M) hDim gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'⟩

/-- The closed horizon stays positive at a finite-action realization radius. -/
theorem horizon_action_pos {Ctop B0 B1 D ρ Cpt K : ℝ} (d : ℕ)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hCpt : 0 ≤ Cpt) :
    0 < lowregHorizon Ctop B0 B1 D ρ (actionRealizeRad Cpt K d) :=
  lowregHorizon_pos hCtop hB0 hB1 hD hρ (actionRealizeRad_pos hCpt K d)

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
