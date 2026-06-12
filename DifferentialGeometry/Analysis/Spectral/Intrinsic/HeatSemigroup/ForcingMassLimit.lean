import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing

/-!
# Per-order forcing masses pass to time-`L²` limits

For a sequence of time-`L²` forcings converging in `L²([0,T]; Hᵃ)`, the per-mode
forcing masses at every spatial Sobolev order `c` converge mode by mode: the
time-mode coordinate map `f ↦ timeModeCoeff f i` is a bounded linear map of the
forcing, so each per-mode mass `forcingMass f c i = (1 + λᵢ)ᶜ ‖timeModeCoeff f i‖²`
is a continuous function of `f`.

Consequently, per-order mass summability with a uniform bound passes to the
limit: if every member of the sequence has summable order-`c` masses with total
mass at most `B`, then so does the limit, with the same bound.  Pointwise this
is the elementary Fatou-type argument over finite partial sums — each finite
partial sum of the limit's masses is the limit of the corresponding partial
sums along the sequence, hence at most `B`, and nonnegative families with
uniformly bounded partial sums are summable with total at most `B`.

This is the limit-transfer step of two-norm Picard schemes: base-order (weak
norm) convergence of the iterates plus uniform per-order mass bounds along the
sequence yield the same per-order mass bounds for the limit, which is what
upgrades the weak-norm limit to an all-order-graded (gate-realizable) forcing.
-/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ} {T : ℝ}

/-- **Per-mode forcing masses are continuous in the forcing.**  Along a sequence
of forcings converging in `L²([0,T]; Hᵃ)`, each per-mode mass at every spatial
order `c` converges to the corresponding mass of the limit: the time-mode
coordinate `f ↦ timeModeCoeff f i` is the bounded linear map
`(tensorHsCoeffL i).compLpL`, and the mass is the weight times the squared norm
of its value. -/
theorem forcingMass_tendsto_of_tendsto
    (gf : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (glim : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (htend : Tendsto gf atTop (𝓝 glim)) (c : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Tendsto (fun k => forcingMass (I := I) (M := M) (gf k) c i) atTop
      (𝓝 (forcingMass (I := I) (M := M) glim c i)) := by
  have hcl : Tendsto (fun k => timeModeCoeff (I := I) (M := M) (gf k) i) atTop
      (𝓝 (timeModeCoeff (I := I) (M := M) glim i)) :=
    (((tensorHsCoeffL (I := I) (M := M) i).compLpL 2
      (timeMeasure T)).continuous.tendsto glim).comp htend
  simpa only [forcingMass] using
    (hcl.norm.pow 2).const_mul (tensorSobolevWeight (I := I) (M := M) i c)

/-- **Per-order forcing-mass bounds pass to time-`L²` limits.**  If a sequence
of forcings converges in `L²([0,T]; Hᵃ)` and every member has summable
order-`c` masses with total at most `B`, then the limit has summable order-`c`
masses with total at most `B`: each finite partial sum of the limit's masses is
the limit of the corresponding partial sums along the sequence (per-mode
continuity), hence at most `B`; a nonnegative family with partial sums
uniformly bounded by `B` is summable with total at most `B`. -/
theorem forcingMass_summable_tsum_le_of_tendsto
    (gf : ℕ → timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (glim : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (htend : Tendsto gf atTop (𝓝 glim)) (c : ℝ) {B : ℝ}
    (hsum : ∀ k, Summable (forcingMass (I := I) (M := M) (gf k) c))
    (hbd : ∀ k, ∑' i, forcingMass (I := I) (M := M) (gf k) c i ≤ B) :
    Summable (forcingMass (I := I) (M := M) glim c) ∧
      ∑' i, forcingMass (I := I) (M := M) glim c i ≤ B := by
  have hfin : ∀ u : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ u, forcingMass (I := I) (M := M) glim c i ≤ B := by
    intro u
    have htends : Tendsto
        (fun k => ∑ i ∈ u, forcingMass (I := I) (M := M) (gf k) c i) atTop
        (𝓝 (∑ i ∈ u, forcingMass (I := I) (M := M) glim c i)) :=
      tendsto_finset_sum u (fun i _ =>
        forcingMass_tendsto_of_tendsto (I := I) (M := M) gf glim htend c i)
    refine le_of_tendsto htends (Eventually.of_forall fun k => ?_)
    exact le_trans
      (Summable.sum_le_tsum u
        (fun i _ => forcingMass_nonneg (I := I) (M := M) (gf k) c i) (hsum k))
      (hbd k)
  refine ⟨summable_of_sum_le
    (fun i => forcingMass_nonneg (I := I) (M := M) glim c i) hfin, ?_⟩
  exact Real.tsum_le_of_sum_le
    (fun i => forcingMass_nonneg (I := I) (M := M) glim c i) hfin

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
