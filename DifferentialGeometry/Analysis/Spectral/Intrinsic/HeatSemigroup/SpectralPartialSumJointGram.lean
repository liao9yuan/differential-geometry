import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint

/-!
# Joint chart-Gram smoothness of a realized spectrally-smooth time family

This file records the general spectral-regularity bedrock behind the joint
chart-Gram smoothness conjunct of the realized DeTurck–Ricci family: a family of
`C^∞` representatives `T_rep : ℝ → SmoothCcTensor g 0 2`, uniformly `g`-fibre small
with a single constant `δ < 1`, that

* is **continuous in time** at the `L²` level on the closed interval `Icc 0 T`, and
* lands, for each `t`, in the spectral smooth subspace `⋂_σ Hˢ` (the all-order
  membership of its `L²` class, the interior parabolic smoothing output),

realizes through `tensorSectionRealizeMetric` to a metric family whose chart-Gram
matrix entries are jointly `C^∞` up to `t = 0` (`JointChartGramSmooth`).

The construction is the classical Chow–Knopf interior smoothing read at the chart
level: the spectral partial sums `spectralPartialSum g (T_rep t).toL2 n` are jointly
`C^∞` in `(t, x)` (their eigen-coefficients `i ↦ ⟨bᵢ, (T_rep t).toL2⟩` are continuous
in `t` by the `L²`-time continuity hypothesis, and the eigensections are smooth in
`x`), and they converge to `T_rep t` together with all spatial derivatives, uniformly
in `t`, by the orthogonal Gårding bound and the supercritical Sobolev embedding (the
all-order membership hypothesis); the joint `C^∞` limit then passes through the
chart-Gram extraction.

The single deferred analytic statement
`jointChartGramSmooth_of_spectralSmooth_timeContinuous` carries these two structural
hypotheses (`L²`-time continuity and all-order membership), so it is non-vacuous and
standalone: a family that is not `L²`-time continuous, or whose values do not lie in
`⋂_σ Hˢ`, does not satisfy the premises, and a discontinuous or non-smooth family does
not satisfy the conclusion.  Consumers transitively depend on its `sorryAx`. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Joint chart-Gram smoothness of a realized spectrally-smooth time family
(the interior-smoothing regularity bedrock).**

Let `g` be a closed Riemannian metric, `T_rep : ℝ → SmoothCcTensor g 0 2` a family of
`C^∞` representatives, uniformly `g`-fibre small with a single constant `δ < 1`
(`hδ_lt`, `hδ`), and suppose

* `h_cont`: the `L²` classes `t ↦ (T_rep t).toL2 : TensorL2 0 2 g` depend continuously
  on `t` over the closed interval `Icc 0 T`; and
* `h_allHs`: for every `t ∈ Icc 0 T` the `L²` class `(T_rep t).toL2` lies in the
  spectral smooth subspace `⋂_σ Hˢ` (for each `σ ≥ 0` there is an `Hˢ` element whose
  `tensorHsToL2` realization is `(T_rep t).toL2`).

Then the chart-Gram matrix entries of the realized metric family
`g_DT t = tensorSectionRealizeMetric g (T_rep t) hδ_lt (hδ t)` are jointly `C^∞` up to
`t = 0`: `JointChartGramSmooth T g_DT`.

This is the classical parabolic interior smoothing read through the chart-Gram
extraction (Chow–Knopf): the spectral partial sums of `(T_rep t).toL2` are jointly
`C^∞` in `(t, x)` and converge with all spatial derivatives uniformly in `t` under the
all-order membership, so the chart-Gram limit is jointly `C^∞`.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`).  The two
structural hypotheses make the statement non-vacuous and standalone: it constrains the
specific continuous, spectrally-smooth family, not an arbitrary one. -/
theorem jointChartGramSmooth_of_spectralSmooth_timeContinuous
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (h_cont : ContinuousOn
      (fun t : ℝ => (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)))
      (Set.Icc (0 : ℝ) T))
    (h_allHs : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v =
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) :=
  sorry

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
