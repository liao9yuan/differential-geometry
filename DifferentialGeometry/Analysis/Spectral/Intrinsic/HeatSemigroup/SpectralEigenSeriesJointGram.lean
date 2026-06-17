import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint

/-!
# Joint chart-Gram smoothness from a *time-smooth* spectral eigen-coordinate family

This file records the corrected spectral-regularity bedrock behind the joint
chart-Gram smoothness conjunct of the realized DeTurck–Ricci family.  It replaces
the false-as-stated `jointChartGramSmooth_of_spectralSmooth_timeContinuous`
(`SpectralPartialSumJointGram.lean`), whose hypothesis was only `L²`-time
*continuity* of the family — which does **not** give joint `C^∞` (counterexample
`T_rep t = |t| · S₀`: the realized chart-Gram entries are then merely `C⁰`, not
`C^∞`, in `t`).

The corrected statement takes a genuinely **time-smooth** eigen-coordinate family
`φ : TensorEigenIdx g 0 2 → ℝ → ℝ` together with a single, `t`-independent,
summable-across-modes majorant on every time-jet of the weighted coordinate
squares — exactly the consumer-facing conclusion shape produced by
`perModeConv_allOrder_timeDeriv_spectralMass_le`
(`MaxRegInteriorTimeSmoothing.lean`).  Under these hypotheses the chart-Gram
matrix entries of the realized metric family
`g_DT t = tensorSectionRealizeMetric g (T_rep t) hδ_lt (hδ t)` are jointly `C^∞`
up to `t = 0` (`JointChartGramSmooth`).

## The reasoning route

The realized chart-Gram entry is *affine* in the tensor `T_rep t`:
`chartGramMatrix (realize g (T_rep t)) α x i j
  = chartGramMatrix g α x i j + ccTensorBilinSymm g (T_rep t) x (vᵢ) (vⱼ)`
(`tensorSectionRealizeMetric_inner`, `chartGramMatrix_apply`), where
`vₖ = chartBasisVecFiber α k x`.  The first (background) term is time-independent
and smooth in `x` (`chartGramMatrix_entry_contMDiffOn`); the time-dependence enters
only through the increment, and through `T_rep t`'s eigen-series
`T_rep t = ∑ᵢ φᵢ(t) · bᵢ`.

This file proves the manifold-level joint smoothness *in full* — the affine
decomposition, the background smoothness, the manifold↔Euclidean chart pull/push,
and the composition with the smooth moving chart point — and reduces the genuine
analytic content to a **single** Euclidean prerequisite: that the realized
chart-Gram increment, pulled through the inverse chart to a scalar function on
`ℝ × E`, is jointly `C^∞` on the closed-time slab over the chart target.

That Euclidean increment is the series
`(t, y) ↦ ∑' i, φᵢ(t) · ccTensorBilinSymm g (bᵢ) ((extChartAt α).symm y) (vᵢ) (vⱼ)`
of jointly-`C^∞` per-mode terms (time-`C^∞` `φᵢ` by `hφ_smooth`; space-`C^∞`
eigensection chart-component by `eigenvectorSmooth_contMDiff`), and joint `C^∞`
is the closed-set `M`-test series lemma `contDiffOn_tsum` applied per convex
chart-ball: the spatial chart `Sobolev ↪ Cᵏ` embedding of the eigensections
contributes a `tensorSobolevWeight`-power factor per spatial order, which the
supplied time-jet mode-mass hypothesis `hmodemass` absorbs into a
summable-across-modes majorant.

## Deferred analytic prerequisites (honest `sorry`s)

The Euclidean increment smoothness `realizedChartGramIncrement_euclidean_contDiffOn`
is **proved here in full** as the eigen-series assembly: `contDiffOn_tsum` applied per
convex chart-ball over the open-ball cover of the chart-target interior
(`contDiffOn_of_locally_contDiffOn`), with the per-mode joint smoothness
`eigenChartIncrementMode_contDiffOn` (also proved here, by the manifold↔Euclidean chart
transfer specialised to a fixed smooth eigensection).  The genuine remaining analytic
content is isolated as **two** named prerequisites, both categorically distinct from any
`ContDiffOn`/`ContMDiffOn` conclusion and not available on disk as public lemmas:

* `realizedChartGramIncrement_eigenSeries_eq` — the *pointwise* eigen-series identity for
  the increment (the chart-level `Sobolev → C⁰` convergence of the spectral partial sums to
  `T_rep t`, which on disk exists only at the `L²` norm level
  `spectralPartialSum_toL2_tendsto`); and
* `eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant` — the *per-mode mixed-jet
  chart `M`-test majorant* (the quantitative iterated chart `Sobolev ↪ Cᵇ` embedding for the
  tensor eigensections, Leibniz-combined with the supplied time-jet mode-mass `hmodemass` and
  summable across modes).

Both are honest `sorry`s; consumers transitively depend on their `sorryAx`. -/

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Additivity of the symmetrized extracted bilinear form in the tensor argument.**
The companion to `ccTensorBilinSymm_smul`: `ccTensorBilinSymm` is additive in the
`(0,2)`-tensor section.  Both `ccTensorBilin` and the symmetrization are linear in the
section, which is additive (`SmoothCcTensor.toSection_add`). -/
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S + T) x v w =
      ccTensorBilinSymm (I := I) g S x v w + ccTensorBilinSymm (I := I) g T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hbilin : ∀ (a b : TangentSpace I x),
      ccTensorBilin (I := I) g (S + T) x a b =
        ccTensorBilin (I := I) g S x a b + ccTensorBilin (I := I) g T x a b := by
    intro a b
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
    show ccTensorModel (I := I) g (S + T) x ![a, b] =
      ccTensorModel (I := I) g S x ![a, b] + ccTensorModel (I := I) g T x ![a, b]
    have hmodel : ccTensorModel (I := I) g (S + T) x =
        ccTensorModel (I := I) g S x + ccTensorModel (I := I) g T x := by
      rw [ccTensorModel, ccTensorModel, ccTensorModel]
      have hmul : (ccTensorMultilinear (I := I) g (S + T) x :
            Tensor0SBundle.Tensor0SSpace 2 I x) =
          (ccTensorMultilinear (I := I) g S x : Tensor0SBundle.Tensor0SSpace 2 I x) +
            (ccTensorMultilinear (I := I) g T x : Tensor0SBundle.Tensor0SSpace 2 I x) := by
        rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply, ccTensorMultilinear_apply,
          SmoothCcTensor.toSection_add]
        exact ContinuousLinearMap.add_apply _ _ _
      rw [hmul, Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [hmodel, ContinuousMultilinearMap.add_apply]
  rw [hbilin v w, hbilin w v]; ring

/-- The Euclidean *per-mode* increment scalar: for an eigen-index `i`, the chart-pulled
chart-Gram increment of the smooth eigensection `eigenvectorSmooth g 0 2 i`, weighted by the
smooth time coordinate `φ i`.  This is the summand of the eigen-series whose joint `C^∞`
smoothness (across the closed-time slab) assembles into the increment smoothness. -/
private def eigenChartIncrementMode
    (g : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ × E → ℝ :=
  fun q : ℝ × E =>
    φ i q.1 *
      ccTensorBilinSymm (I := I) g
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
          (I := I) (M := M) g 0 2 i)
        ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))

/-- **Per-mode joint smoothness (analytic prerequisite P0).**  Each eigen-series summand
`eigenChartIncrementMode` is jointly `C^∞` on the closed-time slab over the chart-target
interior.  In `t` it is the smooth coordinate `φ i` (`hφ_smooth`); in `y` it is the
chart-pulled chart-Gram increment of the *smooth* eigensection
`eigenvectorSmooth g 0 2 i` (a `C^∞` tensor section, whose chart component is `C^∞` in the
chart coordinate).  The product is jointly smooth.

The chart-pulled increment of a fixed smooth eigensection is `C^∞` in `y` through the same
manifold↔Euclidean chart transfer used by the sibling
`realizedChartGramIncrement_alongChart_contMDiffOn`, specialised to the time-constant
eigensection: the manifold scalar `x ↦ ccTensorBilinSymm g bᵢ x (vᵢ' x)(vⱼ' x)` is smooth on
the trivialization base set (the smooth Hom-section `ccTensorBilinSymm_contMDiff` evaluated on
the two smooth chart-basis sections, exactly as `chartGramMatrix_entry_contMDiffOn`), composed
with the smooth inverse chart `contMDiffOn_extChartAt_symm` and read as a Euclidean
`ContDiffOn` (`ContMDiffOn.contDiffOn`).  The product with the time-smooth coordinate is jointly
smooth. -/
private theorem eigenChartIncrementMode_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set S := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
    (I := I) (M := M) g 0 2 i with hS_def
  -- Step 1: the manifold scalar `x ↦ ccTensorBilinSymm g S x (vᵢ' x)(vⱼ' x)` is smooth on
  -- the trivialization base set, by the same `clm_bundle_apply₂` pattern as
  -- `chartGramMatrix_entry_contMDiffOn`.
  have hB : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g S b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    (MetricRealization.ccTensorBilinSymm_contMDiff (I := I) g S).contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i'
  have hw := chartBasisVec_contMDiffOn (I := I) α j'
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g S m
              (chartBasisVecFiber (I := I) α i' m)
              (chartBasisVecFiber (I := I) α j' m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id) hB hv hw
  have hScal : ContMDiffOn I 𝓘(ℝ) ∞
      (fun m : M => ccTensorBilinSymm (I := I) g S m
        (chartBasisVecFiber (I := I) α i' m)
        (chartBasisVecFiber (I := I) α j' m))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hpx := happ x hx
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
    exact hpx.2
  -- Step 2: rewrite the base set to the chart source, compose with the smooth inverse chart,
  -- and read off the Euclidean `ContDiffOn` in the chart coordinate `y`.
  rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hScal
  have hsource_eq : (chartAt H α).source = (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
  rw [hsource_eq] at hScal
  have hmapsTo : Set.MapsTo (extChartAt I α).symm (interior (extChartAt I α).target)
      (extChartAt I α).source := by
    intro y hy
    have hy' : y ∈ (extChartAt I α).target := interior_subset hy
    exact (extChartAt I α).map_target hy'
  have hsymm_cmdiff : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (interior (extChartAt I α).target) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) α).mono interior_subset
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hScal.comp hsymm_cmdiff hmapsTo
  have hSpace : ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hcomp.contDiffOn
  -- Step 3: the per-mode increment is `(φ i ∘ fst) · (space scalar ∘ snd)`, jointly smooth.
  have htime : ContDiffOn ℝ ∞ (fun q : ℝ × E => φ i q.1)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
  have hspaceComp : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hSpace.comp contDiffOn_snd (Set.mapsTo_snd_prod)
  exact htime.mul hspaceComp

/-- **Pointwise eigen-series identity (analytic prerequisite P1).**  On the closed-time
slab over the chart-target interior, the Euclidean chart-Gram increment of `T_rep q.1`
equals the eigen-series of its per-mode increments.  This is the chart-level (pointwise)
convergence `T_rep t = ∑' i, φ i t • eigenvectorSmooth g 0 2 i` of the spectral partial
sums — which on disk exists only at the `L²`/`H^s`-norm level
(`spectralPartialSum_toL2_tendsto`) — paired with the additivity of `ccTensorBilinSymm` in
its tensor argument.

Honest `sorry`: the chart-`C⁰` upgrade of the `L²` spectral convergence
(`spectralPartialSum_toL2_tendsto`) is not available on disk; it requires the **uniform-in-`i`
eigensection chart `H^{2k} ↪ C⁰` Sobolev embedding** — the same missing prerequisite carried
by `eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant` (P2) — so that the `L²`
partial-sum convergence upgrades to chart-`C⁰` (uniform pointwise) convergence and the
`ccTensorBilinSymm`-additivity gives the per-mode series.  Consumers transitively depend on its
`sorryAx`.  The `hcoeff` hypothesis (now relativized to the slab `t ∈ Icc 0 T`) fixes the
coordinates `φ i t` as the `L²` eigen-coordinates of `T_rep t`, so the identity is the genuine
spectral expansion, not a free posit. -/
private theorem realizedChartGramIncrement_eigenSeries_eq
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target,
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))
        = ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q :=
  sorry

/-- **Per-order summable mixed-jet majorant (analytic prerequisite P2).**  On a convex
subset `Icc 0 T ×ˢ B` of the slab over a **compact** chart-ball `B ⊆ interior target`, each
order-`k` within-iterated Fréchet derivative of the per-mode increment admits a single
summable-across-modes uniform majorant.  By the Leibniz product rule the mixed `(t, y)`-jet
is bounded by `∑_{a+b=k} |∂ₜ^a φ_i| · ‖∇^b(chart increment of eigensection)‖`; the spatial
factor is controlled, uniformly over the **compact** `B`, by the eigensection's chart
`H^{2k} ↪ C^b` Sobolev embedding — now reduced (away from the partition-of-unity kernel, near
the chart-target boundary) to the compact-uniform reverse-Christoffel order-peeling
`iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact` and order-`0` fibre bound
`exists_zeroContentR_le_fiberNorm_on_compact` (`CompactChartJetBound.lean`, both PROVEN),
composed with the global pointwise `C^m` embedding
`iteratedCovGrad_toSobolev_embedding_Cm_unconditional` — contributing a
`tensorSobolevWeight`-power factor, which the supplied summable time-jet mode-mass
(`hmodemass`) absorbs into a summable-across-modes bound.

**Domain correctness (the routing fix).**  The earlier free `{B} (hB : B ⊆ interior target)`
quantification was FALSE-as-posited: the chart-trivialisation operator norm blows up at the
chart-target boundary, so no `tensorSobolevWeight`-power majorant exists for an arbitrary
boundary-touching `B`.  Requiring `B` compact (e.g. a closed ball strictly inside the
interior) is exactly the domain on which the compact-uniform bounds hold; the consumer
`realizedChartGramIncrement_euclidean_contDiffOn` only ever needs a compact-in-interior ball
(it works locally per ball via `contDiffOn_of_locally_contDiffOn`), so the restriction does
not weaken the apex.

Honest `sorry`: the genuine remaining content is the **uniform-in-`i` eigensection chart
`H^{2k} ↪ C^b` Sobolev decay** — that `‖eigenvectorSmooth g 0 2 i .toHs (2k)‖` decays like a
fixed `tensorSobolevWeight`-power — feeding the `contDiffOn_tsum` `M`-test together with the
PROVEN compact-uniform reverse-peel.  Consumers transitively depend on its `sorryAx`.  The
`hmodemass` hypothesis supplies the time-jet mode mass, without which no uniform majorant
exists. -/
private theorem eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ k : ℕ, ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i :=
  sorry

/-- **The realized chart-Gram increment is jointly `C^∞` in chart coordinates.**

For a smooth representative family `T_rep` whose `L²` eigen-coordinates at time `t`
are `φ i t` (`hcoeff`), with `φ` time-smooth (`hφ_smooth`) and equipped with summable
time-jet mode-mass (`hmodemass`), the chart-Gram *increment*
`ccTensorBilinSymm g (T_rep t) ((extChartAt α).symm y) (vᵢ') (vⱼ')`, pulled to a scalar
function of `(t, y) : ℝ × E`, is jointly `C^∞` on the closed-time slab
`Icc 0 T ×ˢ interior (extChartAt α).target`.

The increment is the eigen-series
`∑' i, φᵢ(t) · ccTensorBilinSymm g (bᵢ) ((extChartAt α).symm y) (vᵢ') (vⱼ')` of
jointly-`C^∞` per-mode terms (`eigenChartIncrementMode_contDiffOn`, equal to the increment
by `realizedChartGramIncrement_eigenSeries_eq`); joint `C^∞` is the closed-set `M`-test
series lemma `contDiffOn_tsum` applied per convex chart-ball
(`Icc 0 T ×ˢ B`, convex as a product), the `M`-test majorant supplied by
`eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant`, and glued over the open
ball cover of `interior (extChartAt α).target` by `contDiffOn_of_locally_contDiffOn`.

This assembles the spectral series joint smoothness; the genuine analytic content is carried
by the three named prerequisites `eigenChartIncrementMode_contDiffOn` /
`realizedChartGramIncrement_eigenSeries_eq` /
`eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant` (honest `sorry`s, consumers
transitively depend on their `sorryAx`).  The hypotheses `hφ_smooth`/`hcoeff`/`hmodemass`
constrain it: a non-time-smooth `φ`, or one without summable time-jet mode-mass, does not
yield the joint `C^∞` increment. -/
theorem realizedChartGramIncrement_euclidean_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀
  -- Local set: the OPEN ball of radius `r/2`.  We prove `ContDiffOn` on the *compact* closed
  -- ball `closedBall y₀ (r/2)` — where the compact-uniform spatial majorant (P2) holds — and
  -- restrict (`mono`) to the requested open ball.
  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro x hx
    rw [hBc_def, Metric.mem_closedBall] at hx
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod
      (uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne)
  have hmajorant :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g φ hmodemass α i' j' hBc_compact hBc_sub
  classical
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun k => Classical.choose (hmajorant k) with hv_def
  have hv_spec : ∀ k, Summable (v k) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v k i :=
    fun k => Classical.choose_spec (hmajorant k)
  have htsum_Bc : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    refine DifferentialGeometry.Analysis.contDiffOn_tsum (v := v) (x₀ := (0, y₀))
      huniq hconv
      (fun i => (eigenChartIncrementMode_contDiffOn (I := I) (M := M) (T := T)
        g φ hφ_smooth α i' j' i).mono (Set.prod_mono (le_refl _) hBc_sub))
      (fun k _hk => (hv_spec k).1)
      (fun k i q hq _hk => (hv_spec k).2 i q hq)
      ⟨left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
  have htsum : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) T ×ˢ Ω := ⟨hq.1, hB_sub hq.2⟩
  exact realizedChartGramIncrement_eigenSeries_eq (I := I) (M := M) (T := T)
    g T_rep φ hcoeff α i' j' q hq'

/-- The realized chart-Gram increment, along the moving chart point, is jointly `C^∞` on
the closed-time slab over the trivialization base set: the Euclidean increment scalar (a
function on `ℝ × E`, supplied by `realizedChartGramIncrement_euclidean_contDiffOn`) is
composed with the smooth moving `(t, x) ↦ (t, extChartAt α x)`, carried pointwise through
the single normed-space model to avoid the product-model defeq blow-up. -/
private theorem realizedChartGramIncrement_alongChart_contMDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E =>
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)) with hG_def
  have hGEuclid : ContDiffOn ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    realizedChartGramIncrement_euclidean_contDiffOn
      (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i' j'
  set f : ℝ × M → ℝ × E := fun q : ℝ × M => (q.1, extChartAt I α q.2) with hf_def
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    exact hx
  have hmaps : Set.MapsTo f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    have hmem : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx'
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  have heq : Set.EqOn
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (G ∘ f)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    simp only [Function.comp, hG_def, hf_def]
    rw [(extChartAt I α).left_inv hx']
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

/-- **Joint chart-Gram smoothness of a realized time-smooth spectral family
(the corrected interior-smoothing regularity bedrock).**

Let `g` be a closed Riemannian metric, `T_rep : ℝ → SmoothCcTensor g 0 2` a family of
`C^∞` representatives, uniformly `g`-fibre small with a single constant `δ < 1`
(`hδ_lt`, `hδ`), and suppose

* `φ` is a genuinely **time-smooth** eigen-coordinate family (`hφ_smooth`) realizing the
  `L²` eigen-coordinates of `T_rep` (`hcoeff`); and
* `hmodemass`: every time-jet of the weighted coordinate squares admits a single,
  `t`-independent, summable-across-modes majorant on `[0,T]` — the consumer-facing
  conclusion shape produced by `perModeConv_allOrder_timeDeriv_spectralMass_le`.

Then the chart-Gram matrix entries of the realized metric family
`g_DT t = tensorSectionRealizeMetric g (T_rep t) hδ_lt (hδ t)` are jointly `C^∞` up to
`t = 0`: `JointChartGramSmooth T g_DT`.

This is the corrected form of `jointChartGramSmooth_of_spectralSmooth_timeContinuous`
(whose `L²`-time-*continuity* hypothesis is too weak — `T_rep t = |t| · S₀`
counterexample): time *smoothness* of the eigen-coordinates with summable time-jet
mode-mass is what makes the chart-Gram limit jointly `C^∞`.

The chart-Gram entry of the realized metric is affine in `T_rep t`; the time-constant
background part is smooth (`chartGramMatrix_entry_contMDiffOn`), and the increment is
jointly `C^∞` in chart coordinates (`realizedChartGramIncrement_euclidean_contDiffOn`,
the spectral series joint smoothness), pushed back through the smooth moving chart point.
Consumers transitively depend on the prerequisite's `sorryAx`. -/
theorem jointChartGramSmooth_of_spectralSmooth_timeSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) := by
  intro α i j
  have hincrement := realizedChartGramIncrement_alongChart_contMDiffOn
    (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i j
  have hbg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) g α p.2 i j)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hbase := chartGramMatrix_entry_contMDiffOn (I := I) g α i j
    have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      contMDiffOn_snd
    have hmaps : Set.MapsTo (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      fun p hp => hp.2
    exact hbase.comp hsnd hmaps
  refine (hbg.add hincrement).congr ?_
  rintro ⟨t, x⟩ _
  change Integral.Measure.chartGramMatrix (I := I)
      (tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) α x i j =
    Integral.Measure.chartGramMatrix (I := I) g α x i j +
      ccTensorBilinSymm (I := I) g (T_rep t) x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x)
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
