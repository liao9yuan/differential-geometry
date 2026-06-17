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
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.EigensectionSobolevDecay
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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

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

This is now proved in full.  The spatial factor of each per-mode increment is bounded,
uniformly over the compact `B`, by the **uniform-in-`i` eigensection chart `H^{2k} ↪ C^b`
Sobolev decay** (`eigenvectorSmooth_toHs_norm_le_lambda_pow`, the spectral norm of the
smooth eigensection equals its eigenvalue weight) composed with the compact-uniform
reverse-Christoffel order-peeling and `C^m` Sobolev embedding; the time factor of each
Leibniz summand is controlled, uniformly over `Icc 0 T`, by the supplied summable time-jet
mode-mass `hmodemass` (without which no uniform majorant exists).  The two factors are
combined across modes by the arithmetic–geometric-mean inequality against the Weyl
summability `tensorEigen_summable_negpow`. -/
private lemma norm_iteratedFDeriv_clm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (i : ℕ) (hi : 1 ≤ i) (x : F) :
    ‖iteratedFDeriv ℝ i (fun p => L p) x‖ ≤ (‖L‖ + 1) ^ i := by
  have hD1 : (1 : ℝ) ≤ ‖L‖ + 1 := by have := norm_nonneg L; linarith
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · interval_cases i
    rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    simp only [pow_one]; linarith [norm_nonneg L]
  · obtain ⟨j, rfl⟩ : ∃ jj, i = (jj + 1) + 1 := ⟨i - 2, by omega⟩
    have hz : ‖iteratedFDeriv ℝ ((j + 1) + 1) (fun p => L p) x‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv]
      have hfd : fderiv ℝ (fun p => L p) = fun _ : F => (L : F →L[ℝ] G) := by
        funext y; exact ContinuousLinearMap.fderiv L
      rw [hfd, iteratedFDeriv_const_of_ne (by omega) (L : F →L[ℝ] G)]
      simp
    rw [hz]; positivity

private lemma norm_iteratedFDerivWithin_compFst_le
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) {a bb : ℝ} {B : Set E}
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B)) (hab : a < bb)
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => f p.1) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set t := Set.Icc a bb with ht_def
  set L : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E with hL_def
  have hUDt : UniqueDiffOn ℝ t := uniqueDiffOn_Icc hab
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.1) s t := fun p hp => hp.1
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := f)
    (f := fun p : ℝ × E => p.1) (n := n) (s := s) (t := t) (x := q) (N := ∞)
    hf.contDiffOn contDiffOn_fst (by exact_mod_cast le_top) hUDt hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => by
      have heq : iteratedFDerivWithin ℝ i f t q.1 = iteratedFDeriv ℝ i f q.1 :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUDt
          (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hmaps hq)
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.1) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (f ∘ (fun p : ℝ × E => p.1)) = (fun p : ℝ × E => f p.1) := rfl
  rw [hcomp] at hbound
  exact hbound

private lemma norm_iteratedFDerivWithin_compSnd_le
    (spatial : E → ℝ) {O : Set E} (hO_open : IsOpen O)
    (hspatial : ContDiffOn ℝ ∞ spatial O)
    {a bb : ℝ} {B : Set E} (hBO : B ⊆ O)
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B))
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j spatial O q.2‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => spatial p.2) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set L : (ℝ × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ ℝ E with hL_def
  have hUDO : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.2) s O := fun p hp => hBO hp.2
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := spatial)
    (f := fun p : ℝ × E => p.2) (n := n) (s := s) (t := O) (x := q) (N := ∞)
    hspatial contDiffOn_snd (by exact_mod_cast le_top) hUDO hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.2) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.2) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_snd (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (spatial ∘ (fun p : ℝ × E => p.2)) = (fun p : ℝ × E => spatial p.2) := rfl
  rw [hcomp] at hbound
  exact hbound

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma ccTensorBilinSymm_eq_half_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H α).source) :
    ccTensorBilinSymm (I := I) g S p
        (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![a, b] p +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![b, a] p) := by
  classical
  rw [ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      (S.toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ccTensorBilin (I := I) g S p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]

private lemma norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m *
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
          (toEuclidean (E := E) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclN := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hcompose : rawCompOnE (I := I) (M := M) g S α Jdx =
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ∘ ⇑e := by
    have h := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrFun h (e z)
    simp only [Function.comp_apply, he_def] at this ⊢
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  rw [hcompose]
  set Oe : Set EuclN := e '' O with hOe_def
  have hOe_open : IsOpen Oe := e.isOpenMap O hO_open
  have hUDe : UniqueDiffOn ℝ Oe := hOe_open.uniqueDiffOn
  have hpre : (⇑e) ⁻¹' Oe = O := by rw [hOe_def, Set.preimage_image_eq _ e.injective]
  have hey : e y ∈ Oe := ⟨y, hy, rfl⟩
  have hOe_sub : Oe ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hOe_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, he_def, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset hx
  have hcr := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    hUDe (x := y) hey m
  rw [hpre] at hcr
  rw [hcr]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hOe_open hey]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma exists_rawCompOnE_jet_le_toHs_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    {B : Set E} (hB_compact : IsCompact B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  set K : Set EuclN := (toEuclidean (E := E)) '' B with hK_def
  have hK_compact : IsCompact K := hB_compact.image (toEuclidean (E := E)).continuous
  have hK_sub : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset (hB hx)
  set KM : Set M := (extChartAt I α).symm '' B with hKM_def
  have hKM_compact : IsCompact KM :=
    hB_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono
        (fun x hx => interior_subset (hB hx)))
  have hKM_sub : KM ⊆ (chartAt H α).source := by
    rw [hKM_def]
    rintro b ⟨x, hx, rfl⟩
    have hx' : x ∈ (extChartAt I α).target := interior_subset (hB hx)
    have := (extChartAt I α).map_target hx'
    rwa [extChartAt_source (I := I)] at this
  obtain ⟨Cpeel, hCpeel_nn, hpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact (I := I) (M := M) g 0 2 α m
      hK_compact hK_sub m (le_refl m)
  have hz_per : ∀ i : ℕ, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (S : SmoothCcTensor g 0 2) {b : M}, b ∈ KM →
      zeroContentR (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad g 0 2 i S) α (toEuclidean (E := E) (extChartAt I α b)) ≤
        Cz * (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    intro i
    obtain ⟨Cz, hCz_nn, hCz⟩ :=
      exists_zeroContentR_le_fiberNorm_on_compact (I := I) (M := M) g 0 (2 + i) α
        hKM_compact hKM_sub
    exact ⟨Cz, hCz_nn, fun S b hb => hCz (iteratedCovGrad g 0 2 i S) hb⟩
  choose Czf hCzf_nn hCzf using hz_per
  set Czmax : ℝ := (Finset.range (m + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)) Czf with hCzmax_def
  have hCzmax_nn : 0 ≤ Czmax := by
    rw [hCzmax_def]
    exact le_trans (hCzf_nn 0) (Finset.le_sup' Czf (Finset.mem_range.mpr (Nat.succ_pos m)))
  have hCz_le : ∀ i ∈ Finset.range (m + 1), Czf i ≤ Czmax :=
    fun i hi => Finset.le_sup' Czf hi
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm_unconditional (I := I) (M := M) g 0 2 k m h_super
  set Cnorm : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m with hCnorm_def
  have hCnorm_nn : 0 ≤ Cnorm := by rw [hCnorm_def]; positivity
  refine ⟨Cnorm * (Cpeel * (Czmax * Cemb)), by positivity, fun S y hy => ?_⟩
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  set b : M := (extChartAt I α).symm y with hb_def
  have hyt : y ∈ (extChartAt I α).target := interior_subset (hB hy)
  have hb_mem : b ∈ KM := ⟨y, hy, rfl⟩
  have hyB : toEuclidean (E := E) y ∈ K := ⟨y, hy, rfl⟩
  have hy_eq : extChartAt I α b = y := by rw [hb_def]; exact (extChartAt I α).right_inv hyt
  have hrev := norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR (I := I) (M := M) g S α Jdx m (hB hy)
  refine le_trans hrev ?_
  have hpeel_y := hpeel S m (le_refl m) 0 (by omega) (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
    (toEuclidean (E := E) y) hyB
  rw [iteratedCovGrad_zero] at hpeel_y
  have hsum_fiber : ∑ i ∈ Finset.range (m + 1),
        zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
          (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
      Czmax * ∑ i ∈ Finset.range (m + 1),
        (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
        ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Nat.zero_add]
    have hzi := hCzf i S hb_mem
    rw [hy_eq] at hzi
    refine le_trans hzi ?_
    letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    exact mul_le_mul_of_nonneg_right (hCz_le i hi) (norm_nonneg _)
  have hemb := hCemb S b
  have hpeel_y' : ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖ ≤
      Cpeel * (Czmax * (Cemb * N)) := by
    refine le_trans hpeel_y ?_
    have hstep1 : Cpeel * ∑ i ∈ Finset.range (m + 1),
          zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
            (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
        Cpeel * (Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖)) :=
      mul_le_mul_of_nonneg_left hsum_fiber hCpeel_nn
    refine le_trans hstep1 ?_
    have hfiber_le : ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Cemb * N := hemb
    have hthis : Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Czmax * (Cemb * N) :=
      mul_le_mul_of_nonneg_left hfiber_le hCzmax_nn
    exact mul_le_mul_of_nonneg_left hthis hCpeel_nn
  calc Cnorm * ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖
      ≤ Cnorm * (Cpeel * (Czmax * (Cemb * N))) :=
        mul_le_mul_of_nonneg_left hpeel_y' hCnorm_nn
    _ = Cnorm * (Cpeel * (Czmax * Cemb)) * N := by ring

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
/-- The spatial factor of the per-mode increment, as a function on `E` (the chart target):
`y ↦ ccTensorBilinSymm g (eᵢ) ((extChartAt α).symm y) (vᵢ')(vⱼ')`, equal on the chart-target
interior to `(1/2)(rawCompOnE ![i',j'] + rawCompOnE ![j',i'])`. -/
private def eigenSpatialFactor
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : E → ℝ :=
  fun y : E =>
    ccTensorBilinSymm (I := I) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i)
      ((extChartAt I α).symm y)
      (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
      (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y))

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma eigenSpatialFactor_eqOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    Set.EqOn (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (fun y : E => (1 / 2 : ℝ) *
        (rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y))
      (interior (extChartAt I α).target) := by
  intro y hy
  have hsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hyt : y ∈ (extChartAt I α).target := interior_subset hy
    have := (extChartAt I α).map_target hyt
    rwa [extChartAt_source (I := I)] at this
  rw [eigenSpatialFactor,
    ccTensorBilinSymm_eq_half_rawComponent (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α i' j' hsrc]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma eigenSpatialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (interior (extChartAt I α).target) := by
  refine ContDiffOn.congr ?_ (eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i)
  have hadd : ContDiffOn ℝ ∞
      (fun y : E => rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y)
      (interior (extChartAt I α).target) :=
    (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j']).add
      (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'])
  exact contDiffOn_const.mul hadd

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma exists_eigenSpatialFactor_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E)) (m : ℕ)
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hUDO : UniqueDiffOn ℝ O := isOpen_interior.uniqueDiffOn
  -- Embedding order covering all spatial orders up to m.
  set kE : ℕ := Module.finrank ℝ E + 2 * m + 1 with hkE_def
  -- Per-order spatial bound (single embedding order kE works for every m' ≤ m).
  have hper : ∀ m' : ℕ, m' ≤ m → ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y‖ ≤
          Cm' * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
   intro m' hm'
   have h_super : 2 * kE > Module.finrank ℝ E + 2 * m' := by rw [hkE_def]; omega
   obtain ⟨Cab, hCab_nn, hCab⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![i', j'] m' kE h_super hB_compact hB
   obtain ⟨Cba, hCba_nn, hCba⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![j', i'] m' kE h_super hB_compact hB
   obtain ⟨Cdec, hCdec_nn, hCdec⟩ :=
     eigenvectorSmooth_toHs_norm_le_lambda_pow (I := I) (M := M) g kE
   refine ⟨(1 / 2 : ℝ) * (Cab + Cba) * Cdec, by positivity, fun i y hy => ?_⟩
   set S := eigenvectorSmooth (I := I) (M := M) g 0 2 i with hS_def
   -- Jet of eigenSpatialFactor = jet of (1/2 • (rawCompOnE_ab + rawCompOnE_ba)).
   have hcongr : iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y =
       iteratedFDerivWithin ℝ m'
         ((1 / 2 : ℝ) • (rawCompOnE (I := I) (M := M) g S α ![i', j'] +
           rawCompOnE (I := I) (M := M) g S α ![j', i'])) O y := by
     refine iteratedFDerivWithin_congr ?_ (hB hy) m'
     intro z hz
     rw [eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i hz]
     simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hS_def]
   rw [hcongr]
   have hcd_ab : ContDiffWithinAt ℝ (m' : ℕ∞) (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![i', j']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   have hcd_ba : ContDiffWithinAt ℝ (m' : ℕ∞) (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![j', i']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   rw [iteratedFDerivWithin_const_smul_apply (f := rawCompOnE (I := I) (M := M) g S α ![i', j'] +
         rawCompOnE (I := I) (M := M) g S α ![j', i']) (hcd_ab.add hcd_ba) hUDO (hB hy),
     iteratedFDerivWithin_add_apply hcd_ab hcd_ba hUDO (hB hy)]
   refine le_trans (norm_smul_le (1 / 2 : ℝ)
     (iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
       iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y)) ?_
   have htri : ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
         iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖ ≤
       Cab * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ +
         Cba * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ :=
     le_trans (norm_add_le _ _) (add_le_add (hCab S y hy) (hCba S y hy))
   set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ with hN_def
   have hN_nn : 0 ≤ N := norm_nonneg _
   have hdec : N ≤ Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := hCdec i
   have hbase_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) :=
     pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _
   calc ‖(1 / 2 : ℝ)‖ * ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
           iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖
       ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * N) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         calc ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
               iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖
             ≤ Cab * N + Cba * N := htri
           _ = (Cab + Cba) * N := by ring
     _ ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * (Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE))) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         exact mul_le_mul_of_nonneg_left hdec (by positivity)
     _ = (1 / 2 : ℝ) * (Cab + Cba) * Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
         rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; ring
  choose Cf hCf_nn hCf using hper
  set Cmax : ℝ := (Finset.range (m + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun b => if hb : b ≤ m then Cf b hb else 0) with hCmax_def
  have hCmax_ge : ∀ (m' : ℕ) (h : m' ≤ m), Cf m' h ≤ Cmax := by
    intro m' h
    rw [hCmax_def]
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun b => if hb : b ≤ m then Cf b hb else 0)
      (Finset.mem_range.mpr (by omega : m' < m + 1)))
    rw [dif_pos h]
  refine ⟨Cmax, 2 * kE, ?_, fun m' hm' i y hy => ?_⟩
  · exact le_trans (hCf_nn 0 (Nat.zero_le m)) (hCmax_ge 0 (Nat.zero_le m))
  · refine le_trans (hCf m' hm' i y hy) ?_
    refine mul_le_mul_of_nonneg_right (hCmax_ge m' hm') ?_
    exact pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private theorem eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB_uniq : UniqueDiffOn ℝ B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ k : ℕ, ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro k
  set O : Set E := interior (extChartAt I α).target with hO_def
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq
  -- Spatial decay exponent: a single `pSp` covering all spatial orders `b ≤ k`.
  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ :=
    exists_eigenSpatialFactor_jet_le_lambda_pow (I := I) (M := M) g α i' j' k hB_compact hB
  -- The time mode-mass at order `σ := 2 * pSp + 2 * (weylSobolevExp + 1)`, per time-jet order `a ≤ k`.
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  set σ0 : ℝ := 2 * (pSp : ℝ) + 2 * (sW : ℝ) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
  -- For each time order `a`, the summable mode-mass `Cmaj a`.
  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cm ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i :=
    fun a => hmodemass a σ0 hσ0_nn
  choose Cmf hCmf_summable hCmf using htime
  -- Weyl summability of `(1 + λ)^(-2 sW)`.
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ)))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * (sW : ℝ)) ?_
    rw [hsW_def]; push_cast; have := weylSobolevExp_gt_finrank (E := E); push_cast at this ⊢
    have h0 : (0:ℝ) ≤ (weylSobolevExp (E := E) : ℝ) := by positivity
    nlinarith [h0]
  -- Time-factor pointwise bound: `|∂ʲφi t| ≤ sqrt(Cmf j i) * (1+λ)^{-σ0/2}` for `t ∈ Icc`.
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have htime_pt : ∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) T →
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) := by
    intro j i t ht
    have hmm := hCmf j i t ht
    -- (1+λ)^σ0 * (∂ʲφ)² ≤ Cmf j i, σ0 = 2pSp + 2sW.
    have hw : tensorSobolevWeight (I := I) (M := M) i σ0 =
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ))) ^ 2 := by
      unfold tensorSobolevWeight
      rw [hσ0_def, show 2 * (pSp : ℝ) + 2 * (sW : ℝ) = ((pSp : ℝ) + (sW : ℝ)) * 2 by ring,
        Real.rpow_mul (hbase_pos i).le, Real.rpow_two]
    rw [hw] at hmm
    set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ)) with hW_def
    have hW_pos : 0 < W := Real.rpow_pos_of_pos (hbase_pos i) _
    -- W² (∂ʲφ)² ≤ Cmf, so |∂ʲφ| ≤ sqrt(Cmf)/W = sqrt(Cmf)·W⁻¹.
    have hCm_nn : 0 ≤ Cmf j i := le_trans (by positivity) hmm
    have habs : |iteratedDeriv j (φ i) t| ≤ Real.sqrt (Cmf j i) / W := by
      rw [le_div_iff₀ hW_pos]
      have h2 : (|iteratedDeriv j (φ i) t| * W) ^ 2 ≤ (Real.sqrt (Cmf j i)) ^ 2 := by
        rw [Real.sq_sqrt hCm_nn, mul_pow, sq_abs]
        nlinarith [hmm, hW_pos.le]
      have hlhs_nn : 0 ≤ |iteratedDeriv j (φ i) t| * W := by positivity
      nlinarith [Real.sqrt_nonneg (Cmf j i), h2, hlhs_nn, sq_nonneg (|iteratedDeriv j (φ i) t| * W - Real.sqrt (Cmf j i))]
    rw [Real.rpow_neg (hbase_pos i).le]
    rw [div_eq_mul_inv] at habs
    rwa [← hW_def]
  -- The per-mode majorant.
  set Kconst : ℝ := (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hwfun_sq : ∀ i, wfun i ^ 2 = tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ))) := by
    intro i
    rw [hwfun_def]
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hCm_nn : ∀ (a : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a i
    have h := hCmf a i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) with htermf_def
  have hw2_summable : Summable (fun i => wfun i ^ 2) := by simp_rw [hwfun_sq]; exact hweyl
  have hsqrt_summable : ∀ j, Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j
    have hbound : ∀ i, Real.sqrt (Cmf j i) * wfun i ≤ (Cmf j i + wfun i ^ 2) / 2 := by
      intro i
      have h1 : Real.sqrt (Cmf j i) * wfun i ≤ (Real.sqrt (Cmf j i) ^ 2 + wfun i ^ 2) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt (Cmf j i) - wfun i), Real.sq_sqrt (hCm_nn j i)]
      rwa [Real.sq_sqrt (hCm_nn j i)] at h1
    have hnn : ∀ i, 0 ≤ Real.sqrt (Cmf j i) * wfun i :=
      fun i => mul_nonneg (Real.sqrt_nonneg _) (hwfun_nn i)
    exact Summable.of_nonneg_of_le hnn hbound (((hCmf_summable j).add hw2_summable).div_const 2)
  have htermf_summable : ∀ a, Summable (termf a) := by
    intro a
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j _ => hsqrt_summable j)
  refine ⟨fun i => ∑ a ∈ Finset.range (k + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a _ => htermf_summable a)
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ ∞ (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ ∞ (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s := by
      refine (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i).comp contDiffOn_snd ?_
      intro p hp; exact hB hp.2
    have heqmode : eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i =
        (fun p : ℝ × E => φ i p.1) * (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) := by
      funext p; rw [eigenChartIncrementMode]; rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := k) (by exact_mod_cast le_top)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (k + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    -- Time factor `Cφa`.
    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le (φ i) (hφ_smooth i) hUD hT a q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (eigenSpatialFactor (I := I) (M := M) g α i' j' i) isOpen_interior
      (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i) hB hUD (k - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)
    -- Now combine: term ≤ C(k,a) * (a! Cφa (‖fst‖+1)ᵃ) * ((k-a)! Csp(1+λ)^pSp (‖snd‖+1)^{k-a}).
    have hfn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ := norm_nonneg _
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (k - a)
        (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (k.choose a : ℝ) := by positivity
    have hF1 := hfst_bnd
    have hG1 := hsnd_bnd
    -- Bound the product of the two factors, then multiply by the choose coefficient.
    have hsp_nn : 0 ≤ Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp :=
      mul_nonneg hCsp_nn (pow_nonneg hbase_nn _)
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (k - a)
            (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a)) := by
      refine mul_le_mul hF1 hG1 hgn_nn ?_
      positivity
    calc (k.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖
        = (k.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖) := by ring
      _ ≤ (k.choose a : ℝ) * (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]
          -- Regroup: the (1+λ)^{-(pSp+sW)} · (1+λ)^pSp = (1+λ)^{-sW}.
          have hcollapse : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (k.choose a : ℝ) ≤ (2 : ℝ) ^ k := by
            calc (k.choose a : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow k a
              _ = (2:ℝ) ^ k := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le hak
          have hfka : ((k-a).factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) hak
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)
          -- Assemble all bounds via nlinarith-style monotone multiplication.
          have hlhs_eq : (k.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) =
              ((k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp) *
              (Ssqrt * ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
                (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hcoef_nn : (0:ℝ) ≤ (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp := by positivity
            have hstep : (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp ≤
                (2:ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp := by
              have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
              have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
              gcongr
            exact hstep
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

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
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  have hmajorant :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g hT φ hφ_smooth hmodemass α i' j' hBc_compact huniqBc hBc_sub
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
