import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossLimits
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDiv
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorWeakPartials
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.TensorChartBilinearData
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.AbstractChartPull
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolutionDirichlet
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.BootstrapSource
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.RotatedTestSection
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovariantLeibniz
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# The eigenvector chart variational identity and the chart-bilinear data
# assembly

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
and a component multi-index `P₀`, this module assembles the per-component
chart-local weak-elliptic identity for the `P₀`-chart-component of the abstract
connection-Laplacian eigenvector, and packages it into the chart-bilinear
divergence-form data structure `TensorChartBilinearH1ComplData`.

The variational-identity assembly applies the source-free per-approximant chart
bilinear identity `tensorComponent_chartBilinIdentity_of_dirichlet` to the
partition-of-unity-weighted canonical smooth approximants
`Tₙ := eigenvectorPouApprox g r s h_atlas i α n = pouSmul g r s α
(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor`. The per-approximant
identity holds for every `n`; the `n → ∞` limit of both sides — assembled from
the lower-order source limits proven below, the main-Dirichlet limit
`mainDir_tendsto`, and the cross-Leibniz limits of the sibling files — turns it
into a chart variational identity for the eigenvector chart component.

## Main results

* `covPrincipalRotationCoeff_source_tendsto`,
  `covLowerOrderRotationValueCoeff_source_tendsto`,
  `weightedGradCoeffDivSum_source_tendsto` — the `n → ∞` limits of the three
  explicit lower-order source terms of the per-approximant chart bilinear
  identity.
* `eigenvectorChartVariationalIdentity` — the per-component chart variational
  identity, in the exact density-weighted shape of the
  `variational_identity` field of `ChartBilinearH1ComplData`.
* `eigenvectorTensorChartBilinearData` — the chart-bilinear divergence-form
  data `TensorChartBilinearH1ComplData g r s α P₀` of the eigenvector
  `P₀`-chart-component.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## `L²`-pairing convergence

If a sequence `g n` converges to `g_lim` in `Lp ℝ 2 μ` and `m ∈ Lp ℝ 2 μ` is
fixed, then the real integrals `∫ m · g n dμ` converge to `∫ m · g_lim dμ`. The
`L²` inner product is continuous, and the integral of the pointwise product is
the real `L²` inner product. -/

/-- **Convergence of an `L²` integral against a fixed test element.** For a
sequence `g : ℕ → Lp ℝ 2 μ` converging to `g_lim` and a fixed `m : Lp ℝ 2 μ`,
the real integrals `∫ m · g n dμ` converge to `∫ m · g_lim dμ`. -/
private lemma tendsto_lp_inner_integral
    {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (m : Lp ℝ 2 μ) {g : ℕ → Lp ℝ 2 μ} {g_lim : Lp ℝ 2 μ}
    (h_tendsto : Filter.Tendsto g atTop (𝓝 g_lim)) :
    Filter.Tendsto (fun n => ∫ a, (m : β → ℝ) a * (g n : β → ℝ) a ∂μ)
      atTop (𝓝 (∫ a, (m : β → ℝ) a * (g_lim : β → ℝ) a ∂μ)) := by
  classical
  have h_inner_eq : ∀ (f : Lp ℝ 2 μ),
      ∫ a, (m : β → ℝ) a * (f : β → ℝ) a ∂μ = ⟪m, f⟫_ℝ := by
    intro f
    rw [L2.inner_def (𝕜 := ℝ) m f]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    change (m : β → ℝ) a * (f : β → ℝ) a =
      @inner ℝ _ _ ((m : β → ℝ) a) ((f : β → ℝ) a)
    rw [show @inner ℝ _ _ ((m : β → ℝ) a) ((f : β → ℝ) a) =
        (f : β → ℝ) a * (m : β → ℝ) a from RCLike.inner_apply _ _]
    ring
  rw [h_inner_eq g_lim,
    show (fun n => ∫ a, (m : β → ℝ) a * (g n : β → ℝ) a ∂μ) =
      (fun n => ⟪m, g n⟫_ℝ) from funext (fun n => h_inner_eq (g n))]
  exact (continuous_inner.tendsto (m, g_lim)).comp
    (Filter.Tendsto.prodMk_nhds tendsto_const_nhds h_tendsto)

/-! ## The partition-of-unity-weighted canonical smooth approximant

`eigenvectorPouApprox g r s h_atlas i α n` is the partition-of-unity-weighted
`n`-th canonical smooth `H¹`-approximant `pouSmul g r s α
(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor`; it is a smooth
compactly-supported `(r, s)`-tensor section supported inside the chart-`α`
source, the section the source-free per-approximant chart bilinear identity is
applied to. -/

/-- The partition-of-unity-weighted `n`-th canonical smooth approximant
`pouSmul g r s α (eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor`, a
smooth compactly-supported `(r, s)`-tensor section supported in the chart-`α`
source. -/
def eigenvectorPouApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) : SmoothCcTensor g r s :=
  pouSmul (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor

/-- The chart-Euclidean partial derivative of a function vanishes off the
topological support of that function: on the open complement of the support the
function is locally zero, so its Fréchet derivative there is the zero map. -/
private lemma euclidPartial_zero_off_tsupport
    {u : EuclN → ℝ} (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ tsupport u) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hopen_c : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hy)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- The chart-pulled weighted-`MemLp` test element `densityOnEuclid g α · ψ` of
the chart target, used to pair the lower-order `L²`-limits against the chart
density and the test function. -/
private lemma densityOnEuclid_mul_test_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun y => densityOnEuclid (I := I) g α y * ψ y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have h_cd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y * ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α) hψ hψ_supp
  have h_cs : HasCompactSupport (fun y => densityOnEuclid (I := I) g α y * ψ y) :=
    hasCompactSupport_mul_chartTest (E := E) hψ_cs
  rw [chartL2Measure]
  exact (h_cd.continuous.memLp_of_hasCompactSupport h_cs).restrict _

/-- The test function `ψ` is `MemLp 2` of the chart-`L²` measure when it is `C^∞`
and compactly supported. -/
private lemma test_memLp
    (α : M) {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ) :
    MemLp ψ 2 (chartL2Measure (I := I) (M := M) α) := by
  rw [chartL2Measure]
  exact (hψ.continuous.memLp_of_hasCompactSupport hψ_cs).restrict _

/-! ## The `n → ∞` limit of the principal-rotation source term

The principal-rotation source term `∫ y, densityOnEuclid g α y ·
covPrincipalRotationCoeff g r s Tₙ α P₀ y · ψ y ∂volume` of the source-free
chart bilinear identity, evaluated at the partition-of-unity-weighted canonical
smooth approximants `Tₙ`, converges to its chart-density-weighted limit built
from `covPrincipalRotationCoeffLimit`. -/

/-- **The `n → ∞` limit of the principal-rotation source term.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a chart
center `α : M`, a component multi-index `P₀`, and a chart-supported smooth test
function `ψ`, the principal-rotation source terms `∫ densityOnEuclid g α ·
covPrincipalRotationCoeff g r s Tₙ α P₀ · ψ` at the partition-of-unity-weighted
canonical smooth approximants converge, as `n → ∞`, to `∫ densityOnEuclid g α ·
covPrincipalRotationCoeffLimit g r s h_atlas i α P₀ · ψ`. -/
theorem covPrincipalRotationCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set μch : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμch_def
  set m : Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp _
    with hm_def
  set glim : Lp ℝ 2 μch :=
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s h_atlas i α P₀).toLp _ with hglim_def
  set gseq : ℕ → Lp ℝ 2 μch := fun n =>
    (covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covPrincipalRotationCoeff_tendsto (I := I) (M := M)
      g r s h_atlas i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

/-! ## The `n → ∞` limit of the lower-order rotation value source term -/

/-- **The `n → ∞` limit of the lower-order rotation value source term.** The
lower-order rotation value source terms `∫ densityOnEuclid g α ·
covLowerOrderRotationValueCoeff g r s Tₙ α P₀ · ψ` at the
partition-of-unity-weighted canonical smooth approximants converge, as `n → ∞`,
to `∫ densityOnEuclid g α · covLowerOrderRotationValueCoeffLimit g r s h_atlas
i α P₀ · ψ`. -/
theorem covLowerOrderRotationValueCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set μch : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμch_def
  set m : Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp _
    with hm_def
  set glim : Lp ℝ 2 μch :=
    (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
      g r s h_atlas i α P₀).toLp _ with hglim_def
  set gseq : ℕ → Lp ℝ 2 μch := fun n =>
    (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covLowerOrderRotationValueCoeff_tendsto (I := I) (M := M)
      g r s h_atlas i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

/-! ## The `n → ∞` limit of the lower-order gradient divergence source term -/

/-- **The `n → ∞` limit of the lower-order gradient divergence source term.** The
lower-order gradient divergence source terms `∫ (∑_l euclidPartial l
(weightedGradCoeff g r s Tₙ α P₀ l)) · ψ` at the partition-of-unity-weighted
canonical smooth approximants converge, as `n → ∞`, to `∫ (∑_l
weightedGradCoeffDivLimit g r s h_atlas i α P₀ l) · ψ`. -/
theorem weightedGradCoeffDivSum_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
              α P₀ l) y) * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y) * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set m : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    (test_memLp (I := I) (M := M) α hψ hψ_cs).toLp _ with hm_def
  set gseq : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) := fun n =>
    ∑ l : Fin (Module.finrank ℝ E),
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l n).toLp _ with hgseq_def
  set glim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    ∑ l : Fin (Module.finrank ℝ E),
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l).toLp _ with hglim_def
  have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α] ψ := by
    rw [hm_def]; exact MemLp.coeFn_toLp _
  have h_gseq_ae : ∀ n : ℕ, (gseq n : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ l) y := fun n => by
    rw [hgseq_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l n)
  have h_glim_ae : (glim : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ l y := by
    rw [hglim_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ l)
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
                α P₀ l) y) * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
              α P₀ l) y) * ψ y := by
      filter_upwards [h_m_ae, h_gseq_ae n] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l y) * ψ y ∂(volume : Measure EuclN) := by
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l y) * ψ y := by
      filter_upwards [h_m_ae, h_glim_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) :=
    weightedGradCoeffDivSum_tendsto (I := I) (M := M) g r s h_atlas i α P₀
  have h_main := tendsto_lp_inner_integral
    (μ := chartL2Measure (I := I) (M := M) α) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

/-! ## The partition-of-unity kernel as a uniform compact support set

The partition-of-unity-weighted approximant `Tₙ := eigenvectorPouApprox …` is, for
every `n`, supported inside the closed support of the chart-atlas
partition-of-unity weight; its Euclidean chart component is therefore supported
inside the partition-of-unity kernel `chartPouKernel α`, uniformly in `n`. The
kernel is a compact subset of the open chart target, so it furnishes a single
compact `K` containing the topological support of the chart component of every
approximant — the input the source-free per-approximant chart bilinear identity
needs. -/

/-- The Euclidean chart component of the `n`-th partition-of-unity-weighted
approximant is supported inside the partition-of-unity kernel `chartPouKernel α`,
uniformly in `n`. -/
private lemma eigenvectorPouApprox_component_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ⊆
      chartPouKernel (I := I) (M := M) α := by
  rw [eigenvectorPouApprox,
    ← tensorChartComponent_eq_tensorComponentEuclid_pouSmul]
  exact tensorChartComponent_tsupport_subset_chartPouKernel (I := I) (M := M)
    g r s _ α P₀.1 P₀.2

/-- The `n`-th partition-of-unity-weighted approximant has its underlying tensor
field supported inside the chart-`α` source. -/
private lemma eigenvectorPouApprox_tsupport_subset_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) :
    tsupport (eigenvectorPouApprox (I := I) (M := M)
        g r s h_atlas i α n).toFun ⊆ (chartAt H α).source :=
  pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α _

/-! ## The chart-Euclidean partial of an approximant chart component is `MemLp`

The Euclidean chart component `uₙ := tensorComponentEuclid g r s Tₙ α P₀` of the
`n`-th partition-of-unity-weighted approximant is globally `C^∞` with compact
support inside the chart target; each chart-Euclidean partial `euclidPartial k
uₙ` is therefore again globally `C^∞` with compact support, hence `MemLp 2` with
respect to the chart-`L²` measure. -/

/-- The Euclidean chart component of the `n`-th partition-of-unity-weighted
approximant is globally `C^∞`. -/
private lemma eigenvectorPouApprox_component_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) :=
  tensorComponentEuclid_contDiff (I := I) (M := M) g r s
    (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀
    (eigenvectorPouApprox_tsupport_subset_source (I := I) (M := M)
      g r s h_atlas i α n)

/-- The chart-Euclidean partial `euclidPartial k uₙ` of the Euclidean chart
component of the `n`-th approximant is globally `C^∞`. -/
private lemma euclidPartial_eigenvectorPouApprox_component_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)) :=
  euclidPartial_contDiff (E := E)
    (eigenvectorPouApprox_component_contDiff (I := I) (M := M)
      g r s h_atlas i α P₀ n) k

/-- The chart-Euclidean partial `euclidPartial k uₙ` of the Euclidean chart
component of the `n`-th approximant has compact support. -/
private lemma euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    HasCompactSupport (euclidPartial (E := E) k
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (K := chartPouKernel (I := I) (M := M) α)
    (chartPouKernel_isCompact (I := I) (M := M) α) ?_
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyK
  refine hy ?_
  -- `uₙ` vanishes on a neighbourhood of `y` (off the closed kernel), so its
  -- chart-Euclidean partial there is zero.
  have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
  have hu_evt : (tensorComponentEuclid (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
      =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
      (fun z hz => image_eq_zero_of_notMem_tsupport
        (fun h => hz (eigenvectorPouApprox_component_tsupport_subset
          (I := I) (M := M) g r s h_atlas i α P₀ n h)))
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- The chart-Euclidean partial `euclidPartial k uₙ` of the Euclidean chart
component of the `n`-th approximant is `MemLp 2` with respect to the chart-`L²`
measure. -/
private lemma euclidPartial_eigenvectorPouApprox_component_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp (euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  rw [chartL2Measure]
  exact ((euclidPartial_eigenvectorPouApprox_component_contDiff (I := I) (M := M)
    g r s h_atlas i α P₀ k n).continuous.memLp_of_hasCompactSupport
    (euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
      (I := I) (M := M) g r s h_atlas i α P₀ k n)).restrict _

/-! ## The `L²` class of an approximant chart partial as a continuous-linear-map
## value

The chart-Euclidean partial `euclidPartial k uₙ` of the Euclidean chart
component of the `n`-th partition-of-unity-weighted approximant agrees almost
everywhere — by `eigenvectorChartPartialLp_approx_coeFn`,
`chosenWeakPartial'_tensorChartComponent_ae_eq` and the chart-component
identification `tensorChartComponent_eq_tensorComponentEuclid_pouSmul` — with the
coercion-to-function of the value of the canonical chart-partial continuous
linear map at the completion embedding of the smooth approximant. Its `L²` class
is therefore exactly that continuous-linear-map value, and converges, as
`n → ∞`, to `μ` times the candidate weak chart partial. -/

/-- The coercion-to-function of `eigenvectorChartPartialCLM g r s α P₀ k` at the
completion embedding of the `n`-th smooth approximant agrees almost everywhere,
on the chart-`L²` measure, with the chart-Euclidean partial of the Euclidean
chart component of the `n`-th partition-of-unity-weighted approximant. -/
private lemma eigenvectorChartPartialCLM_smoothApprox_coeFn_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) := by
  classical
  have hμ : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h1 := eigenvectorChartPartialLp_approx_coeFn (I := I) (M := M)
    g r s h_atlas i α P₀ k n
  have h2 := chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
    g r s (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    α P₀.1 P₀.2 k
  have h3 : tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        α P₀.1 P₀.2 =
      tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀ := by
    rw [eigenvectorPouApprox]
    exact tensorChartComponent_eq_tensorComponentEuclid_pouSmul (I := I) (M := M)
      g r s α _ P₀
  have hsmul := Lp.coeFn_smul (i.fst.val)⁻¹
    (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)))
  have h4 : ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have hcomb := hsmul.symm.trans h1
    filter_upwards [hcomb] with y hy
    have hyeq : (i.fst.val)⁻¹ • ((eigenvectorChartPartialCLM (I := I) (M := M)
        g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y =
      (i.fst.val)⁻¹ • chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y := hy
    exact smul_right_injective ℝ (inv_ne_zero hμ) hyeq
  refine (h4.trans h2).trans ?_
  rw [h3]

/-- The `L²` class of the chart-Euclidean partial `euclidPartial k uₙ` of the
`n`-th approximant chart component equals the value of the canonical
chart-partial continuous linear map at the completion embedding of the `n`-th
smooth approximant. -/
private lemma euclidPartial_eigenvectorPouApprox_toLp_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ k n).toLp _ =
      eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)) := by
  refine Lp.ext ?_
  refine (MemLp.coeFn_toLp _).trans ?_
  exact (eigenvectorChartPartialCLM_smoothApprox_coeFn_eq (I := I) (M := M)
    g r s h_atlas i α P₀ k n).symm

/-- The `L²` classes of the chart-Euclidean partials `euclidPartial k uₙ` of the
`n`-th approximant chart components converge, as `n → ∞` and in
`Lp ℝ 2 (chartL2Measure α)`, to `μ` times the candidate weak `k`-th chart
partial `eigenvectorChartPartialLp g r s h_atlas i α P₀ k` of the eigenvector
chart component. -/
private lemma euclidPartial_eigenvectorPouApprox_toLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ k n).toLp _)
      atTop
      (𝓝 (i.fst.val •
        eigenvectorChartPartialLp (I := I) (M := M) g r s h_atlas i α P₀ k)) := by
  classical
  have hμ : i.fst.val ≠ 0 := i.fst.val_ne_zero
  -- `μ⁻¹ • eigenvectorChartPartialCLM(smoothToTensorH1Compl wₙ) → eigenvectorChartPartialLp`.
  have h_base := eigenvectorChartPartialLp_tendsto (I := I) (M := M)
    g r s h_atlas i α P₀ k
  -- Multiply by `μ`: `eigenvectorChartPartialCLM(smoothToTensorH1Compl wₙ) → μ • eigenvectorChartPartialLp`.
  have h_scaled := h_base.const_smul i.fst.val
  have h_eq : ∀ n : ℕ, i.fst.val • ((i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))) =
      (euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
        g r s h_atlas i α P₀ k n).toLp _ := by
    intro n
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul,
      euclidPartial_eigenvectorPouApprox_toLp_eq_clm (I := I) (M := M)
        g r s h_atlas i α P₀ k n]
  exact h_scaled.congr h_eq

/-! ## The principal integrand of the per-approximant chart bilinear form

The Euclidean chart component `uₙ := tensorComponentEuclid g r s Tₙ α P₀` is
supported, uniformly in `n`, inside the partition-of-unity kernel
`chartPouKernel α`. Choosing the source-free per-approximant chart bilinear
identity's compact set to be that kernel, the `principalIntegrand` of the
principal-part elliptic bilinear form `tensorPrincipalForm`, evaluated on `uₙ`
against `ψ`, agrees on the open chart target — by `weightedInvGram_principalIntegrand_eq`
on the kernel and by the vanishing of the chart-Euclidean partial of `uₙ` off
the kernel — with the `weightedInvGramOnEuclid`-contraction
`∑ᵢ∑ⱼ weightedInvGramOnEuclid g α i j · euclidPartial i uₙ · ∂ⱼψ`. -/

/-- On the open Euclidean chart target the `principalIntegrand` of the
principal-part elliptic bilinear form `tensorPrincipalForm g α (chartPouKernel
isCompact) (chartPouKernel subset)`, evaluated on the Euclidean chart component
`uₙ` of the `n`-th approximant against `ψ`, equals the
`weightedInvGramOnEuclid`-contraction of the chart-Euclidean partials. -/
private lemma principalIntegrand_eigenvectorPouApprox_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (n : ℕ) :
    Set.EqOn
      ((tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ)
      (fun y => ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α k l y *
            euclidPartial (E := E) k
              (tensorComponentEuclid (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
              y *
            euclidPartial (E := E) l ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
  · -- On the kernel the chart-bilinear-form coefficient is the weighted inverse
    -- Gram, so `principalIntegrand` is the density-weighted contraction.
    have hPI := weightedInvGram_principalIntegrand_eq (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ hyK
    rw [← hPI, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show weightedInvGramOnEuclid (I := I) g α k l y =
        densityOnEuclid (I := I) g α y *
          chartInvGramEuclid (I := I) g α k l y from by
      rw [← weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M)
        g α k l]; rfl]
    ring
  · -- Off the kernel the chart-Euclidean partial of `uₙ` vanishes, killing both
    -- sides.
    have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) k
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
          y = 0 := by
      intro k
      have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
      have hu_evt : (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
          =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
          (fun z hz => image_eq_zero_of_notMem_tsupport
            (fun h => hz (eigenvectorPouApprox_component_tsupport_subset
              (I := I) (M := M) g r s h_atlas i α P₀ n h)))
      rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
        fderiv_const_apply, ContinuousLinearMap.zero_apply]
    have hLHS_zero :
        (tensorPrincipalForm (I := I) (M := M) g α
            (chartPouKernel_isCompact (I := I) (M := M) α)
            (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
          ψ y = 0 := by
      rw [SmoothEllipticBilinearForm.principalIntegrand]
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      have hk := hu_partial_zero k
      rw [euclidPartial_def] at hk
      rw [hk]; ring
    have hRHS_zero :
        (fun y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (tensorComponentEuclid (I := I) (M := M) g r s
                  (eigenvectorPouApprox (I := I) (M := M)
                    g r s h_atlas i α n) α P₀)
                y *
              euclidPartial (E := E) l ψ y) y = 0 := by
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      rw [hu_partial_zero k]; ring
    rw [hLHS_zero, hRHS_zero]

/-! ## The principal-symbol test element

The `i`-th *principal-symbol test element* `principalSymbolTest g α ψ i` is the
inverse-Gram-weighted derivative combination `∑ⱼ weightedInvGramOnEuclid g α i j
· ∂ⱼψ`. It is the fixed `Lp ℝ 2 (chartL2Measure α)` element against which the
`L²`-classed chart-Euclidean partials of the approximant chart components are
paired in the principal part of the chart bilinear form: it is `C^∞` on the open
chart target (a finite combination of `C^∞` factors) and compactly supported, so
it is `MemLp 2` with respect to the chart-`L²` measure. -/

/-- The `i`-th principal-symbol test element `∑ⱼ weightedInvGramOnEuclid g α i j ·
∂ⱼψ`, a function `EuclN → ℝ`. -/
private def principalSymbolTest
    (g : SmoothRiemannianMetric I M) (α : M)
    (ψ : EuclN → ℝ) (i' : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => ∑ j : Fin (Module.finrank ℝ E),
    weightedInvGramOnEuclid (I := I) g α i' j y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)

/-- The `i`-th principal-symbol test element is `MemLp 2` with respect to the
chart-`L²` measure: a finite sum of products of the `C^∞` weighted inverse-Gram
entry `weightedInvGramOnEuclid g α i j` (`= weightedInvGramEuclid g α i j`, `C^∞`
on the chart target) with the chart-Euclidean partial `∂ⱼψ` of the
chart-supported smooth test function. -/
private lemma principalSymbolTest_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i' : Fin (Module.finrank ℝ E)) :
    MemLp (principalSymbolTest (I := I) (M := M) g α ψ i') 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  -- The chart-Euclidean partial of `ψ`, as a smooth compactly-supported
  -- function with topological support inside the chart target.
  have hdψ_cd : ∀ j : Fin (Module.finrank ℝ E),
      ContDiff ℝ ∞ (euclidPartial (E := E) j ψ) :=
    fun j => euclidPartial_contDiff (E := E) hψ j
  have hdψ_cs : ∀ j : Fin (Module.finrank ℝ E),
      HasCompactSupport (euclidPartial (E := E) j ψ) := by
    intro j
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (euclidPartial_zero_off_tsupport j hyψ)
  have hdψ_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (euclidPartial (E := E) j ψ) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro j
    refine (closure_minimal ?_ (isClosed_tsupport _)).trans hψ_supp
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_zero_off_tsupport j hz')
  -- The weighted inverse-Gram entry, `C^∞` on the chart target.
  have hgram : ∀ j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => weightedInvGramOnEuclid (I := I) g α i' j y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro j
    refine (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α i' j).congr ?_
    intro y _
    rw [weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M)
      g α i' j]
  -- `principalSymbolTest` agrees pointwise with the `euclidPartial`-form sum.
  have hpst_eq : principalSymbolTest (I := I) (M := M) g α ψ i' =
      fun y => ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j y *
          euclidPartial (E := E) j ψ y := by
    funext y
    simp only [principalSymbolTest]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [euclidPartial_def]
  rw [hpst_eq, chartL2Measure]
  have hsum_memLp : MemLp (fun y => ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j y *
          euclidPartial (E := E) j ψ y) 2 (volume : Measure EuclN) := by
    refine memLp_finset_sum (μ := (volume : Measure EuclN))
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun j _ => ?_)
    have hcd : ContDiff ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α i' j y *
        euclidPartial (E := E) j ψ y) :=
      contDiff_mul_chartTest (I := I) (M := M) α (hgram j) (hdψ_cd j) (hdψ_supp j)
    have hcs : HasCompactSupport (fun y => weightedInvGramOnEuclid (I := I) g α i' j y *
        euclidPartial (E := E) j ψ y) :=
      hasCompactSupport_mul_chartTest (E := E) (hdψ_cs j)
    exact hcd.continuous.memLp_of_hasCompactSupport hcs
  exact hsum_memLp.restrict _

/-! ## The chart bilinear form of an approximant as a sum of `L²` pairings

The source-free per-approximant chart bilinear identity
`tensorComponent_chartBilinIdentity_of_dirichlet`, instantiated at the
partition-of-unity kernel as the compact set, has left-hand side
`bilin (tensorComponentEuclid g r s Tₙ α P₀) ψ`. Unfolding `bilin` (zeroth-order
coefficient identically zero) and the chart-`principalIntegrand`-collapse
`principalIntegrand_eigenvectorPouApprox_eqOn` exhibits the chart bilinear form
as the integral over the chart target of the `weightedInvGramOnEuclid`
contraction of the chart-Euclidean partial of `uₙ` against `∂ⱼψ`; reorganising
the double sum, it is the finite sum, over chart directions `i`, of the chart-`L²`
pairing of the principal-symbol test element `principalSymbolTest g α ψ i`
against the chart-Euclidean partial `euclidPartial i uₙ`. -/

set_option linter.style.show false in
/-- The chart bilinear form `bilin (tensorComponentEuclid g r s Tₙ α P₀) ψ` of the
`n`-th partition-of-unity-weighted approximant equals the finite sum, over chart
directions `i`, of the chart-`L²` integral of the principal-symbol test element
`principalSymbolTest g α ψ i` against the chart-Euclidean partial of the
Euclidean chart component `uₙ` of the approximant. -/
private lemma bilin_eigenvectorPouApprox_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (_hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (tensorPrincipalForm (I := I) (M := M) g α
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
          euclidPartial (E := E) i'
            (tensorComponentEuclid (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
            y ∂(chartL2Measure (I := I) (M := M) α) := by
  classical
  set uₙ : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s
    (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀ with huₙ_def
  set Bform := tensorPrincipalForm (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) with hBform_def
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hcTE_open.measurableSet
  -- `principalIntegrand` is `C^∞` globally and compactly supported.
  have huₙ_cd : ContDiff ℝ ∞ uₙ :=
    eigenvectorPouApprox_component_contDiff (I := I) (M := M) g r s h_atlas i α P₀ n
  have hP_principal : ContDiff ℝ ∞ (Bform.principalIntegrand uₙ ψ) := by
    have huₙ_dpartial : ∀ a : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun x => (fderiv ℝ uₙ x) (EuclideanSpace.single a 1)) :=
      fun a => euclidPartial_contDiff (E := E) huₙ_cd a
    have hψ_dpartial : ∀ b : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single b 1)) :=
      fun b => euclidPartial_contDiff (E := E) hψ b
    have hbody : ContDiff ℝ ∞
        (fun x => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            Bform.a x a b *
              ((fderiv ℝ uₙ x) (EuclideanSpace.single a 1)) *
              ((fderiv ℝ ψ x) (EuclideanSpace.single b 1))) :=
      ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        ((Bform.smooth_a a b).mul (huₙ_dpartial a)).mul (hψ_dpartial b)))
    exact hbody
  have huₙ_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport uₙ → euclidPartial (E := E) k uₙ y = 0 :=
    fun k y hy => euclidPartial_zero_off_tsupport (E := E) k hy
  have huₙ_tsupport_compact : IsCompact (tsupport uₙ) :=
    IsCompact.of_isClosed_subset (chartPouKernel_isCompact (I := I) (M := M) α)
      (isClosed_tsupport _)
      (eigenvectorPouApprox_component_tsupport_subset (I := I) (M := M)
        g r s h_atlas i α P₀ n)
  have hcs_principal : HasCompactSupport (Bform.principalIntegrand uₙ ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      huₙ_tsupport_compact ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyu
    refine hy ?_
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    have hk := huₙ_partial_zero a y hyu
    rw [euclidPartial_def] at hk
    rw [hk]; ring
  -- `bilin uₙ ψ = ∫_volume principalIntegrand uₙ ψ` (zeroth-order coefficient = 0).
  have hbilin_eq : Bform.bilin uₙ ψ =
      ∫ y, Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) := by
    rw [SmoothEllipticBilinearForm.bilin, MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    show Bform.principalIntegrand uₙ ψ y + Bform.c y * uₙ y * ψ y =
      Bform.principalIntegrand uₙ ψ y
    rw [hBform_def, tensorPrincipalForm_c_apply (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) y]
    ring
  -- `principalIntegrand uₙ ψ` vanishes off the chart target.
  have hPI_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      Bform.principalIntegrand uₙ ψ y = 0 := by
    intro y hy
    have hyψ : y ∉ tsupport ψ := fun h => hy (hψ_supp h)
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    rw [show (fderiv ℝ ψ y) (EuclideanSpace.single b 1) =
        euclidPartial (E := E) b ψ y from (euclidPartial_def _ _ _).symm,
      euclidPartial_zero_off_tsupport (E := E) b hyψ]
    ring
  -- Convert the whole-space integral to a chart-target integral.
  have hPI_volume_to_target :
      ∫ y, Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hPI_zero).symm
  -- On the chart target, `principalIntegrand` is the `weightedInvGramOnEuclid`
  -- contraction.
  have hPI_target_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α k l y *
                euclidPartial (E := E) k uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setIntegral_congr_fun hcTE_meas ?_
    have := principalIntegrand_eigenvectorPouApprox_eqOn (I := I) (M := M)
      g r s h_atlas i α P₀ (ψ := ψ) n
    rw [hBform_def, huₙ_def]
    exact this
  -- Reorganise the double-sum integral as a sum of pairing integrals.
  have hreorg :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α k l y *
                euclidPartial (E := E) k uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
        ∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α) := by
    -- Each pairing integral, as a chart-target integral.
    have hcoeff : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      intro i'
      rw [chartL2Measure]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro y
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show (fderiv ℝ ψ y) (EuclideanSpace.single l 1) =
          euclidPartial (E := E) l ψ y from (euclidPartial_def _ _ _).symm]
      ring
    rw [show (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α)) =
        (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN))
        from funext hcoeff]
    -- The chart-Euclidean partial of `uₙ` is globally `C^∞`, has compact
    -- support, and is topologically supported inside the chart target.
    have huₙ_partial_cd : ∀ k : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (euclidPartial (E := E) k uₙ) :=
      fun k => euclidPartial_eigenvectorPouApprox_component_contDiff
        (I := I) (M := M) g r s h_atlas i α P₀ k n
    have huₙ_partial_cs : ∀ k : Fin (Module.finrank ℝ E),
        HasCompactSupport (euclidPartial (E := E) k uₙ) :=
      fun k => euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
        (I := I) (M := M) g r s h_atlas i α P₀ k n
    have huₙ_partial_supp : ∀ k : Fin (Module.finrank ℝ E),
        tsupport (euclidPartial (E := E) k uₙ) ⊆
          chartTargetEuclid (I := I) (M := M) α := by
      intro k
      refine (closure_minimal ?_
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed).trans
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hyK
      refine hy ?_
      have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
      have hu_evt : uₙ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
          (fun z hz => image_eq_zero_of_notMem_tsupport
            (fun h => hz ((eigenvectorPouApprox_component_tsupport_subset
              (I := I) (M := M) g r s h_atlas i α P₀ n) h)))
      rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
        fderiv_const_apply, ContinuousLinearMap.zero_apply]
    have hgram_cd : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α k l y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      refine (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).congr ?_
      intro y _
      rw [weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M) g α k l]
    have hdψ_cd : ∀ l : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (euclidPartial (E := E) l ψ) :=
      fun l => euclidPartial_contDiff (E := E) hψ l
    -- Each summand integrand: `C^∞` globally and compactly supported.
    have hsummand_cd : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) := by
      intro k l
      have h1 : ContDiff ℝ ∞ (fun y =>
          weightedInvGramOnEuclid (I := I) g α k l y *
            euclidPartial (E := E) k uₙ y) :=
        contDiff_mul_chartTest (I := I) (M := M) α (hgram_cd k l)
          (huₙ_partial_cd k) (huₙ_partial_supp k)
      exact h1.mul (hdψ_cd l)
    have hsummand_cs : ∀ k l : Fin (Module.finrank ℝ E),
        HasCompactSupport (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) := by
      intro k l
      refine HasCompactSupport.of_support_subset_isCompact
        (huₙ_partial_cs k) ?_
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hyu
      refine hy ?_
      rw [show euclidPartial (E := E) k uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport hyu]
      ring
    have hsummand_int : ∀ k l : Fin (Module.finrank ℝ E),
        Integrable (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) (volume : Measure EuclN) :=
      fun k l => (hsummand_cd k l).continuous.integrable_of_hasCompactSupport
        (hsummand_cs k l)
    -- Each `i'`-summand chart-target integral equals the whole-space one.
    have hsplit : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
          ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i' l y *
              euclidPartial (E := E) i' uₙ y *
              euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      intro i'
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [show euclidPartial (E := E) i' uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport
          (fun h => hy (huₙ_partial_supp i' h))]
      ring
    rw [show (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN)) =
        (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i' l y *
              euclidPartial (E := E) i' uₙ y *
              euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN))
        from funext hsplit]
    rw [← MeasureTheory.integral_finset_sum _
      (fun i' _ => MeasureTheory.integrable_finset_sum _
        (fun l _ => hsummand_int i' l))]
    -- The chart-target double-sum integral equals the whole-space one; the
    -- summation order is then exchanged.
    have hdouble_split :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k uₙ y *
                  euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
          ∫ y, (∑ i' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      rw [show euclidPartial (E := E) k uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport
          (fun h => hy (huₙ_partial_supp k h))]
      ring
    rw [hdouble_split]
  rw [hbilin_eq, hPI_volume_to_target, hPI_target_eq, hreorg]

/-! ## The `n → ∞` limit of the chart bilinear form of an approximant

Pairing the principal-symbol test element `principalSymbolTest g α ψ i` — a fixed
chart-`L²` element — against the `L²`-classed chart-Euclidean partial
`euclidPartial i uₙ` and summing over chart directions exhibits the per-approximant
chart bilinear form as a finite sum of `L²` pairings. As `n → ∞`, the `L²` classes
of the chart-Euclidean partials converge to `μ` times the candidate weak chart
partials of the eigenvector chart component
(`euclidPartial_eigenvectorPouApprox_toLp_tendsto`); pairing convergence and the
finite sum give the `n → ∞` limit of the chart bilinear form. -/

set_option linter.style.show false in
/-- **The `n → ∞` limit of the chart bilinear form of an approximant.** The chart
bilinear forms `bilin (tensorComponentEuclid g r s Tₙ α P₀) ψ` of the
partition-of-unity-weighted approximants converge, as `n → ∞`, to `μ` times the
density-weighted principal pairing `∫ y in chartTargetEuclid α, ∑ i' ∑ j',
weightedInvGramOnEuclid g α i' j' y · eigenvectorChartWeakPartial g r s h_atlas
i α P₀ i' y · (fderiv ℝ ψ y) (EuclideanSpace.single j' 1)` of the eigenvector
chart component's weak partials. -/
private lemma bilin_eigenvectorPouApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ)
      atTop
      (𝓝 (i.fst.val *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ∂(volume : Measure EuclN))) := by
  classical
  -- The fixed principal-symbol test elements, as chart-`L²` classes.
  set mtest : Fin (Module.finrank ℝ E) → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun i' => (principalSymbolTest_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp i').toLp _
    with hmtest_def
  -- Per chart direction `i'`: the pairing integral converges.
  have h_dir : ∀ i' : Fin (Module.finrank ℝ E),
      Filter.Tendsto
        (fun n => ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
            g r s h_atlas i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s h_atlas i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))) := by
    intro i'
    exact tendsto_lp_inner_integral (μ := chartL2Measure (I := I) (M := M) α)
      (mtest i')
      (euclidPartial_eigenvectorPouApprox_toLp_tendsto (I := I) (M := M)
        g r s h_atlas i α P₀ i')
  -- The per-`n` pairing integral equals the chart-`L²` integral.
  have h_int_n : ∀ (i' : Fin (Module.finrank ℝ E)) (n : ℕ),
      ∫ y, (mtest i' : EuclN → ℝ) y *
        ((euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
          g r s h_atlas i α P₀ i' n).toLp _ : EuclN → ℝ) y
        ∂(chartL2Measure (I := I) (M := M) α) =
      ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
        euclidPartial (E := E) i'
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
          y ∂(chartL2Measure (I := I) (M := M) α) := by
    intro i' n
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [(by rw [hmtest_def]; exact MemLp.coeFn_toLp _ :
        (mtest i' : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α]
          principalSymbolTest (I := I) (M := M) g α ψ i'),
      MemLp.coeFn_toLp (euclidPartial_eigenvectorPouApprox_component_memLp
        (I := I) (M := M) g r s h_atlas i α P₀ i' n)] with y hy_m hy_g
    rw [hy_m, hy_g]
  -- The per-`n` chart bilinear form is the finite sum of pairing integrals.
  have h_bilin_n : ∀ n : ℕ,
      (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
            g r s h_atlas i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) := by
    intro n
    rw [bilin_eigenvectorPouApprox_eq_sum (I := I) (M := M)
      g r s h_atlas i α P₀ hψ hψ_cs hψ_supp n]
    exact Finset.sum_congr rfl (fun i' _ => (h_int_n i' n).symm)
  -- The limit: the finite sum of the per-direction limits.
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (mtest i' : EuclN → ℝ) y *
            ((euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
              g r s h_atlas i α P₀ i' n).toLp _ : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (mtest i' : EuclN → ℝ) y *
            ((i.fst.val •
              eigenvectorChartPartialLp (I := I) (M := M)
                g r s h_atlas i α P₀ i' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))) :=
    tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i' _ => h_dir i')
  -- The limit equals `μ` times the density-weighted principal pairing.
  have h_limit_eq :
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s h_atlas i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
      i.fst.val *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ∂(volume : Measure EuclN) := by
    -- Each summand: rewrite the pairing integral, pulling out the scalar `μ`.
    have h_summand : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s h_atlas i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        i.fst.val *
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
            ∂(volume : Measure EuclN) := by
      intro i'
      have h_m_ae : (mtest i' : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          principalSymbolTest (I := I) (M := M) g α ψ i' := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      have h_g_ae : ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s h_atlas i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => i.fst.val •
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i α P₀ i' y :=
        Lp.coeFn_smul i.fst.val
          (eigenvectorChartPartialLp (I := I) (M := M) g r s h_atlas i α P₀ i')
      have h_ae_prod :
          (fun y => (mtest i' : EuclN → ℝ) y *
            ((i.fst.val •
              eigenvectorChartPartialLp (I := I) (M := M)
                g r s h_atlas i α P₀ i' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => i.fst.val *
            (principalSymbolTest (I := I) (M := M) g α ψ i' y *
              eigenvectorChartWeakPartial (I := I) (M := M)
                g r s h_atlas i α P₀ i' y) := by
        filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
        rw [hy_m, hy_g, smul_eq_mul]; ring
      rw [integral_congr_ae h_ae_prod, MeasureTheory.integral_const_mul]
      congr 1
      -- `∫ … ∂(chartL2Measure α) = ∫ … in chartTargetEuclid α ∂volume`.
      show ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ i' y)
          ∂((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) = _
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i' _ => h_summand i'), ← Finset.mul_sum]
    congr 1
    -- Each `i'`-th inner-sum integrand, restricted to the chart target, is the
    -- product of two chart-`L²` functions — the chart-`L²` weak partial and the
    -- principal-symbol test element — hence integrable.
    have h_inner_integrable : ∀ i' : Fin (Module.finrank ℝ E),
        Integrable (fun y => ∑ j' : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i' j' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i α P₀ i' y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro i'
      -- The chart-`L²` weak partial is `MemLp 2`.
      have hwp_memLp : MemLp (eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P₀ i') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        have h : MemLp (fun y => ((eigenvectorChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
            (chartL2Measure (I := I) (M := M) α) :=
          Lp.memLp _
        exact h
      -- The principal-symbol test element is `MemLp 2`.
      have hpst_memLp : MemLp (principalSymbolTest (I := I) (M := M) g α ψ i') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        exact principalSymbolTest_memLp (I := I) (M := M) g α hψ hψ_cs
          hψ_supp i'
      -- Their product is `MemLp 1`, hence integrable.
      have hprod : MemLp (fun y => principalSymbolTest (I := I) (M := M) g α ψ i' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ i' y) 1
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        hwp_memLp.mul hpst_memLp
      have hprod_int : Integrable (fun y =>
          principalSymbolTest (I := I) (M := M) g α ψ i' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i α P₀ i' y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        (memLp_one_iff_integrable).mp hprod
      refine hprod_int.congr ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      ring
    rw [← MeasureTheory.integral_finset_sum _
      (fun i' _ => h_inner_integrable i')]
  rw [show (fun n => (tensorPrincipalForm (I := I) (M := M) g α
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀) ψ) =
      (fun n => ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
            g r s h_atlas i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
      from funext h_bilin_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

/-! ## The inverse-Gram-rotated chart test section attached to `ψ`

For a chart-supported smooth Euclidean test function `ψ`, the inverse-Gram-rotated
test section `eigenvectorRotatedTestSection g r s α P₀ ψ` is the rotated test
section of the manifold-side chart pullback `chartTestPullback I α ψ`. It is the
fixed smooth `(r, s)`-tensor section against which the per-approximant chart
bilinear identity's source-term Dirichlet pairing is taken. -/

/-- The inverse-Gram-rotated chart test section
`rotatedTestSection g r s α P₀ (chartTestPullback I α ψ)` attached to a
chart-supported smooth Euclidean test function `ψ`. -/
private def eigenvectorRotatedTestSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothCcTensor g r s :=
  rotatedTestSection (I := I) (M := M) g r s α P₀
    (chartTestPullback (I := I) (M := M) α ψ)
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)

/-- On the Euclidean chart target the chart `P`-component of the inverse-Gram-rotated
test section attached to `ψ` equals the inverse-Gram entry
`covChartMetricGramInv g r s α y P P₀` times `ψ`. -/
private lemma tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P : TensorCompIdx (E := E) r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) α P)
      (fun y => covChartMetricGramInv (I := I) (M := M) g r s α y P P₀ * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [eigenvectorRotatedTestSection,
    tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s _ α P hy,
    rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀
      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
      (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
      P hy,
    chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]

/-- The inverse-Gram-rotated chart test section attached to `ψ` has its underlying
tensor field supported inside the chart-`α` source: each summand of its
finite-sum definition is a chart-basis tensor section cut off by a bump
supported in the chart source. -/
private lemma eigenvectorRotatedTestSection_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
        hψ hψ_cs hψ_supp).toFun ⊆ (chartAt H α).source := by
  classical
  refine (closure_minimal ?_
    (isClosed_tsupport (chartTestPullback (I := I) (M := M) α ψ))).trans
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
  intro b hb
  rw [Function.mem_support] at hb
  by_contra hb_notin
  -- The underlying field of `rotatedTestSection` is the finite sum, over `Q`, of
  -- the underlying fields of the chart-basis tensor sections; each summand
  -- vanishes off the chart source.
  refine hb ?_
  rw [eigenvectorRotatedTestSection, rotatedTestSection]
  rw [show (∑ Q : CompIdx E r s,
        chartBasisTensorSection (I := I) (M := M) g r s α
          (fun c : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q c *
            chartTestPullback (I := I) (M := M) α ψ c)
          (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ))
          (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp))
          Q).toFun b =
      ∑ Q : CompIdx E r s,
        (chartBasisTensorSection (I := I) (M := M) g r s α
          (fun c : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q c *
            chartTestPullback (I := I) (M := M) α ψ c)
          (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ))
          (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp))
          Q).toFun b
      from by
        induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
        | empty => simp [SmoothCcTensor.toFun_apply, SmoothCcTensor.toSection_zero]
        | insert Q t hQ ih =>
            rw [Finset.sum_insert hQ, Finset.sum_insert hQ,
              SmoothCcTensor.toFun_add, Pi.add_apply, ih]]
  refine Finset.sum_eq_zero (fun Q _ => ?_)
  -- The `Q`-summand vanishes at `b`: the cut-off bump factor `χ b` vanishes
  -- off the closed support of the chart pullback `χ`.
  rw [SmoothCcTensor.toFun_apply, chartBasisTensorSection_toSection_apply,
    image_eq_zero_of_notMem_tsupport hb_notin, mul_zero, zero_smul,
    Tensor0SBundle.TensorRSSpace.toModel_zero]

/-! ## The `n → ∞` limit of the main-Dirichlet term

The main-Dirichlet term `mainDir(n) := ∫ tensorCovDerivPointwiseInner g r s wₙ
(pouSmul g r s α vRot)` is the genuine-gradient term of the covariant-Leibniz
split of the per-approximant source-term Dirichlet pairing, with `vRot` the
inverse-Gram-rotated chart test section attached to `ψ`. By `mainDir_tendsto` it
converges to `(1 − μ) · ⟪(pouSmul g r s α vRot : TensorL2), eigenvector⟫`; the
chart-pull `tensorL2Inner_pouSmul_tensorL2ChartComponent_pull`, the chart-component
identification `tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn`, and the
Gram / inverse-Gram collapse `covChartMetricGram_mul_inv_collapse` rewrite the
inner product as the density-weighted integral of `u_chart · ψ`. -/

/-- **The `n → ∞` limit of the main-Dirichlet term.** The main-Dirichlet pairings
`∫ tensorCovDerivPointwiseInner g r s wₙ (pouSmul g r s α vRot)` converge, as
`n → ∞`, to `(1 − μ)` times the density-weighted integral
`∫ y in chartTargetEuclid α, densityOnEuclid g α y · u_chart y · ψ y`, where
`u_chart` is the eigenvector chart `P₀`-component. -/
private lemma eigenvectorMainDir_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp)) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 ((1 - i.fst.val) *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(volume : Measure EuclN))) := by
  classical
  set vRot : SmoothCcTensor g r s :=
    eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp
    with hvRot_def
  -- The main-Dirichlet limit, in `L²`-pairing closed form.
  have h_md := mainDir_tendsto (I := I) (M := M) g r s h_atlas i
    (pouSmul (I := I) (M := M) g r s α vRot)
  -- The `L²` pairing as a chart-Euclidean integral.
  have h_pull :
      ⟪((pouSmul (I := I) (M := M) g r s α vRot : SmoothCcTensor g r s) :
          TensorL2 r s g),
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                  α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) :=
    tensorL2Inner_pouSmul_tensorL2ChartComponent_pull (I := I) (M := M)
      g r s α (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) vRot
      (eigenvectorRotatedTestSection_tsupport_subset (I := I) (M := M)
        g r s α P₀ hψ hψ_cs hψ_supp)
  -- The chart-Euclidean integrand collapses to `densityOnEuclid · u_chart · ψ`.
  have h_collapse :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
                ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                    α Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y hy => ?_)
    -- On the chart target, the rotated-test chart component is the inverse-Gram
    -- entry times `ψ`.
    have hcomp : ∀ P : CompIdx E r s,
        tensorComponentEuclid (I := I) (M := M) g r s vRot α P y =
          covChartMetricGramInv (I := I) (M := M) g r s α y P P₀ * ψ y :=
      fun P => tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn
        (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp P hy
    rw [show (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
        from ?_]
    · ring
    -- The double-sum collapse.
    rw [Finset.sum_comm]
    have hstep : ∀ Q : CompIdx E r s,
        (∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
          (if Q = P₀ then (1 : ℝ) else 0) *
            (((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ψ y) := by
      intro Q
      rw [show (∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                  α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
          (∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α Q P y *
              covChartMetricGramInv (I := I) (M := M) g r s α y P P₀) *
            (((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ψ y)
        from by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun P _ => ?_)
          rw [hcomp P, covChartMetricGram_symm (I := I) (M := M) g r s α P Q y]
          ring]
      rw [covChartMetricGram_mul_inv_collapse (I := I) (M := M) g r s α hy Q P₀]
    rw [Finset.sum_congr rfl (fun Q _ => hstep Q),
      Finset.sum_eq_single P₀]
    · rw [if_pos rfl, one_mul]
    · intro Q _ hQ
      rw [if_neg hQ, zero_mul]
    · intro hP₀
      exact absurd (Finset.mem_univ P₀) hP₀
  -- Assemble.
  have h_eq : (1 - i.fst.val) *
        ⟪((pouSmul (I := I) (M := M) g r s α vRot : SmoothCcTensor g r s) :
            TensorL2 r s g),
          tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ =
      (1 - i.fst.val) *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(volume : Measure EuclN) := by
    rw [h_pull, h_collapse]
  rw [← h_eq]
  exact h_md

/-! ## A general `C^∞`-coefficient test element

The cross-Leibniz chart-pull limits pair the convergent cutoff chart components
against a fixed test element of the form `densityOnEuclid g α · c · ψ`, with `c`
a `C^∞`-on-the-chart-target coefficient. The next lemma packages, once, that such
a product is `MemLp 2` with respect to the chart-`L²` measure. -/

/-- The product `densityOnEuclid g α · c · ψ` of the chart density, a coefficient
`c` that is `C^∞` on the open chart target, and a chart-supported smooth test
function `ψ` is `MemLp 2` with respect to the chart-`L²` measure. -/
private lemma density_coeff_test_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      ((densityOnEuclid_contDiffOn (I := I) g α).mul hc) hψ hψ_supp
  have hcs : HasCompactSupport
      (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyψ, mul_zero])
  rw [chartL2Measure]
  exact (hcd.continuous.memLp_of_hasCompactSupport hcs).restrict _

/-! ## Integrability of the cross-left chart-pull and limit summands

Each `(P, Q)`-summand of the chart-Euclidean cross-left integral pairs a fixed
`C^∞`-coefficient test element against a chart-`L²` cutoff chart component, both
`MemLp 2` with respect to the chart-`L²` measure. Their product is `MemLp 1`,
hence integrable; the chart-pull and limit summands agree almost everywhere with
that product. -/

/-- The `(P, Q)`-summand of the chart-Euclidean cross-left integral at the `n`-th
approximant is integrable with respect to the chart-pulled volume restricted to
the chart target. -/
private lemma crossLeftPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r (s + 1))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2 (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
            α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
          tensorComponentEuclid (I := I) (M := M) g r (s + 1)
            (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α ψ)
                (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                  hψ_cs hψ_supp)))
            α Q y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The fixed `C^∞`-coefficient test element and the cutoff chart component are
  -- both `MemLp 2` of the chart-`L²` measure; their product is `MemLp 1`.
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp
    exact h
  have hcut_memLp : MemLp (fun y =>
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h : MemLp (fun y =>
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2 (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
          α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) :=
      Lp.memLp _
    exact h
  have hprod : MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hcut_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  -- On the chart target the rotated-test cross-left chart component is the
  -- test-independent `C^∞` cross-left coefficient times `ψ`.
  refine (MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr
    (Filter.Eventually.of_forall (fun y hy => ?_))
  simp only []
  rw [tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
    (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp Q hy]
  ring

/-- The `(P, Q)`-summand of the limiting chart-Euclidean cross-left integral is
integrable with respect to the chart-pulled volume restricted to the chart
target. -/
private lemma crossLeftLimitPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r (s + 1))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp
    exact h
  have hlim_memLp : MemLp (fun y =>
      ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h : MemLp (fun y =>
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) :=
      Lp.memLp _
    exact h
  have hprod : MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hlim_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

/-- The `(P, Q)`-summand of the chart-Euclidean cross-left integral at the `n`-th
approximant: the chart density times the chart-frame Gram, the cutoff chart
component of `tensorCovGradL2 wₙ`, and the rotated-test cross-left chart
component. -/
private noncomputable def crossLeftChartPullSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P Q : TensorCompIdx (E := E) r (s + 1)) (n : ℕ) : EuclN → ℝ :=
  fun y => densityOnEuclid (I := I) g α y *
    (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
      tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp)))
        α Q y)

/-! ## The `n → ∞` limit of the cross-left integral

The cross-left integral `∫crossLeft(n) := ∫ tensorCovDerivCrossLeft g r s ζ_α wₙ
vRot`, chart-pulled by `tensorCovDerivCrossLeft_integral_eq_chartPull` and
test-decoupled by `tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn`,
is the chart-Euclidean integral coupling the cutoff chart components
`tensorL2ChartComponentCutoff g r (s + 1) (tensorCovGradL2 wₙ)` to the
test-independent `C^∞` cross-left coefficient `crossLeftTestCoeff`. As `n → ∞`
the cutoff chart components converge in `Lp ℝ 2 (chartL2Measure α)` to
`crossLeftLimitComponent` (`crossLeftComponent_tendsto`); pairing convergence and
the finite double sum give the `n → ∞` limit. -/

/-- **The `n → ∞` limit of the cross-left integral.** The cross-left integrals
`∫ tensorCovDerivCrossLeft g r s (chartAtlasPOU I M α) wₙ vRot` converge, as
`n → ∞`, to `∫ y in chartTargetEuclid α, densityOnEuclid g α y · (∑ P ∑ Q,
covChartMetricGram g r (s + 1) α P Q y · crossLeftTestCoeff g r s α P₀ Q y ·
crossLeftLimitComponent g r s h_atlas i α P y) · ψ y`. -/
private lemma eigenvectorCrossLeft_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_supp) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN))) := by
  classical
  -- The fixed `(P, Q)`-test elements, as chart-`L²` classes.
  set mtest : TensorCompIdx (E := E) r (s + 1) → TensorCompIdx (E := E) r (s + 1) →
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun P Q => (density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp).toLp _ with hmtest_def
  -- Per `(P, Q)`: the pairing integral converges.
  have h_dir : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      Filter.Tendsto
        (fun n => ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2 (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
            α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))) :=
    fun P Q => tendsto_lp_inner_integral
      (μ := chartL2Measure (I := I) (M := M) α) (mtest P Q)
      (crossLeftComponent_tendsto (I := I) (M := M) g r s h_atlas i α P)
  -- The sum of the per-`(P, Q)` limits.
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2 (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n))
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartL2Measure (I := I) (M := M) α))) :=
    tendsto_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => tendsto_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_dir P Q))
  -- The per-`n` cross-left integral is the finite double sum of pairing
  -- integrals.
  have h_cross_n : ∀ n : ℕ,
      ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_supp) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n))
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α) := by
    intro n
    -- The chart-pull of the cross-left integral.
    rw [eigenvectorRotatedTestSection,
      tensorCovDerivCrossLeft_integral_eq_chartPull (I := I) (M := M) g r s α
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)
        (rotatedTestSection (I := I) (M := M) g r s α P₀
          (chartTestPullback (I := I) (M := M) α ψ)
          (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
          (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
            hψ_cs hψ_supp))]
    -- The chart-pull integral as the finite double sum of `(P, Q)`-pairing
    -- integrals: distribute the chart density, split the finite sums, and
    -- identify each summand with the chart-`L²` pairing.
    have hpair : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n))
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_supp)))
                  α Q y)
            ∂(volume : Measure EuclN) =
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n))
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine (MeasureTheory.integral_congr_ae ?_).symm
      filter_upwards [h_m_ae,
        (MeasureTheory.ae_restrict_iff'
          (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr
          (Filter.Eventually.of_forall (fun y hy =>
            tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
              (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp Q hy))]
        with y hy_m hy_decouple
      rw [hy_m, hy_decouple]
      ring
    -- The chart-pull integrand distributes into the finite double sum, which
    -- the integral then splits over.
    rw [show (fun y => densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n))
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_supp)))
                  α Q y)) =
        fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n))
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_supp)))
                  α Q y)
        from funext (fun y => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun P _ => Finset.mul_sum _ _ _))]
    rw [MeasureTheory.integral_finset_sum _ (fun P _ =>
        MeasureTheory.integrable_finset_sum _ (fun Q _ =>
          crossLeftPairing_integrable (I := I) (M := M) g r s h_atlas i
            α P₀ P Q hψ hψ_cs hψ_supp n))]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [MeasureTheory.integral_finset_sum _ (fun Q _ =>
        crossLeftPairing_integrable (I := I) (M := M) g r s h_atlas i
          α P₀ P Q hψ hψ_cs hψ_supp n)]
    exact Finset.sum_congr rfl (fun Q _ => hpair P Q)
  -- The limit equals the chart-target density-weighted double-sum integral.
  have h_limit_eq :
      ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r (s + 1),
              ∑ Q : TensorCompIdx (E := E) r (s + 1),
                covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                    crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((crossLeftLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN) := by
    -- Each summand pairing integral, rewritten as a chart-target integral.
    have h_summand : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
        ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
      (fun Q _ => h_summand P Q))]
    -- Pull the inner sum into the integral.
    rw [Finset.sum_congr rfl (fun P _ =>
      (MeasureTheory.integral_finset_sum _ (fun Q _ =>
        crossLeftLimitPairing_integrable (I := I) (M := M)
          g r s h_atlas i α P₀ P Q hψ hψ_cs hψ_supp)).symm)]
    -- Pull the outer sum into the integral.
    rw [← MeasureTheory.integral_finset_sum _ (fun P _ =>
      MeasureTheory.integrable_finset_sum _ (fun Q _ =>
        crossLeftLimitPairing_integrable (I := I) (M := M)
          g r s h_atlas i α P₀ P Q hψ hψ_cs hψ_supp))]
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [show (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n))
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))
      from funext h_cross_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

/-! ## Integrability of the cross-right value chart-pull and limit summands

The cross-right test-decoupling splits the chart-Euclidean cross-right integrand
into a *value* part — carrying the cross-right test-decoupling **value**
coefficient `crossRightTestValueCoeff` against the test function `ψ` — and a
*gradient* part carrying `crossRightTestGradCoeff` against the chart-Euclidean
partials of `ψ`. This subsection assembles the integrability of the `(P, Q)`
summands of the *value* part; the gradient part is handled separately via the
committed integration-by-parts rewrite.

Each `(P, Q)`-summand of the chart-Euclidean cross-right *value* integral pairs a
fixed `C^∞`-coefficient test element against a chart-`L²` cutoff chart
component, both `MemLp 2` with respect to the chart-`L²` measure. Their product
is `MemLp 1`, hence integrable. -/

/-- The `(P, Q)`-summand of the chart-Euclidean cross-right value integral at the
`n`-th approximant is integrable with respect to the chart-pulled volume
restricted to the chart target. -/
private lemma crossRightValuePairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp
    exact h
  have hcut_memLp : MemLp (fun y =>
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h : MemLp (fun y =>
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
          α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) :=
      Lp.memLp _
    exact h
  have hprod : MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hcut_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

/-- The `(P, Q)`-summand of the limiting chart-Euclidean cross-right value
integral is integrable with respect to the chart-pulled volume restricted to the
chart target. -/
private lemma crossRightValueLimitPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp
    exact h
  have hlim_memLp : MemLp (fun y =>
      ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h : MemLp (fun y =>
        ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) :=
      Lp.memLp _
    exact h
  have hprod : MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hlim_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

/-! ## The `n → ∞` limit of the cross-right value integral

The *value* part of the chart-Euclidean cross-right integral — the
`crossRightTestValueCoeff`-carrying part, coupling the cutoff chart components
`tensorL2ChartComponentCutoff g r s ((wₙ).toCcTensor : TensorL2)` to the
test-independent `C^∞` value coefficient `crossRightTestValueCoeff` against `ψ`.
As `n → ∞` the cutoff chart components converge in `Lp ℝ 2 (chartL2Measure α)`
to `crossRightLimitComponent` (`crossRightComponent_tendsto`); pairing
convergence and the finite double sum give the `n → ∞` limit. -/

/-- **The `n → ∞` limit of the cross-right value integral.** The cross-right
value integrals — the `crossRightTestValueCoeff`-carrying part of the
chart-pulled, test-decoupled cross-right term — converge, as `n → ∞`, to
`∫ y in chartTargetEuclid α, densityOnEuclid g α y · (∑ P ∑ Q,
covChartMetricGram g r s α P Q y · crossRightTestValueCoeff g r s α P₀ Q y ·
crossRightLimitComponent g r s h_atlas i α P y) · ψ y`. -/
private lemma eigenvectorCrossRight_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN))) := by
  classical
  -- The fixed `(P, Q)`-test elements, as chart-`L²` classes.
  set mtest : TensorCompIdx (E := E) r s → TensorCompIdx (E := E) r s →
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun P Q => (density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_supp).toLp _ with hmtest_def
  -- Per `(P, Q)`: the pairing integral converges.
  have h_dir : ∀ (P Q : TensorCompIdx (E := E) r s),
      Filter.Tendsto
        (fun n => ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossRightLimitComponent (I := I) (M := M) g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))) :=
    fun P Q => tendsto_lp_inner_integral
      (μ := chartL2Measure (I := I) (M := M) α) (mtest P Q)
      (crossRightComponent_tendsto (I := I) (M := M) g r s h_atlas i α P)
  -- The sum of the per-`(P, Q)` limits.
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartL2Measure (I := I) (M := M) α))) :=
    tendsto_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => tendsto_finset_sum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_dir P Q))
  -- The per-`n` value integral is the finite double sum of pairing integrals.
  have h_value_n : ∀ n : ℕ,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                    (((eigenvectorSmoothApprox (I := I) (M := M)
                        g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                    α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN) =
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartL2Measure (I := I) (M := M) α) := by
    intro n
    -- Each summand pairing integral, as a chart-target integral.
    have hpair : ∀ (P Q : TensorCompIdx (E := E) r s),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
              ψ y ∂(volume : Measure EuclN) =
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine (MeasureTheory.integral_congr_ae ?_).symm
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [show (fun y => densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) *
            ψ y) =
        fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) *
              ψ y
        from funext (fun y => by
          simp only [Finset.sum_mul, Finset.mul_sum])]
    rw [MeasureTheory.integral_finset_sum _ (fun P _ =>
        MeasureTheory.integrable_finset_sum _ (fun Q _ =>
          crossRightValuePairing_integrable (I := I) (M := M) g r s h_atlas i
            α P₀ P Q hψ hψ_cs hψ_supp n))]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [MeasureTheory.integral_finset_sum _ (fun Q _ =>
        crossRightValuePairing_integrable (I := I) (M := M) g r s h_atlas i
          α P₀ P Q hψ hψ_cs hψ_supp n)]
    exact Finset.sum_congr rfl (fun Q _ => hpair P Q)
  -- The limit equals the chart-target density-weighted double-sum integral.
  have h_limit_eq :
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((crossRightLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN) := by
    -- Each summand pairing integral, rewritten as a chart-target integral.
    have h_summand : ∀ (P Q : TensorCompIdx (E := E) r s),
        ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
      (fun Q _ => h_summand P Q))]
    -- Pull the inner sum into the integral.
    rw [Finset.sum_congr rfl (fun P _ =>
      (MeasureTheory.integral_finset_sum _ (fun Q _ =>
        crossRightValueLimitPairing_integrable (I := I) (M := M)
          g r s h_atlas i α P₀ P Q hψ hψ_cs hψ_supp)).symm)]
    -- Pull the outer sum into the integral.
    rw [← MeasureTheory.integral_finset_sum _ (fun P _ =>
      MeasureTheory.integrable_finset_sum _ (fun Q _ =>
        crossRightValueLimitPairing_integrable (I := I) (M := M)
          g r s h_atlas i α P₀ P Q hψ hψ_cs hψ_supp))]
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [show (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN)) =
      (fun n => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))
      from funext h_value_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

/-! ## The `n → ∞` limit of the cross-right gradient `∂ψ`-part

The *gradient* part of the chart-Euclidean cross-right integral — the
`crossRightTestGradCoeff`-carrying part, coupling the cross-right gradient-term
coefficient `crossRightTestGradTerm` to the chart-Euclidean partials `∂_l ψ`.
The committed per-`n` integration-by-parts rewrite `crossRightTestGradTerm_byParts`
folds the `∂_l ψ`-carrying part into the single `ψ`-term carrying the
chart-Euclidean divergence `∑_l ∂_l (densityOnEuclid g α · crossRightTestGradTerm)`;
the committed `L²`-convergence `crossRightGradCoeffDivSum_tendsto` of that
divergence, paired against the fixed test element `ψ`, gives the `n → ∞`
limit. -/

/-- **The `n → ∞` limit of the cross-right gradient `∂ψ`-part.** The cross-right
gradient `∂ψ`-parts `∑_l ∫ densityOnEuclid g α · crossRightTestGradTerm g r s
(eigenvectorSmoothApprox … n).toCcTensor α P₀ l · euclidPartial l ψ` converge, as
`n → ∞`, to `−∫ y in chartTargetEuclid α, crossRightGradCoeffDivLimit g r s
h_atlas i α P₀ y · ψ y`.

The per-`n` term is rewritten by the integration-by-parts identity
`crossRightTestGradTerm_byParts` to the negative of the single `ψ`-term carrying
the chart-Euclidean divergence; the `Lp`-convergence
`crossRightGradCoeffDivSum_tendsto` of that divergence, paired against the fixed
`Lp` element `ψ` (`tendsto_lp_inner_integral`), gives the limit. -/
private lemma eigenvectorCrossRightGrad_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (-∫ y in chartTargetEuclid (I := I) (M := M) α,
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set m : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    (test_memLp (I := I) (M := M) α hψ hψ_cs).toLp _ with hm_def
  set gseq : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) := fun n =>
    (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
      g r s h_atlas i α P₀ n).toLp _ with hgseq_def
  set glim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s h_atlas i α P₀).toLp _ with hglim_def
  -- The `n`-th pre-IBP term equals the negative of the `Lp`-pairing of `ψ`
  -- against the chart-Euclidean divergence `gseq n`.
  have h_int_n : ∀ n : ℕ,
      ∑ l : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor α P₀ l y *
              euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN) =
        -(∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α)) := by
    intro n
    -- Integrate by parts: the `∂ψ`-part folds into the divergence `ψ`-term.
    rw [crossRightTestGradTerm_byParts (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
      α P₀ hψ hψ_cs hψ_supp]
    congr 1
    -- The chart-Euclidean divergence `ψ`-integral is the `Lp`-pairing of `ψ`
    -- against `gseq n`.
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α] ψ := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (fun z => densityOnEuclid (I := I) g α z *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor α P₀ l z) y := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod :
        (fun y => (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor α P₀ l z) y) * ψ y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    exact MeasureTheory.integral_congr_ae h_ae_prod
  -- The limiting term as the `Lp`-pairing of `ψ` against `glim`.
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α] ψ := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        crossRightGradCoeffDivLimit (I := I) (M := M) g r s h_atlas i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    exact MeasureTheory.integral_congr_ae h_ae_prod
  -- The `Lp`-convergence of the chart-Euclidean divergence.
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact crossRightGradCoeffDivSum_tendsto (I := I) (M := M)
      g r s h_atlas i α P₀
  have h_main := tendsto_lp_inner_integral
    (μ := chartL2Measure (I := I) (M := M) α) m h_tendsto_lp
  rw [h_int_lim] at h_main
  -- The `n → ∞` limit: negate the convergent `Lp`-pairing sequence.
  have h_neg := h_main.neg
  refine h_neg.congr ?_
  intro n
  exact (h_int_n n).symm

/-! ## The source-term covariant-Leibniz split of an approximant

The partition-of-unity-weighted approximant `Tₙ := eigenvectorPouApprox g r s
h_atlas i α n` is the chart-atlas-partition-of-unity scalar product `pouSmul g r
s α (wₙ).toCcTensor`, which is the smooth-scalar product `scalarSmul g r s
(chartAtlasPOU I M α) (wₙ).toCcTensor`. The covariant-Leibniz rule
`tensorCovDerivPointwiseInner_scalarSmul_left` therefore splits the
source-term Dirichlet integrand of the per-approximant chart bilinear identity,
evaluated at `Tₙ`, into the genuine-gradient main-Dirichlet integrand of `wₙ`
against the smooth-scalar-weighted rotated test section, corrected by the two
explicit cross terms. -/

/-- The chart-atlas-partition-of-unity scalar product `pouSmul g r s α S` is the
smooth-scalar product `scalarSmul g r s (chartAtlasPOU I M α) S`: both are the
pointwise scalar product of the chart-atlas partition-of-unity weight and `S`. -/
private lemma pouSmul_eq_scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    pouSmul (I := I) (M := M) g r s α S =
      scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) S := rfl

/-- **The source-term covariant-Leibniz split of an approximant.** The
source-term Dirichlet integral of the per-approximant chart bilinear identity,
evaluated at the partition-of-unity-weighted approximant `Tₙ`, splits into the
main-Dirichlet integral of `wₙ` against the partition-of-unity-weighted rotated
test section, minus the cross-left integral, plus the cross-right integral. -/
private lemma eigenvectorSource_integral_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_supp)) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
    (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
    (∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    with hwₙ_def
  set vRot : SmoothCcTensor g r s :=
    eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp
    with hvRot_def
  -- The three pointwise pieces of the covariant-Leibniz split.
  set Amain : M → ℝ := fun x => tensorCovDerivPointwiseInner (I := I) (M := M)
    g r s wₙ (scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot) x
    with hAmain_def
  set Bleft : M → ℝ := fun x => tensorCovDerivCrossLeft (I := I) (M := M)
    g r s (chartAtlasPOU I M α) wₙ vRot x with hBleft_def
  set Cright : M → ℝ := fun x => tensorCovDerivCrossRight (I := I) (M := M)
    g r s (chartAtlasPOU I M α) wₙ vRot x with hCright_def
  -- `Amain` is integrable: a covariant-derivative inner product of two smooth
  -- compactly-supported sections.
  have hAmain_int : Integrable Amain
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s wₙ
      (scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot)
  -- `Bleft` is integrable: by the metric-isometry bridge it is the pointwise
  -- inner product of the covariant gradient of `wₙ` and the covector-prepend
  -- section, both smooth compactly-supported.
  have hBleft_int : Integrable Bleft
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_eq : Bleft = fun x => tensorInnerPointwise (I := I) (M := M)
        g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s wₙ).toFun x)
        ((prependCovGradSlot (I := I) (M := M) g r s
          (chartAtlasPOU I M α) vRot).toFun x) := by
      funext x
      rw [hBleft_def]
      exact tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g r s (chartAtlasPOU I M α) wₙ vRot x
    rw [h_eq]
    exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (covGrad (I := I) (M := M) g r s wₙ)
      (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot)
  -- `Cright` is integrable: by the metric-isometry bridge it is the pointwise
  -- inner product of `wₙ` and the covariant derivative of `vRot` along the
  -- gradient of the partition-of-unity weight, both smooth compactly-supported.
  have hCright_int : Integrable Cright
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_eq : Cright = fun x => tensorInnerPointwise (I := I) (M := M)
        g r s x (wₙ.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s vRot
          (chartAtlasPOU I M α)).toFun x) := by
      funext x
      rw [hCright_def]
      exact tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g r s (chartAtlasPOU I M α) wₙ vRot x
    rw [h_eq]
    exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M) wₙ
      (covDerivAlongGrad (I := I) (M := M) g r s vRot (chartAtlasPOU I M α))
  -- The pointwise covariant-Leibniz split of the source integrand.
  have h_pointwise : ∀ x,
      tensorCovDerivPointwiseInner (I := I) (M := M)
        g r s (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
        vRot x =
      Amain x - Bleft x + Cright x := by
    intro x
    rw [eigenvectorPouApprox, pouSmul_eq_scalarSmul (I := I) (M := M)
      g r s α wₙ, hAmain_def, hBleft_def, hCright_def]
    exact tensorCovDerivPointwiseInner_scalarSmul_left (I := I) (M := M)
      g r s (chartAtlasPOU I M α) wₙ vRot x
  -- Integrate the pointwise split and distribute over the integral.
  calc ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
          vRot x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∫ x, ((fun x => Amain x - Bleft x) x + Cright x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall h_pointwise)
    _ = (∫ x, (fun x => Amain x - Bleft x) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, Cright x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_add (hAmain_int.sub hBleft_int) hCright_int
    _ = ((∫ x, Amain x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
          ∫ x, Bleft x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, Cright x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_sub hAmain_int hBleft_int]

/-! ## The cross-right integral as the value part plus the gradient part

Chart-pulling the cross-right integral `∫ tensorCovDerivCrossRight g r s ζ_α wₙ
vRot` by `tensorCovDerivCrossRight_integral_eq_chartPull` and test-decoupling the
chart component of the covariant derivative along the gradient — by
`tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn`
— splits the chart-Euclidean cross-right integral into a *value* part carrying
the cross-right test-decoupling value coefficient `crossRightTestValueCoeff`
against `ψ`, and a *gradient* part carrying the cross-right gradient-term
coefficient `crossRightTestGradTerm` against the chart-Euclidean partials of
`ψ`. -/

/-- The product of the chart density times the cross-right gradient-term
coefficient `c[wₙ, l]` and the chart-Euclidean partial `∂_l ψ` of a
chart-supported smooth test function is integrable with respect to the
chart-pulled volume restricted to the chart target. -/
private lemma density_crossRightTestGradTerm_partialTest_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P₀ l y *
        euclidPartial (E := E) l ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- `∂_l ψ` is globally `C^∞`, compactly supported, and topologically supported
  -- inside the open chart target.
  have hdψ_cd : ContDiff ℝ ∞ (euclidPartial (E := E) l ψ) :=
    euclidPartial_contDiff (E := E) hψ l
  have hdψ_cs : HasCompactSupport (euclidPartial (E := E) l ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (euclidPartial_zero_off_tsupport (E := E) l hyψ)
  have hdψ_supp : tsupport (euclidPartial (E := E) l ψ) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine (closure_minimal ?_ (isClosed_tsupport _)).trans hψ_supp
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_zero_off_tsupport (E := E) l hz')
  -- The integrand `(density · c[wₙ, l]) · ∂_l ψ` is globally `C^∞` with compact
  -- support: a chart-target-`C^∞` coefficient times a chart-supported smooth
  -- test function.
  have hcd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y *
      crossRightTestGradTerm (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor α P₀ l y *
      euclidPartial (E := E) l ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor α P₀ l)
      hdψ_cd hdψ_supp
  have hcs : HasCompactSupport (fun y => densityOnEuclid (I := I) g α y *
      crossRightTestGradTerm (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor α P₀ l y *
      euclidPartial (E := E) l ψ y) :=
    hasCompactSupport_mul_chartTest (E := E) hdψ_cs
  exact (hcd.continuous.integrable_of_hasCompactSupport hcs).restrict

/-- The chart density times the finite-double-sum cross-right value combination
times a chart-supported smooth test function is integrable with respect to the
chart-pulled volume restricted to the chart target. -/
private lemma density_crossRightValueSum_test_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The integrand distributes into the finite double sum of `(P, Q)`-summands,
  -- each integrable by `crossRightValuePairing_integrable`.
  have h_sum_int : Integrable (fun y => ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        densityOnEuclid (I := I) g α y *
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    MeasureTheory.integrable_finset_sum _ (fun P _ =>
      MeasureTheory.integrable_finset_sum _ (fun Q _ =>
        crossRightValuePairing_integrable (I := I) (M := M) g r s h_atlas i
          α P₀ P Q hψ hψ_cs hψ_supp n))
  refine h_sum_int.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- The `(P, Q)`-summand of the chart-Euclidean cross-right chart-pull integral:
the chart density, the chart-frame tensor-metric Gram, the cutoff Euclidean
chart component of the smooth approximant `(wₙ).toCcTensor`, and the Euclidean
chart component of the covariant derivative of the inverse-Gram-rotated chart
test section along the gradient of the chart-atlas partition-of-unity weight. -/
private noncomputable def crossRightChartPullSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P Q : TensorCompIdx (E := E) r s) (n : ℕ) : EuclN → ℝ :=
  fun y => densityOnEuclid (I := I) g α y *
    (covChartMetricGram (I := I) (M := M) g r s α P Q y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
        α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
      tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp))
          (chartAtlasPOU I M α)) α Q y)

/-- The cutoff Euclidean chart component of the smooth approximant
`(wₙ).toCcTensor` agrees, almost everywhere with respect to the chart-`L²`
measure and simultaneously over all component multi-indices, with the concrete
cutoff Euclidean chart component. -/
private lemma tensorL2ChartComponentCutoff_smoothApprox_ae_all
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      ∀ P : TensorCompIdx (E := E) r s,
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
          α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y =
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P.1 P.2 y :=
  MeasureTheory.ae_all_iff.mpr (fun P =>
    tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_atlas i n).toCcTensor α P)

/-- **The cross-right integral as the value part plus the gradient part.** The
cross-right integral `∫ tensorCovDerivCrossRight g r s ζ_α wₙ vRot` equals the
cross-right value integral — the `eigenvectorCrossRight_tendsto` summand — plus
the cross-right gradient `∂ψ`-part — the `eigenvectorCrossRightGrad_tendsto`
summand. -/
private lemma eigenvectorCrossRight_integral_eq_value_plus_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_supp) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y ∂(volume : Measure EuclN)) +
    ∑ l : Fin (Module.finrank ℝ E),
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor α P₀ l y *
          euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN) := by
  classical
  -- Chart-pull the cross-right integral.
  rw [eigenvectorRotatedTestSection,
    tensorCovDerivCrossRight_integral_eq_chartPull (I := I) (M := M) g r s α
      (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
      (rotatedTestSection (I := I) (M := M) g r s α P₀
        (chartTestPullback (I := I) (M := M) α ψ)
        (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
        (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
          hψ_cs hψ_supp))]
  -- The two summed-integrand pieces, value and gradient.
  set valueIntegrand : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
    (∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
    ψ y with hvalueIntegrand_def
  set gradIntegrand : EuclN → ℝ := fun y =>
    ∑ l : Fin (Module.finrank ℝ E),
      densityOnEuclid (I := I) g α y *
          crossRightTestGradTerm (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P₀ l y *
        euclidPartial (E := E) l ψ y with hgradIntegrand_def
  -- The chart-pull integrand agrees, almost everywhere on the chart target,
  -- with the sum of the value and gradient integrands: substitute the
  -- test-decoupling for the chart component of the covariant derivative along
  -- the gradient, and the cutoff bridge for the cutoff chart component of the
  -- smooth approximant.
  have h_integrand_ae :
      (fun y => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            tensorComponentEuclid (I := I) (M := M) g r s
              (covDerivAlongGrad (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀
                  (chartTestPullback (I := I) (M := M) α ψ)
                  (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                  (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                    hψ_cs hψ_supp))
                (chartAtlasPOU I M α)) α Q y))
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      fun y => valueIntegrand y + gradIntegrand y := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (chartTargetEuclid_measurableSet (I := I) (M := M) α),
      (tensorL2ChartComponentCutoff_smoothApprox_ae_all (I := I) (M := M)
        g r s h_atlas i α n :
        ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α), _)]
      with y hy hcut
    -- The test-decoupling of the chart component of the covariant derivative
    -- along the gradient, on the chart target.
    have hdec : ∀ Q : CompIdx E r s,
        tensorComponentEuclid (I := I) (M := M) g r s
          (covDerivAlongGrad (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀
              (chartTestPullback (I := I) (M := M) α ψ)
              (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
              (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                hψ_cs hψ_supp))
            (chartAtlasPOU I M α)) α Q y =
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y +
          ∑ l : Fin (Module.finrank ℝ E),
            crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
              euclidPartial (E := E) l ψ y :=
      fun Q => tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn
        (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_supp Q hy
    change densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            tensorComponentEuclid (I := I) (M := M) g r s
              (covDerivAlongGrad (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀
                  (chartTestPullback (I := I) (M := M) α ψ)
                  (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                  (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                    hψ_cs hψ_supp))
                (chartAtlasPOU I M α)) α Q y) =
      valueIntegrand y + gradIntegrand y
    rw [hvalueIntegrand_def, hgradIntegrand_def]
    beta_reduce
    -- Per chart direction `l`, expand `crossRightTestGradTerm` into the
    -- `(P, Q)`-double sum, distribute, and substitute the cutoff bridge.
    have hgrad_per_l : ∀ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s h_atlas i n).toCcTensor α P₀ l y *
          euclidPartial (E := E) l ψ y =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                euclidPartial (E := E) l ψ y)) := by
      intro l
      rw [crossRightTestGradTerm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [← hcut P]
      ring
    -- The left-hand chart-pull double sum, normalised to a single `(P, Q)`-sum
    -- with the chart density distributed inward.
    have hLHS : densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s
                (covDerivAlongGrad (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀
                    (chartTestPullback (I := I) (M := M) α ψ)
                    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                      hψ_cs hψ_supp))
                  (chartAtlasPOU I M α)) α Q y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y +
                ∑ l : Fin (Module.finrank ℝ E),
                  crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                    euclidPartial (E := E) l ψ y)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [hdec Q]
    -- The value integrand, normalised to the same single `(P, Q)`-sum.
    have hVal : densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ψ y)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      ring
    -- The gradient integrand, reindexed and normalised to the same `(P, Q)`-sum.
    have hGrad : (∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ∑ l : Fin (Module.finrank ℝ E),
                crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                  euclidPartial (E := E) l ψ y) := by
      rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hgrad_per_l l),
        Finset.sum_comm]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
    -- Assemble: the left-hand and right-hand sides both normalise to the same
    -- `(P, Q)`-sum with the per-`(P, Q)` test-decoupling factored.
    rw [hLHS, hVal, hGrad, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  -- The chart-pull integral over the chart target equals the integral of the
  -- summed value and gradient integrands.
  rw [MeasureTheory.integral_congr_ae h_integrand_ae]
  -- Split the integral of the sum, then pull the finite sum out of the
  -- gradient integral.
  rw [MeasureTheory.integral_add
    (hvalueIntegrand_def ▸ density_crossRightValueSum_test_integrable
      (I := I) (M := M) g r s h_atlas i α P₀ hψ hψ_cs hψ_supp n)
    (hgradIntegrand_def ▸ MeasureTheory.integrable_finset_sum _
      (fun l _ => density_crossRightTestGradTerm_partialTest_integrable
        (I := I) (M := M) g r s h_atlas i α P₀ l hψ hψ_cs hψ_supp n))]
  congr 1
  rw [hgradIntegrand_def]
  exact MeasureTheory.integral_finset_sum _
    (fun l _ => density_crossRightTestGradTerm_partialTest_integrable
      (I := I) (M := M) g r s h_atlas i α P₀ l hψ hψ_cs hψ_supp n)

/-! ## Integrability of the chart right-hand-side limit terms

Each term of the chart-Euclidean right-hand side `eigenvectorChartRHS` is, paired
with the chart density and a chart-supported test function, integrable with
respect to the chart-pulled volume restricted to the chart target: a chart-`L²`
limit object — `MemLp 2` of the chart-`L²` measure by its companion-file lemma —
times the `C^∞`-coefficient test element `densityOnEuclid g α · c · ψ`. -/

/-- The chart density times a chart-`L²` limit object times a chart-supported
smooth test function is integrable with respect to the chart-pulled volume
restricted to the chart target. -/
private lemma density_memLp2_test_integrable
    (g : SmoothRiemannianMetric I M) (α : M) {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y * w y * ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp
    rw [chartL2Measure] at h
    exact h
  have hprod : MemLp (fun y => w y *
      (fun y => densityOnEuclid (I := I) g α y * ψ y) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hm_memLp.mul' hw
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only []
  ring

/-- The chart density times a chart-`C^∞`-coefficient times a chart-`L²` limit
object times a chart-supported smooth test function is integrable with respect
to the chart-pulled volume restricted to the chart target. -/
private lemma density_coeff_memLp2_test_integrable
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y * (c y * w y) * ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α hc hψ hψ_cs hψ_supp
    rw [chartL2Measure] at h
    exact h
  have hprod : MemLp (fun y => w y *
      (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hm_memLp.mul' hw
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only []
  ring

/-! ## The eigenvector chart variational identity

Applying the source-free per-approximant chart bilinear identity
`tensorComponent_chartBilinIdentity_of_dirichlet` to the
partition-of-unity-weighted canonical smooth approximants `Tₙ :=
eigenvectorPouApprox g r s h_atlas i α n`, every `n` satisfies the per-`n`
chart bilinear identity. Its source term splits — by the covariant Leibniz rule
and the cross-right value/gradient decomposition — into the main-Dirichlet term
and the two cross terms; both sides of the resulting per-`n` identity converge,
the limits are extracted from the companion-file limit lemmas, and
`tendsto_nhds_unique` upgrades the per-`n` identity to the limiting variational
identity. The final algebra divides by the eigenvalue `μ` and re-expresses the
two `∫ (div) · ψ` terms in the density-weighted shape, landing the right-hand
side exactly on `∫ densityOnEuclid g α · eigenvectorChartRHS · ψ`. -/

/-- **The eigenvector chart variational identity.** For a closed Riemannian
manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i` with nonzero
resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`, a component
multi-index `P₀`, and a chart-supported smooth test function `ψ`, the
density-weighted per-component variational identity

```
∫ ∑_{i, j} weightedInvGramOnEuclid g α · (eigenvectorChartWeakPartial …) · ∂_j ψ
  + ∫ densityOnEuclid g α · u_chart · ψ
  = ∫ densityOnEuclid g α · eigenvectorChartRHS · ψ
```

holds on `chartTargetEuclid α`, with `u_chart` the eigenvector chart
`P₀`-component `tensorL2ChartComponent g r s (tensorResolventEigenbasisVec
h_atlas i) α P₀`. This is the equation in the exact shape of the
`variational_identity` field of `ChartBilinearH1ComplData`. -/
theorem eigenvectorChartVariationalIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i' j' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i α P₀ i' y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀ y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  set μ : ℝ := i.fst.val with hμ_def
  have hμ_ne : μ ≠ 0 := i.fst.val_ne_zero
  -- The principal pairing `P` and the chart-density-weighted eigenvector chart
  -- component integral `U`.
  set P : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    (∑ i' : Fin (Module.finrank ℝ E),
      ∑ j' : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ i' y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
    ∂(volume : Measure EuclN) with hP_def
  set U : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
    ∂(volume : Measure EuclN) with hU_def
  -- The cross-left, cross-right value, source, and divergence limits.
  set CL : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s h_atlas i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(volume : Measure EuclN) with hCL_def
  set CRV : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          covChartMetricGram (I := I) (M := M) g r s α P' Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s h_atlas i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(volume : Measure EuclN) with hCRV_def
  set CRGdiv : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) with hCRGdiv_def
  set PRC : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) with hPRC_def
  set LOV : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) with hLOV_def
  set GD : ℝ := ∫ y, (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l y) * ψ y
    ∂(volume : Measure EuclN) with hGD_def
  -- The chart-`L²`-target integral of a `volume`-integral over the chart target.
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  -- Step 1: the per-`n` chart bilinear identity, with the source term split.
  have h_per_n : ∀ n : ℕ,
      (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
        ψ =
      ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp)) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_supp) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ((∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                  α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN)) +
      ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s h_atlas i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN))) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN)) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
              α P₀ l) y) * ψ y ∂(volume : Measure EuclN) := by
    intro n
    rw [tensorComponent_chartBilinIdentity_of_dirichlet (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) P₀
      (eigenvectorPouApprox_tsupport_subset_source (I := I) (M := M)
        g r s h_atlas i α n)
      (eigenvectorPouApprox_component_tsupport_subset (I := I) (M := M)
        g r s h_atlas i α P₀ n) hψ hψ_cs hψ_supp]
    rw [show (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            (rotatedTestSection (I := I) (M := M) g r s α P₀
              (chartTestPullback (I := I) (M := M) α ψ)
              (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
              (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                hψ_cs hψ_supp)) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
    rw [eigenvectorSource_integral_split (I := I) (M := M) g r s h_atlas i
      α P₀ hψ hψ_cs hψ_supp n,
      eigenvectorCrossRight_integral_eq_value_plus_grad (I := I) (M := M)
        g r s h_atlas i α P₀ hψ hψ_cs hψ_supp n]
  -- Step 2: the limit `L` of the per-`n` right-hand side.
  set L : ℝ := ((1 - μ) * U - CL + (CRV + -CRGdiv) - PRC - LOV + GD) with hL_def
  have h_rhs_tendsto : Filter.Tendsto
      (fun n => ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor
            (pouSmul (I := I) (M := M) g r s α
              (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
                hψ hψ_cs hψ_supp)) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
            (chartAtlasPOU I M α)
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P' : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                    (((eigenvectorSmoothApprox (I := I) (M := M)
                        g r s h_atlas i n).toCcTensor) : TensorL2 r s g)
                    α P' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN)) +
        ∑ l : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s h_atlas i n).toCcTensor α P₀ l y *
              euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN))) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
              α P₀ y * ψ y ∂(volume : Measure EuclN)) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
              α P₀ y * ψ y ∂(volume : Measure EuclN)) +
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n)
                α P₀ l) y) * ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 L) := by
    rw [hL_def]
    -- The main-Dirichlet limit, paired with `(pouSmul g r s α vRot)` in slot 2.
    have h_md := eigenvectorMainDir_tendsto (I := I) (M := M) g r s h_atlas i
      α P₀ hψ hψ_cs hψ_supp
    refine (((((h_md.sub
      (eigenvectorCrossLeft_tendsto (I := I) (M := M) g r s h_atlas i
        α P₀ hψ hψ_cs hψ_supp)).add
      ((eigenvectorCrossRight_tendsto (I := I) (M := M) g r s h_atlas i
        α P₀ hψ hψ_cs hψ_supp).add
        (eigenvectorCrossRightGrad_tendsto (I := I) (M := M) g r s h_atlas i
          α P₀ hψ hψ_cs hψ_supp))).sub
      (covPrincipalRotationCoeff_source_tendsto (I := I) (M := M) g r s
        h_atlas i α P₀ hψ hψ_cs hψ_supp)).sub
      (covLowerOrderRotationValueCoeff_source_tendsto (I := I) (M := M) g r s
        h_atlas i α P₀ hψ hψ_cs hψ_supp)).add
      (weightedGradCoeffDivSum_source_tendsto (I := I) (M := M) g r s
        h_atlas i α P₀ hψ hψ_cs hψ_supp)).congr ?_
    intro n
    rfl
  -- Step 3: the per-`n` left-hand side converges to `μ · P`.
  have h_lhs_tendsto : Filter.Tendsto
      (fun n => (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s h_atlas i α n) α P₀)
        ψ)
      atTop (𝓝 (μ * P)) := by
    rw [hμ_def, hP_def]
    exact bilin_eigenvectorPouApprox_tendsto (I := I) (M := M) g r s h_atlas i
      α P₀ hψ hψ_cs hψ_supp
  -- Step 4: `μ · P = L` by uniqueness of limits.
  have h_mu_P : μ * P = L := by
    refine tendsto_nhds_unique (h_lhs_tendsto.congr ?_) h_rhs_tendsto
    intro n
    exact h_per_n n
  -- Step 5: the chart-`C^∞`-coefficients of the right-hand-side terms are `C^∞`.
  have h_one_div_density : ContDiffOn ℝ ∞
      (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
      (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')
  -- Step 6: `∫ density · eigenvectorChartRHS · ψ = μ⁻¹ · (∫ density · bracket · ψ)`.
  -- The chart-Euclidean right-hand side carries the global `μ⁻¹` factor; the
  -- two divergence-limit terms carry `1 / density`, which cancels the chart
  -- density on the chart target (where it is strictly positive).
  have h_rhs_integral :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀ y * ψ y
        ∂(volume : Measure EuclN)) =
      μ⁻¹ * (U - CL + CRV - PRC - LOV + GD - CRGdiv) := by
    -- The seven integrability facts for the bracket terms.
    have hint_U : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (Lp.memLp (tensorL2ChartComponent (I := I) (M := M)
          g r s (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
          α P₀))
        hψ hψ_cs hψ_supp
    have hint_CLsum : Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finset_sum _ (fun P' _ =>
          MeasureTheory.integrable_finset_sum _ (fun Q _ =>
            crossLeftLimitPairing_integrable (I := I) (M := M) g r s h_atlas i
              α P₀ P' Q hψ hψ_cs hψ_supp))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_CRVsum : Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finset_sum _ (fun P' _ =>
          MeasureTheory.integrable_finset_sum _ (fun Q _ =>
            crossRightValueLimitPairing_integrable (I := I) (M := M)
              g r s h_atlas i α P₀ P' Q hψ hψ_cs hψ_supp))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_PRC : Integrable (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
          g r s h_atlas i α P₀)
        hψ hψ_cs hψ_supp
    have hint_LOV : Integrable (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
          g r s h_atlas i α P₀)
        hψ hψ_cs hψ_supp
    have hint_GD : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ l y) * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (memLp_finset_sum (μ := (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
            g r s h_atlas i α P₀ l))
        hψ hψ_cs hψ_supp
    have hint_CRGD : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y) * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s h_atlas i α P₀)
        hψ hψ_cs hψ_supp
    -- The integrand identity on the chart target: `μ⁻¹` factors out and the
    -- `1 / density` cancels the chart density.
    have h_integrand : Set.EqOn
        (fun y => densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀ y * ψ y)
        (fun y => μ⁻¹ *
          ((densityOnEuclid (I := I) g α y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y * ψ y) -
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r (s + 1),
                ∑ Q : TensorCompIdx (E := E) r (s + 1),
                  covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                      crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossLeftLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y +
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r s,
                ∑ Q : TensorCompIdx (E := E) r s,
                  covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                      crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossRightLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y -
            densityOnEuclid (I := I) g α y *
              covPrincipalRotationCoeffLimit (I := I) (M := M)
                g r s h_atlas i α P₀ y * ψ y -
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
                g r s h_atlas i α P₀ y * ψ y +
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                ∑ l : Fin (Module.finrank ℝ E),
                  weightedGradCoeffDivLimit (I := I) (M := M)
                    g r s h_atlas i α P₀ l y) * ψ y -
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                crossRightGradCoeffDivLimit (I := I) (M := M)
                  g r s h_atlas i α P₀ y) * ψ y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro y _hy
      simp only [eigenvectorChartRHS]
      ring
    rw [MeasureTheory.setIntegral_congr_fun hcTE_meas h_integrand]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- Identify each of the seven bracket integrals: the first three are the
    -- chart-target integrals `U`, `CL`, `CRV`; the principal- / lower-order-
    -- rotation terms convert chart-target to whole-space integrals (the test
    -- function vanishes off the chart target); the two divergence terms drop
    -- the cancelling `densityOnEuclid g α · (1 / densityOnEuclid g α)`.
    have hψ_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α → ψ y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h))
    have hD4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeffLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN)) = PRC := by
      rw [hPRC_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, mul_zero])
    have hD5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN)) = LOV := by
      rw [hLOV_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, mul_zero])
    have hD6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s h_atlas i α P₀ l y) * ψ y
          ∂(volume : Measure EuclN)) = GD := by
      rw [hGD_def]
      rw [show (∫ y, (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y ∂(volume : Measure EuclN)
        from (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [hψ_zero y hy, mul_zero])).symm]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s h_atlas i α P₀ l y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            ((∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    have hD7 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ y) * ψ y
          ∂(volume : Measure EuclN)) = CRGdiv := by
      rw [hCRGdiv_def]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            (crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    -- Distribute the integral of the bracket over its seven terms by
    -- peeling one term at a time; each step is the additivity of the
    -- Bochner integral, applied to the explicit integrability facts.
    have e1 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y +
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y -
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y) * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y +
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y) ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀ y) * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub (((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub
        hint_LOV).add hint_GD) hint_CRGD
    have e2 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y +
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y) ∂(volume : Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((1 / densityOnEuclid (I := I) g α y) *
            ∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l y) * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_add ((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub hint_LOV) hint_GD
    have e3 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y -
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y) ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub (((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC) hint_LOV
    have e4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y -
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y) ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ y * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub ((hint_U.sub hint_CLsum).add hint_CRVsum) hint_PRC
    have e5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y +
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y) ∂(volume : Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_add (hint_U.sub hint_CLsum) hint_CRVsum
    have e6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y -
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y) ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y * ψ y ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) * ψ y ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub hint_U hint_CLsum
    rw [e1, e2, e3, e4, e5, e6, ← hU_def, ← hCL_def, ← hCRV_def,
      hD4, hD5, hD6, hD7]
  -- Step 7: assemble the final algebra.
  rw [hP_def, hU_def, h_rhs_integral, ← hU_def]
  rw [show U - CL + CRV - PRC - LOV + GD - CRGdiv =
      L + μ * U from by rw [hL_def]; ring]
  rw [← h_mu_P]
  rw [show μ⁻¹ * (μ * P + μ * U) = P + U from by
    rw [mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul,
      one_mul]]

/-! ## The chart-bilinear divergence-form data of the eigenvector chart component

Assembling the eigenvector chart `P₀`-component into the chart-bilinear
divergence-form data structure `TensorChartBilinearH1ComplData g r s α P₀`: the
chart component `u_chart` is the canonical eigenvector chart component, its weak
partials are the candidate weak chart partials `eigenvectorChartWeakPartial`, the
right-hand side is the chart-Euclidean right-hand side `eigenvectorChartRHS`, and
the variational identity is the one assembled above. -/

/-- **The chart-bilinear divergence-form data of the eigenvector chart
component.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart
center `α : M`, and a component multi-index `P₀`, this is the chart-bilinear
divergence-form data `TensorChartBilinearH1ComplData g r s α P₀` of the chart
`P₀`-component of the abstract connection-Laplacian eigenvector
`tensorResolventEigenbasisVec h_atlas i`:

* the chart component `u_chart` is `tensorL2ChartComponent g r s
  (tensorResolventEigenbasisVec h_atlas i) α P₀`;
* the weak partials are the candidate weak chart partials
  `eigenvectorChartWeakPartial g r s h_atlas i α P₀`;
* the right-hand side `f_chart` is the chart-Euclidean right-hand side
  `eigenvectorChartRHS g r s h_atlas i α P₀`;
* the variational identity is `eigenvectorChartVariationalIdentity`.

This packages the per-component chart-local weak-elliptic identity for the
`P₀`-chart-component of the abstract connection-Laplacian eigenvector. -/
def eigenvectorTensorChartBilinearData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
  ⟨{ u_chart := fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
     f_chart := eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀
     weak_partial := eigenvectorChartWeakPartial (I := I) (M := M)
       g r s h_atlas i α P₀
     u_chart_memLp_weighted :=
       tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
         (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀
     f_chart_memLp_weighted :=
       eigenvectorChartRHS_memLp_weighted (I := I) (M := M) g r s h_atlas i α P₀
     weak_partial_locally_memLp := fun k _K hK hK_in =>
       eigenvectorChartWeakPartial_locally_memLp (I := I) (M := M)
         g r s h_atlas i α P₀ k hK hK_in
     weak_partial_isWeakPartial := fun k =>
       eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
         g r s h_atlas i α P₀ k
     variational_identity := fun _ψ hψ hψ_cs hψ_supp =>
       eigenvectorChartVariationalIdentity (I := I) (M := M) g r s h_atlas i
         α P₀ hψ hψ_cs hψ_supp }⟩

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
  eigenvectorTensorChartBilinearData (I := I) (M := M) g r s h_atlas i α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
