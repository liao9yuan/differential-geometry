import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralSmoothGate
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CutoffChartComponentMemWkp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

/-!
# The per-chart smooth-representative existence for an arbitrary spectral-smooth `L²` tensor

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E`, the tensor
super-critical reconstruction bridge `TensorSuperCriticalReconstruct g r s`
(`SpectralSmoothGate.lean`) asks that an `L²` tensor `w`, all of whose canonical
Euclidean chart-Sobolev components lie in `W^{2k,2}` for every order `k`, be the
`L²` class of a genuine `C^∞` (`SmoothCcTensor`) section.

This file establishes the **foundational analytic layer** of that bridge, fully
unconditionally (no `HasLocallyConstantChartAt`): from the super-critical chart
hypothesis on `w` it produces, at every chart centre `α` and component
multi-index `P₀`, a genuine `C^∞`, compactly-supported-in-target representative
of the canonical Euclidean chart `P₀`-component `tensorL2ChartComponent g r s w
α P₀`, almost everywhere equal to it. This is the exact data shape that the
single-chart frame constructor `tensorBundleSectionOfChartComponents`
(`TensorChartFrameSection.lean`) consumes, and it is the abstract-`w` analogue of
the per-eigenvector existence theorem
`eigenvectorChartComponent_exists_smooth_representative_unconditional`
(`EigenvectorChartComponentSmooth.lean`).

## What is proved here (fully, unconditionally)

* `superCriticalChartComponent_exists_smooth_representative` — for an `L²` tensor
  `w` whose every canonical Euclidean chart `P₀`-component lies in `MemWkp (2k) 2`
  on its chart target for every order `k`, the chart `P₀`-component admits a
  `C^∞`, compactly-supported-strictly-inside-target representative, almost
  everywhere equal to it on the chart target.

The construction is the standard localisation: the iterated Euclidean Sobolev
embedding `contDiffOn_of_forall_memWkp_two` produces a `C^∞` representative `u₀`
on the open chart target; multiplying by a smooth cutoff that is `1` on a
neighbourhood of the compact partition-of-unity kernel `chartPouKernel α` and
compactly supported strictly inside the chart target localises it; and the
chart component of *any* abstract `L²` element is a.e. zero off that kernel
(`tensorL2ChartComponent_ae_zero_off_chartPouKernel`), so the localisation does
not change the a.e. class.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹`, eigenvalues `λᵢ ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## `CompleteSpace E`

A finite-dimensional real normed space is complete; this is needed by the
chart-component machinery imported from the elliptic-bridge layer. -/

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Two trivial topological facts about the chart target minus its kernel

The chart target minus the compact partition-of-unity kernel is open (an open
set minus a closed set) and is a subset of the chart target. These twins of the
private elliptic-bridge helpers are reproved inline for use in the a.e. patching
below. -/

/-- The chart-`α` Euclidean target minus the (closed) partition-of-unity kernel
is open. -/
private lemma chartTargetEuclid_sdiff_chartPouKernel_isOpen' (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
    (I := I) (M := M) α).sdiff
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

/-- The chart-`α` Euclidean target minus the partition-of-unity kernel is a
subset of the chart target. -/
private lemma chartTargetEuclid_sdiff_chartPouKernel_subset' (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Set.diff_subset

/-! ## The chart component of `w` is a.e. zero off the kernel, on `Ω \ K`

The chart component of any abstract `L²` element is almost everywhere zero off
the compact partition-of-unity kernel
(`tensorL2ChartComponent_ae_zero_off_chartPouKernel`). Restricting that a.e.
implication to the open subset `Ω \ K` of the chart target — where the kernel
membership fails everywhere — turns it into an honest a.e. equality with the
zero function. -/

/-- For an arbitrary `L²` tensor `w`, the canonical Euclidean chart
`P₀`-component is almost everywhere zero on the chart-`α` target minus the
partition-of-unity kernel. -/
private lemma superCriticalChartComponent_ae_zero_off_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : TensorL2 r s g) (α : M)
    (P₀ : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorCompIdx
      (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- The a.e. implication "off the kernel ⇒ zero", on `chartL2Measure α`.
  have h_ae :
      ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α →
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
    tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s w α P₀
  -- `chartL2Measure α = volume.restrict (chartTargetEuclid α)`, so we may
  -- restrict the a.e. implication to the open subset `Ω \ K`.
  have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
    (chartTargetEuclid_sdiff_chartPouKernel_isOpen' (I := I) (M := M) α).measurableSet
  have h_ae_V :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α →
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    -- `chartL2Measure α` is `volume.restrict (chartTargetEuclid α)`, which
    -- dominates its further restriction to `Ω \ K`.
    refine ae_mono ?_ h_ae
    show (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) ≤
      chartL2Measure (I := I) (M := M) α
    rw [show chartL2Measure (I := I) (M := M) α =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) from rfl]
    exact Measure.restrict_mono_set _
      (chartTargetEuclid_sdiff_chartPouKernel_subset' (I := I) (M := M) α)
  -- On `Ω \ K` the kernel membership fails for every point, so the implication
  -- collapses to the value being zero.
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [(ae_restrict_iff' hV_meas).mp h_ae_V] with y hy
  intro hy_V
  exact hy hy_V hy_V.2

/-! ## The per-chart smooth-representative existence

The localised representative is the smooth Sobolev representative on the chart
target multiplied by a smooth cutoff that equals `1` on a neighbourhood of the
compact kernel and is supported strictly inside the chart target. It agrees a.e.
with the chart component on the chart target: on the kernel the cutoff is `1`
and the Sobolev representative is a.e. the chart component; off the kernel both
the chart component and the localised representative are a.e. zero. -/

/-- **Per-chart smooth representative of the chart component of a super-critical
`L²` tensor.** For an `L²` tensor `w` whose canonical Euclidean chart
`P₀`-component lies in `MemWkp (2k) 2` on its chart target for *every* order
`k`, the chart `P₀`-component admits a `C^∞` representative, compactly supported
strictly inside the chart target, almost everywhere equal to it.

This is the abstract-`w` analogue of
`eigenvectorChartComponent_exists_smooth_representative_unconditional`. -/
theorem superCriticalChartComponent_exists_smooth_representative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : TensorL2 r s g) (α : M)
    (P₀ : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorCompIdx
      (E := E) r s)
    (h_all : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  -- Abbreviations for the chart target, the chart component and the kernel.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- `u ∈ MemWkp k 2` on the chart target for every order `k`: the hypothesis
  -- gives even orders `2k`, and downward monotonicity gives the odd ones.
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := by
    intro k
    -- `k ≤ 2k`, so `MemWkp (2k) ⇒ MemWkp k`.
    exact MemWkp.le_of_le (d := Module.finrank ℝ E)
      (by omega : k ≤ 2 * k) (h_all k)
  -- The iterated-Sobolev embedding: a `C^∞` representative `u₀` on the open
  -- chart target, almost everywhere equal to `u`.
  obtain ⟨u₀, hu₀_cdiff, hu_ae_u₀⟩ :=
    contDiffOn_of_forall_memWkp_two (d := Module.finrank ℝ E) hΩ_open hu_memWkp
  -- A smooth cutoff `η`, equal to `1` on a neighbourhood of the compact kernel
  -- `K` and compactly supported strictly inside the chart target `Ω`.
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_cdiff, hη_cpt, _hη_range,
      hη_one_cthick, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hK_compact hΩ_open hK_subset_Ω
  -- The cutoff is `1` on the kernel itself.
  have hη_one_K : ∀ y ∈ K, η y = 1 := fun y hy =>
    hη_one_cthick y (Metric.self_subset_cthickening _ hy)
  -- The localised representative.
  set u_smooth : EuclN → ℝ := fun y => η y * u₀ y with hu_smooth_def
  -- `u_smooth` is `C^∞` on the chart target: a product of two `C^∞` functions.
  have hu_smooth_cdiff : ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω :=
    (hη_cdiff.contDiffOn).mul hu₀_cdiff
  -- `u_smooth` has compact support: its support sits inside that of `η`.
  have hu_smooth_cpt : HasCompactSupport u_smooth :=
    HasCompactSupport.mul_right hη_cpt
  -- `tsupport u_smooth ⊆ tsupport η ⊆ Ω`.
  have hu_smooth_tsupp : tsupport u_smooth ⊆ Ω :=
    (tsupport_mul_subset_left).trans hη_tsupp
  refine ⟨u_smooth, hu_smooth_cdiff, hu_smooth_cpt, hu_smooth_tsupp, ?_⟩
  -- The almost-everywhere identity `u_smooth =ᵐ u`.
  -- The chart component is a.e. zero off the kernel.
  have hu_ae_zero :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) :=
    superCriticalChartComponent_ae_zero_off_kernel
      (I := I) (M := M) g r s w α P₀
  -- `u₀ =ᵐ u` on `Ω` (the embedding), hence on the open subset `Ω \ K`.
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hΩK_subset : Ω \ K ⊆ Ω := Set.diff_subset
  have hu₀_ae_u_ΩK : u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hΩK_subset hu_ae_u₀)
  -- Off the kernel: `u₀ =ᵐ u =ᵐ 0`, hence `u_smooth = η · u₀ =ᵐ 0`.
  have hu_smooth_ae_zero_ΩK :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hu₀_ae_zero_ΩK :
        u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
          (fun _ : EuclN => (0 : ℝ)) := hu₀_ae_u_ΩK.trans hu_ae_zero
    filter_upwards [hu₀_ae_zero_ΩK] with y hy
    simp [hu_smooth_def, hy]
  -- `u =ᵐ u_smooth` on `Ω \ K`: both are a.e. zero there.
  have hu_ae_u_smooth_ΩK :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u_smooth :=
    hu_ae_zero.trans hu_smooth_ae_zero_ΩK.symm
  -- On the kernel: `η = 1`, so `u_smooth = u₀ =ᵐ u`.
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hu₀_ae_u_K : u₀ =ᵐ[(volume : Measure EuclN).restrict K] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hK_subset_Ω hu_ae_u₀)
  have hu_smooth_ae_u₀_K :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict K] u₀ := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simp [hu_smooth_def, hη_one_K y hy]
  have hu_ae_u_smooth_K :
      u =ᵐ[(volume : Measure EuclN).restrict K] u_smooth :=
    (hu₀_ae_u_K.symm).trans hu_smooth_ae_u₀_K.symm
  -- Patch the two a.e. identities over `Ω = K ∪ (Ω \ K)`.
  have hΩ_eq : Ω = K ∪ (Ω \ K) := by
    rw [Set.union_diff_cancel hK_subset_Ω]
  have hu_ae_u_smooth :
      u =ᵐ[(volume : Measure EuclN).restrict Ω] u_smooth := by
    rw [hΩ_eq]
    exact (MeasureTheory.ae_restrict_union_iff K (Ω \ K)
      (fun x => u x = u_smooth x)).mpr ⟨hu_ae_u_smooth_K, hu_ae_u_smooth_ΩK⟩
  exact hu_ae_u_smooth.symm

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
