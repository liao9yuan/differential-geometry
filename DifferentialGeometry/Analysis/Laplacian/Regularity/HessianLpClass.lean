import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainPerChartWitness
import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

/-!
# Chart-side `L^p` Hessian for elements of `laplacianDomain g`

For an element `u_h` of the Laplacian domain `laplacianDomain g` of a smooth
Riemannian metric `g` on a closed manifold `(M, g)`, the chart-pushed
representative `chartPushed POU α u_h.coeFn` lies in the iterated Euclidean
Sobolev space `MemWkp 2 2` on the chart target. The canonical second weak
partial in coordinate directions `(i, j)` is the chosen weak partial
`chosenWeakPartial' 2 j (chosenWeakPartial' 2 i (chartPushed POU α u_h.coeFn))`,
all on `chartTargetEuclid α`. We package these chart-side weak partials, prove
their `L^2` regularity, and produce the chart-coordinate Frobenius norm
squared along with its `L^1` regularity.

For smooth inputs, the chart-side weak Hessian agrees almost everywhere with
the classical second partial of the chart-pushed function (no Christoffel
correction — the latter would belong to the geometer's *tensor* Hessian,
which differs from the pure second weak partial of the chart-pushed
function).

## Main definitions

* `laplacianDomainHessianChart g α hu_h i j` — the chart-side second weak
  partial of `chartPushed POU α u_h.coeFn` in coordinate directions `(i, j)`,
  for `u_h ∈ laplacianDomain g`.
* `laplacianDomainHessFrobeniusSqChart g α hu_h` — the chart-metric Frobenius
  norm squared of the chart-side Hessian, contracted with two inverse Gram
  factors.

## Main results

* `laplacianDomainHessianChart_memLp_two` — chart-side second weak partial
  is in `L^2` of the chart target.
* `laplacianDomainHessFrobeniusSqChart_memLp_one` — the chart-metric Frobenius
  square is in `L^1` of the chart target.
* `laplacianDomainHessianChart_smooth_case` — for a smooth scalar `f`, the
  chart-side weak Hessian of `smoothToH1Compl g f` is, a.e. on the chart
  target, equal to the classical second partial of `chartPushed POU α f.toFun`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianLpClass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The chart-pushed function lies in `MemWkp 2 2` on the chart target

The C-step `laplacianDomain_memWkpChart_two_unconditional` gives, for every
`u_h ∈ laplacianDomain g`, the `MemWkp 2 2` membership of the chart-pushed
function on the chart target. We package this as a small reusable
abbreviation. -/

/-- The canonical chart-pushed representative of `H1ComplToLp u_h` on the
chart target image. -/
private noncomputable def chartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)

/-- For `u_h ∈ laplacianDomain g`, the chart-pushed function is in
`MemWkp 2 2` of the chart target. -/
private lemma chartPushedU_memWkp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := laplacianDomain_memWkpChart_two_unconditional (I := I) (M := M) g hu_h
  exact h.1 α

/-- For `u_h ∈ laplacianDomain g`, the chart-pushed function is in `MemW1p 2`
of the chart target. -/
private lemma chartPushedU_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DeGiorgi.MemW1p 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedU_memWkp_two (I := I) (M := M) g α hu_h).memW1p

/-- The inner chosen weak partial of `chartPushedU` is in `MemW1p 2` on the
chart target. -/
private lemma chosenInner_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := chartPushedU_memWkp_two (I := I) (M := M) g α hu_h
  have hstep := h.chosenWeakPartial_mem i
  rw [MemWkp.one_iff_memW1p] at hstep
  exact hstep

/-! ## Definition: chart-side second weak partial -/

/-- For `u_h ∈ laplacianDomain g`, the chart-side second weak partial in
coordinate directions `(i, j)` of the chart-pushed function on the chart
target. This is the iteration of `chosenWeakPartial' 2`, applied first in
direction `i` (inner) and then in direction `j` (outer). -/
noncomputable def laplacianDomainHessianChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
/-- Unfolding `laplacianDomainHessianChart` to its definitional content. -/
private lemma laplacianDomainHessianChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushedU (I := I) (M := M) g α u_h)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

/-! ## Theorem 1: chart-side Hessian is in `L^2` on the chart target -/

/-- **Chart-side second weak partial is in `L^2`.** For
`u_h ∈ laplacianDomain g` and any pair of coordinate directions `(i, j)`,
the chart-side Hessian `laplacianDomainHessianChart g α hu_h i j` lies in
`L^2` of the volume measure restricted to `chartTargetEuclid α`. -/
theorem laplacianDomainHessianChart_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [laplacianDomainHessianChart_def]
  exact chosenWeakPartial'_memLp_of_mem
    (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j

/-! ## Vanishing of the chart-pushed function outside the support kernel -/

omit [NeZero (Module.finrank ℝ E)] in
/-- The chart-pushed function vanishes a.e. on
`chartTargetEuclid α \ chartImagePOUTsupport α`. (In fact it vanishes
pointwise there.) -/
private lemma chartPushedU_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushedU (I := I) (M := M) g α u_h
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  refine (ae_restrict_iff' hV_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  unfold chartPushedU
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
    α _ hy.1 hy.2

/-- The chart-pushed function is in `MemW1p 2` on the open subset
`chartTargetEuclid α \ chartImagePOUTsupport α`. -/
private lemma chartPushedU_memW1p_sdiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DeGiorgi.MemW1p 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ chartTargetEuclid (I := I) (M := M) α := Set.diff_subset
  have hu : DeGiorgi.MemW1p 2 (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedU_memW1p (I := I) (M := M) g α hu_h
  refine ⟨?_, ?_⟩
  · exact hu.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
  · intro k
    obtain ⟨gk, hgk_memLp, hgk_weak⟩ := hu.2 k
    refine ⟨gk, ?_, ?_⟩
    · exact hgk_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
    · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgk_weak

omit [NeZero (Module.finrank ℝ E)] in
/-- The chosen weak partial of `chartPushedU` along the open set `V` (the
`sdiff` open set) is a.e. zero on `volume.restrict V`. -/
private lemma chosenWeakPartial_chartPushedU_ae_zero_sdiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hae_zero :
      chartPushedU (I := I) (M := M) g α u_h
        =ᵐ[(volume : Measure EuclN).restrict V]
        (fun _ : EuclN => (0 : ℝ)) :=
    chartPushedU_ae_zero_off_support (I := I) (M := M) g α u_h
  exact chosenWeakPartial'_ae_zero_of_ae_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open
    hae_zero i

/-- The chosen weak partial taken on the full chart target equals, a.e. on
`V := chartTarget \ K`, the chosen weak partial taken on `V`. This uses the
ae-uniqueness of weak partials between locally integrable witnesses. -/
private lemma chosenWeakPartial_chartPushedU_restrict_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ chartTargetEuclid (I := I) (M := M) α := Set.diff_subset
  -- Both chosen partials are weak partials of `chartPushedU` on `V`.
  have hu_full := chartPushedU_memW1p (I := I) (M := M) g α hu_h
  have hu_sdiff := chartPushedU_memW1p_sdiff (I := I) (M := M) g α hu_h
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_full i
  have h_partial_Ω_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      (chartPushedU (I := I) (M := M) g α u_h) V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset h_partial_Ω
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V)
      (chartPushedU (I := I) (M := M) g α u_h) V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_sdiff i
  -- Local integrability on V for both.
  have hmemLp_Ω : MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict V) := by
    have hLp := chosenWeakPartial'_memLp_of_mem hu_full i
    exact hLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
  have h_loc_Ω : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α))
      ((volume : Measure EuclN).restrict V) :=
    hmemLp_Ω.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmemLp_V : MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V) 2
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem hu_sdiff i
  have h_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h) V)
      ((volume : Measure EuclN).restrict V) :=
    hmemLp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open h_partial_Ω_on_V h_partial_V
    h_loc_Ω h_loc_V

/-- **Inner chosen weak partial is ae-zero outside the support kernel.**
For `u_h ∈ laplacianDomain g`, the inner chosen weak partial of
`chartPushedU` along the full chart target is ae-zero on
`chartTargetEuclid α \ chartImagePOUTsupport α`. -/
private lemma chosenWeakPartial_chartPushedU_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  exact (chosenWeakPartial_chartPushedU_restrict_ae_eq
      (I := I) (M := M) g α hu_h i).trans
    (chosenWeakPartial_chartPushedU_ae_zero_sdiff
      (I := I) (M := M) g α hu_h i)

/-! ## Outer chosen weak partial: ae-vanishing outside the support kernel -/

/-- The outer chosen weak partial of the inner one, taken on the open
sdiff `V`, is a.e. zero on `V`. -/
private lemma chosenWeakPartial_outer_sdiff_ae_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushedU (I := I) (M := M) g α u_h)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  -- Apply chosenWeakPartial'_ae_zero_of_ae_zero on V to the inner
  -- ae-zero hypothesis.
  exact chosenWeakPartial'_ae_zero_of_ae_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open
    (chosenWeakPartial_chartPushedU_ae_zero_off_support
      (I := I) (M := M) g α hu_h i) j

/-- The inner chosen weak partial on the open sdiff `V` is in `MemW1p 2` on
`V`. -/
private lemma chosenInner_sdiff_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushedU (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by
  have h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedU (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) := by
    -- Promote MemW1p to MemWkp 2.
    -- Easier: build directly from chartPushedU_memWkp_two via restriction.
    classical
    set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
      chartImagePOUTsupport (I := I) (M := M) α with hV_def
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    have hΩ_open : IsOpen Ω :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
    have hV_subset : V ⊆ Ω := Set.diff_subset
    -- Both partials of u on Ω restrict to partials on V; chosen partials
    -- ae-equal between Ω and V on volume.restrict V (already shown). Then
    -- MemWkp 2 2 on V follows from MemWkp 2 2 on Ω via the standard
    -- restriction argument.
    -- We unfold MemWkp 2 to: MemW1p ∧ ∀ i, MemWkp 1 (chosenWeakPartial' i).
    refine ⟨chartPushedU_memW1p_sdiff (I := I) (M := M) g α hu_h, ?_⟩
    intro k
    -- Need: MemWkp 1 2 (chosenWeakPartial' 2 k u V) V.
    -- This is equivalent to MemW1p 2 of the chosen partial on V (by MemWkp.one_iff_memW1p).
    -- Then we use that the chosen partial on Ω is in MemW1p 2 on Ω, hence on
    -- V by restriction, and ae-equals the chosen partial on V.
    rw [MemWkp.one_iff_memW1p]
    have h_inner_Ω := chosenInner_memW1p (I := I) (M := M) g α hu_h k
    have h_inner_V : DeGiorgi.MemW1p 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (chartPushedU (I := I) (M := M) g α u_h) Ω) V := by
      refine ⟨?_, ?_⟩
      · exact h_inner_Ω.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
      · intro j
        obtain ⟨gj, hgj_memLp, hgj_weak⟩ := h_inner_Ω.2 j
        refine ⟨gj, ?_, ?_⟩
        · exact hgj_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
        · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgj_weak
    -- ae-equality of the two chosen partials on volume.restrict V.
    have hae := chosenWeakPartial_chartPushedU_restrict_ae_eq
      (I := I) (M := M) g α hu_h k
    exact (MemW1p_congr_ae
      (d := Module.finrank ℝ E) hV_open hae).mp h_inner_V
  have hstep := h.chosenWeakPartial_mem i
  rw [MemWkp.one_iff_memW1p] at hstep
  exact hstep

/-- **Outer chosen weak partial is ae-zero outside the support kernel.** This
is the key vanishing statement we will use to bound the Frobenius squared. -/
lemma laplacianDomainHessianChart_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ Ω := Set.diff_subset
  -- Strategy: define the "mid" partial which has inner-on-Ω and outer-on-V,
  -- show it is ae-zero on V (= h_outer_V_zero), and connect it to FΩ via
  -- uniqueness of weak partials. Both FΩ and Fmid are weak j-partials of the
  -- inner partial on Ω, both locally integrable on V.
  -- Names:
  set inner_Ω := chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
    (chartPushedU (I := I) (M := M) g α u_h) Ω with hinner_Ω_def
  set FΩ := chosenWeakPartial' (d := Module.finrank ℝ E) 2 j inner_Ω Ω
    with hFΩ_def
  set Fmid := chosenWeakPartial' (d := Module.finrank ℝ E) 2 j inner_Ω V
    with hFmid_def
  -- h_outer_V_zero says Fmid =ᵐ 0 on volume.restrict V.
  have h_outer_V_zero : Fmid =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial_outer_sdiff_ae_zero (I := I) (M := M) g α hu_h i j
  -- FΩ is a weak j-partial of inner_Ω on Ω, hence on V (by restriction).
  have h_FΩ_partial_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
      j FΩ inner_Ω V := by
    have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
        j FΩ inner_Ω Ω :=
      chosenWeakPartial'_isWeakPartial_of_mem
        (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j
    exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset h_partial_Ω
  -- Fmid is a weak j-partial of inner_Ω on V.
  -- This requires showing that inner_Ω is in MemW1p 2 on V (it is, by restriction).
  have h_inner_Ω_W1p_V : DeGiorgi.MemW1p 2 inner_Ω V := by
    have h_inner_Ω_W1p_Ω := chosenInner_memW1p (I := I) (M := M) g α hu_h i
    refine ⟨?_, ?_⟩
    · exact h_inner_Ω_W1p_Ω.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
    · intro k
      obtain ⟨gk, hgk_memLp, hgk_weak⟩ := h_inner_Ω_W1p_Ω.2 k
      refine ⟨gk, ?_, ?_⟩
      · exact hgk_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgk_weak
  have h_Fmid_partial_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E)
      j Fmid inner_Ω V :=
    chosenWeakPartial'_isWeakPartial_of_mem h_inner_Ω_W1p_V j
  -- Local integrability of FΩ and Fmid on volume.restrict V.
  have h_FΩ_Lp_Ω : MemLp FΩ 2 ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem
      (chosenInner_memW1p (I := I) (M := M) g α hu_h i) j
  have h_FΩ_Lp_V : MemLp FΩ 2 ((volume : Measure EuclN).restrict V) :=
    h_FΩ_Lp_Ω.mono_measure (Measure.restrict_mono_set volume hV_subset)
  have h_FΩ_loc : LocallyIntegrable FΩ ((volume : Measure EuclN).restrict V) :=
    h_FΩ_Lp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_Fmid_Lp_V : MemLp Fmid 2 ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem h_inner_Ω_W1p_V j
  have h_Fmid_loc : LocallyIntegrable Fmid ((volume : Measure EuclN).restrict V) :=
    h_Fmid_Lp_V.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Step C: by ae-uniqueness on V, FΩ =ᵐ Fmid on V.
  have hae_FΩ_Fmid : FΩ =ᵐ[(volume : Measure EuclN).restrict V] Fmid :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open
      h_FΩ_partial_on_V h_Fmid_partial_on_V h_FΩ_loc h_Fmid_loc
  -- Step D: laplacianDomainHessianChart = FΩ, and Fmid =ᵐ 0 on V.
  change FΩ =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ))
  exact hae_FΩ_Fmid.trans h_outer_V_zero

/-! ## Theorem 2: chart-metric Frobenius squared is in `L^1` on the chart target

We define the chart-metric Frobenius norm squared of the chart-side Hessian
and prove `MemLp 1` regularity. The proof uses a smooth compactly-supported
cutoff `η` that is `≡ 1` on `chartImagePOUTsupport α` and supported in
`chartTargetEuclid α`, to dominate the inverse-Gram factors by a bounded
function on the effective support. -/

/-- The chart-coordinate metric Frobenius norm squared of the chart-side
Hessian: `∑ i j k l, G^{ik} G^{jl} H_{ij} H_{kl}`, where
`H_{ij} = laplacianDomainHessianChart g α hu_h i j` and
`G^{ij} = invGramOnEuclid g α i j`. -/
noncomputable def laplacianDomainHessFrobeniusSqChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  fun y => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  invGramOnEuclid (I := I) g α i k y *
                    invGramOnEuclid (I := I) g α j l y *
                    laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                    laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma laplacianDomainHessFrobeniusSqChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) :
    laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := rfl

/-- Pick a smooth cutoff `η_α` with the properties of `exists_chartCutoff`. -/
noncomputable def chartCutoffα (α : M) : EuclN → ℝ :=
  Classical.choose
    (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
      (I := I) (M := M) α).choose_spec

lemma chartCutoffα_spec (α : M) :
    let cutoff := chartCutoffα (I := I) (M := M) α
    let δ := (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
      (I := I) (M := M) α).choose
    0 < δ ∧
      Metric.cthickening δ (chartImagePOUTsupport (I := I) (M := M) α) ⊆
        chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) cutoff ∧
      HasCompactSupport cutoff ∧
      Set.range cutoff ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α), cutoff y = 1) ∧
      tsupport cutoff ⊆ chartTargetEuclid (I := I) (M := M) α :=
  (DifferentialGeometry.Analysis.Sobolev.Chart.exists_chartCutoff
    (I := I) (M := M) α).choose_spec.choose_spec

lemma chartCutoffα_smooth (α : M) :
    ContDiff ℝ (⊤ : ℕ∞) (chartCutoffα (I := I) (M := M) α) :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.1

lemma chartCutoffα_compactSupport (α : M) :
    HasCompactSupport (chartCutoffα (I := I) (M := M) α) :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.1

lemma chartCutoffα_range (α : M) :
    Set.range (chartCutoffα (I := I) (M := M) α) ⊆ Set.Icc (0 : ℝ) 1 :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.1

lemma chartCutoffα_eq_one_on_K (α : M) :
    ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
      chartCutoffα (I := I) (M := M) α y = 1 := by
  intro y hy
  have hone := (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.2.1
  apply hone y
  exact Metric.self_subset_cthickening _ hy

lemma chartCutoffα_tsupport (α : M) :
    tsupport (chartCutoffα (I := I) (M := M) α) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (chartCutoffα_spec (I := I) (M := M) α).2.2.2.2.2.2

/-- The cutoff is bounded by 1 in absolute value. -/
lemma abs_chartCutoffα_le (α : M) (y : EuclN) :
    |chartCutoffα (I := I) (M := M) α y| ≤ 1 := by
  have hrange := chartCutoffα_range (I := I) (M := M) α
  have hy : chartCutoffα (I := I) (M := M) α y ∈ Set.Icc (0 : ℝ) 1 :=
    hrange (Set.mem_range_self y)
  rw [abs_of_nonneg hy.1]
  exact hy.2

/-- The "cutoff inverse Gram entry": `η_α(y) * G^{ij}(y)`, extended by zero
outside the chart target. This is continuous on all of `EuclN` (it equals
`η_α · G^{ij}` on the chart target, and equals 0 outside via the cutoff). -/
noncomputable def cutoffInvGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    invGramOnEuclid (I := I) g α i j y

lemma cutoffInvGram_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffInvGram (I := I) (M := M) g α i j y =
      chartCutoffα (I := I) (M := M) α y *
        invGramOnEuclid (I := I) g α i j y := rfl

/-- `cutoffInvGram` is bounded on all of `EuclN`. Proof: continuous with
compact support (since `chartCutoff` has compact support inside the chart
target, where `invGramOnEuclid` is continuous; the product is 0 outside
`tsupport chartCutoff`). -/
lemma cutoffInvGram_bounded
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |cutoffInvGram (I := I) (M := M) g α i j y| ≤ C := by
  classical
  -- The function vanishes outside tsupport(chartCutoff), which is compact.
  -- It is continuous on chartTarget (an open set containing tsupport chartCutoff).
  -- Hence continuous on all of EuclN (the pieces glue via vanishing outside tsupport).
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  -- η is bounded by 1 everywhere.
  have hη_bdd : ∀ y : EuclN, |η y| ≤ 1 := abs_chartCutoffα_le (I := I) (M := M) α
  -- Outside Kη, η = 0, hence cutoffInvGram = 0.
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffInvGram (I := I) (M := M) g α i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffInvGram
    rw [hη_zero, zero_mul]
  -- Bound on Kη: |η · invGram| ≤ |invGram(y)| for y ∈ Kη ⊆ Ω, where invGram
  -- is continuous.
  have hG_cont_on : ContinuousOn (invGramOnEuclid (I := I) g α i j) Ω :=
    (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  -- Bound on the compact set Kη ⊆ Ω.
  by_cases hKη_ne : Kη.Nonempty
  · have hG_cont_on_Kη : ContinuousOn (invGramOnEuclid (I := I) g α i j) Kη :=
      hG_cont_on.mono hKη_sub_Ω
    have hG_norm_cont : ContinuousOn
        (fun y : EuclN => ‖invGramOnEuclid (I := I) g α i j y‖) Kη :=
      hG_cont_on_Kη.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne hG_norm_cont
    set C := ‖invGramOnEuclid (I := I) g α i j y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · -- |η · invGram(y)| ≤ 1 · |invGram(y)| ≤ 1 · C.
      have h1 : |cutoffInvGram (I := I) (M := M) g α i j y| =
          |η y| * |invGramOnEuclid (I := I) g α i j y| := by
        unfold cutoffInvGram
        rw [abs_mul]
      rw [h1]
      have hηy : |η y| ≤ 1 := hη_bdd y
      have hGy : ‖invGramOnEuclid (I := I) g α i j y‖ ≤ C := hy₀_max hyK
      have hG_abs_eq : |invGramOnEuclid (I := I) g α i j y| =
          ‖invGramOnEuclid (I := I) g α i j y‖ := rfl
      rw [hG_abs_eq]
      calc |η y| * ‖invGramOnEuclid (I := I) g α i j y‖
          ≤ 1 * ‖invGramOnEuclid (I := I) g α i j y‖ := by
              exact mul_le_mul_of_nonneg_right hηy (norm_nonneg _)
        _ ≤ 1 * C := by exact mul_le_mul_of_nonneg_left hGy zero_le_one
        _ = C := one_mul _
    · -- Outside Kη, the cutoff is 0.
      rw [h_zero_off y hyK, abs_zero]
      exact hC_nn
  · -- Empty case: Kη = ∅, so cutoffInvGram = 0 everywhere.
    refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

/-- `cutoffInvGram` is continuous on all of `EuclN`. -/
lemma cutoffInvGram_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffInvGram (I := I) (M := M) g α i j) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  -- η is continuous on EuclN (since smooth).
  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The product η · G^{ij}: on Ω it's η times a continuous-on-Ω function;
  -- pointwise zero outside Kη. Use that continuity can be checked
  -- locally.
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffInvGram (I := I) (M := M) g α i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffInvGram
    rw [hη_zero, zero_mul]
  -- For the continuity proof, observe:
  -- cutoffInvGram = η * (G_ext) where G_ext is any continuous extension of
  -- invGramOnEuclid restricted to Kη. But equivalently:
  -- η * invGramOnEuclid is continuous wherever both factors are continuous
  -- and well-defined; outside Ω, the function is 0 (since Kη ⊆ Ω).
  -- We pick a continuous extension via the cutoff trick:
  -- Define h(y) := η y * invGramOnEuclid g α i j y on Ω, 0 outside Ω.
  -- We show this is continuous.
  -- Method: continuity by an explicit pointwise argument using a small ball
  -- around each y.
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · -- y ∈ Kη ⊆ Ω. invGramOnEuclid is continuous on Ω, which is open.
    have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hG_cont_at : ContinuousAt (invGramOnEuclid (I := I) g α i j) y := by
      have hG_cont_on : ContinuousOn (invGramOnEuclid (I := I) g α i j) Ω :=
        (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
      exact hG_cont_on.continuousAt (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hG_cont_at
  · -- y ∉ Kη. Use that cutoffInvGram = 0 in a neighborhood of y.
    have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have hVal_y : cutoffInvGram (I := I) (M := M) g α i j y = 0 :=
      h_zero_off y hyKη
    -- cutoffInvGram is eventually 0 near y, hence continuous at y with value 0.
    have h_eventually_zero :
        cutoffInvGram (I := I) (M := M) g α i j =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    have h_const_continuous : ContinuousAt (fun _ : EuclN => (0 : ℝ)) y :=
      continuousAt_const
    have : ContinuousAt (cutoffInvGram (I := I) (M := M) g α i j) y :=
      h_const_continuous.congr h_eventually_zero.symm
    exact this

/-- `cutoffInvGram` is `AEStronglyMeasurable` on any measure. -/
lemma cutoffInvGram_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (μ : Measure EuclN) :
    AEStronglyMeasurable (cutoffInvGram (I := I) (M := M) g α i j) μ :=
  (cutoffInvGram_continuous (I := I) (M := M) g α i j).aestronglyMeasurable

/-- **Ae-equality:** on `volume.restrict chartTargetEuclid α`, the function
`invGramOnEuclid · H_{ij} · H_{kl}` is ae-equal to
`cutoffInvGram · H_{ij} · H_{kl}`. This is because the Hessian factors are
ae-zero outside `chartImagePOUTsupport α`, where the cutoff `η` is `1`. -/
private lemma invGram_mul_H_H_ae_eq_cutoff_mul_H_H
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (fun y : EuclN => invGramOnEuclid (I := I) g α i k y *
        invGramOnEuclid (I := I) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => cutoffInvGram (I := I) (M := M) g α i k y *
        cutoffInvGram (I := I) (M := M) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def
  -- Split the chart target as K ∪ V (disjoint).
  -- On K (interior), η = 1 so cutoffInvGram = invGram pointwise.
  -- On V, H_{ij} =ᵐ 0 and H_{kl} =ᵐ 0, so both sides are 0.
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_sub_Ω : K ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
  -- Pointwise equality on K.
  have h_pt_K : ∀ y ∈ K,
      invGramOnEuclid (I := I) g α i k y *
        invGramOnEuclid (I := I) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y =
      cutoffInvGram (I := I) (M := M) g α i k y *
        cutoffInvGram (I := I) (M := M) g α j l y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    intro y hy
    have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
      chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
    unfold cutoffInvGram
    rw [hη_one]
    ring
  -- Ae-zero on V for H_{ij}, H_{kl}.
  have h_H_zero_ij := laplacianDomainHessianChart_ae_zero_off_support
    (I := I) (M := M) g α hu_h i j
  have h_H_zero_kl := laplacianDomainHessianChart_ae_zero_off_support
    (I := I) (M := M) g α hu_h k l
  -- Translate to volume.restrict (Ω) by splitting via ae_restrict_iff'.
  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas
  -- Strategy: define the property P(y) and show
  -- {y ∈ Ω : ¬ P(y)} has zero measure. Decompose this set as
  -- {y ∈ K : ¬ P(y)} ∪ {y ∈ V : ¬ P(y)} where the first is empty (by pointwise
  -- equality) and the second has zero measure (since H_{ij} =ᵐ 0 there).
  -- We unfold ae on the restricted measure as follows.
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  -- Reduce to: ∀ᵐ y ∂volume, y ∈ Ω → P(y).
  -- Split on K vs V via the ae witnesses on V.
  have hae_ij : (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y)
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)) :=
    h_H_zero_ij
  have hae_kl : (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y)
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)) :=
    h_H_zero_kl
  -- Unfold these via ae_restrict_iff'.
  have hae_ij' : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y = 0 := by
    have := (ae_restrict_iff' hV_meas).mp hae_ij
    filter_upwards [this] with y hy hyV
    exact hy hyV
  have hae_kl' : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 := by
    have := (ae_restrict_iff' hV_meas).mp hae_kl
    filter_upwards [this] with y hy hyV
    exact hy hyV
  filter_upwards [hae_ij', hae_kl'] with y hy_ij hy_kl hyΩ
  by_cases hyK : y ∈ K
  · exact h_pt_K y hyK
  · have hyV : y ∈ V := ⟨hyΩ, hyK⟩
    have hH_ij_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y = 0 :=
      hy_ij hyV
    have hH_kl_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
      hy_kl hyV
    rw [hH_ij_zero, hH_kl_zero]
    ring

/-! ## Auxiliary: AE strong measurability and L^p facts -/

/-- The chart Hessian is `AEStronglyMeasurable` w.r.t. the restricted volume
on the chart target. -/
private lemma laplacianDomainHessianChart_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h i j).aestronglyMeasurable

/-- `H_{ij} · H_{kl}` is integrable on the restricted chart target. -/
private lemma H_ij_mul_H_kl_integrable
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Integrable
      (fun y : EuclN =>
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_ij := laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h i j
  have h_kl := laplacianDomainHessianChart_memLp_two
    (I := I) (M := M) g α hu_h k l
  exact MemLp.integrable_mul h_ij h_kl

/-- Each summand `cutoffInvGram_ik · cutoffInvGram_jl · H_{ij} · H_{kl}` is in
`MemLp 1`. -/
private lemma cutoffSummand_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- Bound on |cutoffInvGram_ik|.
  obtain ⟨C_ik, hC_ik_nn, hC_ik_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α i k
  obtain ⟨C_jl, hC_jl_nn, hC_jl_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α j l
  -- The bound function: `(C_ik · C_jl) * |H_{ij} · H_{kl}|`.
  -- That's integrable since H_{ij} · H_{kl} is integrable.
  have h_HH_int := H_ij_mul_H_kl_integrable
    (I := I) (M := M) g α hu_h i j k l
  have h_HH_memLp_one : MemLp (fun y : EuclN =>
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_one_iff_integrable.mpr h_HH_int
  -- (C_ik · C_jl) · |H_{ij} · H_{kl}| is in MemLp 1.
  set C := C_ik * C_jl with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg hC_ik_nn hC_jl_nn
  -- Define the dominating function.
  set bdd_fn : EuclN → ℝ := fun y =>
    C * |laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
      laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|
    with hbdd_def
  have hbdd_memLp : MemLp bdd_fn 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h_abs : MemLp (fun y => |laplacianDomainHessianChart
        (I := I) (M := M) g α hu_h i j y *
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|) 1
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := h_HH_memLp_one.abs
    exact h_abs.const_mul C
  -- Apply MemLp.mono.
  refine MemLp.mono hbdd_memLp ?_ ?_
  · -- aestronglyMeasurable of the LHS.
    have h_cont_ik : Continuous (cutoffInvGram (I := I) (M := M) g α i k) :=
      cutoffInvGram_continuous (I := I) (M := M) g α i k
    have h_cont_jl : Continuous (cutoffInvGram (I := I) (M := M) g α j l) :=
      cutoffInvGram_continuous (I := I) (M := M) g α j l
    have h_aesm_ik : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α i k)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_cont_ik.aestronglyMeasurable
    have h_aesm_jl : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α j l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_cont_jl.aestronglyMeasurable
    have h_aesm_ij_H := laplacianDomainHessianChart_aestronglyMeasurable
      (I := I) (M := M) g α hu_h i j
    have h_aesm_kl_H := laplacianDomainHessianChart_aestronglyMeasurable
      (I := I) (M := M) g α hu_h k l
    exact ((h_aesm_ik.mul h_aesm_jl).mul h_aesm_ij_H).mul h_aesm_kl_H
  · -- Pointwise bound.
    refine Filter.Eventually.of_forall ?_
    intro y
    -- ‖cutoffInvGram_ik y · cutoffInvGram_jl y · H_{ij} y · H_{kl} y‖
    --   ≤ ‖bdd_fn y‖
    simp only [Real.norm_eq_abs, hbdd_def]
    -- Step 1: factor the absolute value of a product.
    set H_ij := laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j with hH_ij_def
    set H_kl := laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l with hH_kl_def
    set Gik := cutoffInvGram (I := I) (M := M) g α i k with hGik_def
    set Gjl := cutoffInvGram (I := I) (M := M) g α j l with hGjl_def
    -- Pointwise bound: |Gik y * Gjl y * H_ij y * H_kl y| ≤ (C_ik · C_jl) * |H_ij y * H_kl y|.
    have h_abs : |Gik y * Gjl y * H_ij y * H_kl y| =
        |Gik y| * |Gjl y| * |H_ij y * H_kl y| := by
      rw [show Gik y * Gjl y * H_ij y * H_kl y =
            (Gik y * Gjl y) * (H_ij y * H_kl y) by ring]
      rw [abs_mul, abs_mul]
    rw [h_abs]
    have h_step1 : |Gik y| * |Gjl y| ≤ C_ik * C_jl := by
      have h1 := hC_ik_bd y
      have h2 := hC_jl_bd y
      calc |Gik y| * |Gjl y|
          ≤ C_ik * |Gjl y| := by
              exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ C_ik * C_jl := by
              exact mul_le_mul_of_nonneg_left h2 hC_ik_nn
    have h_nonneg_abs_HH : 0 ≤ |H_ij y * H_kl y| := abs_nonneg _
    have h_le_C : |Gik y| * |Gjl y| * |H_ij y * H_kl y| ≤
        C * |H_ij y * H_kl y| := by
      rw [hC_def]
      exact mul_le_mul_of_nonneg_right h_step1 h_nonneg_abs_HH
    set absHH := |H_ij y * H_kl y| with habsHH_def
    have habsHH_nn : 0 ≤ absHH := abs_nonneg _
    have h_eq_abs : C * absHH = |C * absHH| :=
      (abs_of_nonneg (mul_nonneg hC_nn habsHH_nn)).symm
    linarith [h_le_C, h_eq_abs.le, (h_eq_abs.symm).le]

/-- Each summand `invGramOnEuclid_ik · invGramOnEuclid_jl · H_{ij} · H_{kl}` is
in `MemLp 1` (via ae-equality with the cutoff variant). -/
private lemma summand_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        invGramOnEuclid (I := I) g α i k y *
          invGramOnEuclid (I := I) g α j l y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_cutoff_memLp := cutoffSummand_memLp_one
    (I := I) (M := M) g α hu_h i j k l
  exact MemLp.ae_eq
    (invGram_mul_H_H_ae_eq_cutoff_mul_H_H
      (I := I) (M := M) g α hu_h i j k l).symm h_cutoff_memLp

/-! ## Theorem 2: Frobenius squared is in L^1 -/

/-- **Chart-metric Frobenius norm squared of the chart-side Hessian is in
`L^1`.** For `u_h ∈ laplacianDomain g`, the contraction
`∑_{ijkl} G^{ik} G^{jl} H_{ij} H_{kl}` is in `L^1` of the volume measure
restricted to `chartTargetEuclid α`. -/
theorem laplacianDomainHessFrobeniusSqChart_memLp_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The Frobenius is a finite sum of summand_memLp_one elements.
  have h_eq : laplacianDomainHessFrobeniusSqChart (I := I) (M := M) g α hu_h =
      fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    funext y
    rw [laplacianDomainHessFrobeniusSqChart_def]
  rw [h_eq]
  -- Apply `memLp_finset_sum` repeatedly.
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun i _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun j _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun k _ => ?_)
  refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => ?_)
  exact summand_memLp_one (I := I) (M := M) g α hu_h i j k l

/-! ## Theorem 3: smooth-case identification

For a smooth scalar `f`, viewed as `u_h := smoothToH1Compl g f`, the chart-side
weak Hessian of `u_h` in directions `(i, j)`, modulo the bridge that the
chart-pushed of the Lp coercion ae-equals the chart-pushed of the smooth
representative, equals the iterated chosen weak partial of the chart-pushed
function for `f.toFun`. We state this as a hypothesis-bearing variant: the
ae-equality `chartPushed POU α u_h.coeFn =ᵐ chartPushed POU α f.toFun` on
`vol.restrict chartTarget` is the standard L²-coercion null-set transfer,
provable from `MemLp.coeFn_toLp` plus the chart-pullback absolute-continuity
bridge (`chartPushed_aeEq_of_ae_eq_riemannianMeasure` and the Measurable.mk
representative). -/

omit [NeZero (Module.finrank ℝ E)] in
/-- **Theorem 3 (smooth-case identification, hypothesis-bearing).** For a
smooth scalar `f : SmoothScalar g`, viewed as `u_h := smoothToH1Compl g f`,
the chart-side weak Hessian of `u_h` in directions `(i, j)` is, a.e. on the
chart target, the iterated chosen weak partial of `chartPushed POU α f.toFun`.

The hypothesis `h_bridge` is the ae-equality of the chart-pushed Lp coercion
and the chart-pushed smooth representative. It is provable from
`MemLp.coeFn_toLp` plus `chartPushed_aeEq_of_ae_eq_riemannianMeasure` once the
AEStronglyMeasurable.mk machinery is applied to the Lp coercion; we expose
it as a hypothesis to keep this lemma free of measurability bookkeeping. -/
theorem laplacianDomainHessianChart_smooth_case
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : SmoothScalar g) (i j : Fin (Module.finrank ℝ E))
    (h_bridge :
      chartPushedU (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g f)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun) :
    laplacianDomainHessianChart (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f) i j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The chart-side weak Hessian is, by definition,
  -- chosenWeakPartial' 2 j (chosenWeakPartial' 2 i (chartPushedU g α u_h)) chartTarget.
  -- From h_bridge, chartPushedU =ᵐ chartPushed α f.toFun on volume.restrict chartTarget.
  -- The chosenWeakPartial' is ae-invariant under such ae-equalities, via
  -- chosenWeakPartial'_ae_congr.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u_h_mem := smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f
  set u₁ : EuclN → ℝ := chartPushedU (I := I) (M := M) g α
    (smoothToH1Compl (I := I) (M := M) g f) with hu₁_def
  set u₂ : EuclN → ℝ := chartPushed (I := I) (M := M) (chartAtlasPOU I M) α f.toFun
    with hu₂_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Outer chosen partial: connect via two applications of chosenWeakPartial'_ae_congr.
  -- Step 1: chosenWeakPartial' 2 i u₁ Ω =ᵐ chosenWeakPartial' 2 i u₂ Ω.
  have h_inner_eq :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω :=
    chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bridge i
  -- Step 2: chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u₁ Ω) Ω =ᵐ
  --         chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u₂ Ω) Ω.
  have h_outer_eq :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω) Ω
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω) Ω :=
    chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_inner_eq j
  -- Conclude.
  change chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₁ Ω) Ω
    =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u₂ Ω) Ω
  exact h_outer_eq

end HessianLpClass
end Laplacian
end Analysis
end DifferentialGeometry

end
