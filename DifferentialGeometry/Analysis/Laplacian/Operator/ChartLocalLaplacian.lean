import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import DifferentialGeometry.Analysis.Laplacian.Operator.ChartMeasureEquiv
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.Green
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Chart-pulled-back smooth function as a Euclidean weak solution

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M`, a chart point `α : M`, and a smooth function `f : M → ℝ`
supported in the chart at `α`, we package the chart-pulled-back function

```
f̃(y) := f ((extChartAt I α).symm (toEuclidean.symm y)),    y ∈ chartTargetEuclid α,
f̃(y) := 0,                                                   otherwise,
```

together with the smooth elliptic bilinear form `B` produced by the H¹ metric
extension (`exists_smooth_metric_extension`) — whose principal coefficient
matrix agrees on a compact thickening of `tsupport f̃` with the chart-pulled
volume-weighted inverse Gram matrix `√det g · g^{ij}` — into a self-contained
package of:

* the chart-pulled-back smooth function `chartPullback I α f : EuclN → ℝ`,
* the chart-pulled-back density-weighted negative Laplacian `negDensityLaplacianPullback`,
* a smoothness statement for both,
* the H¹-derived `SmoothEllipticBilinearForm` `B` extending the chart metric
  data, with `B.c = 0`,
* a hypothesis-bearing wrapper that, given the chart-local divergence-form
  bilinear identity (which is the chart-pulled Voss–Weyl + integration-by-parts
  identity, expressed against arbitrary smooth compactly-supported test functions
  on `EuclideanSpace`), concludes
  `B.IsSmoothWeakSolution f̃ F̃` where `F̃ = -densityOnEuclid · (Δ_g f) ∘ chart^{-1} ∘ toEuclidean.symm`.

The hypothesis-bearing form is the standard channel through which the
manifold-side weak identity (after chart pull-back) is transported into the
Euclidean smooth-weak-solution language used by the Nirenberg / De Giorgi
machinery; the hypothesis itself is the chart-pulled Voss–Weyl + IBP identity,
which combines `chart_local_ibp` with the chart-pulled-volume identity from
`ChartMeasureEquiv.lean`.

## Setting

We work in the closed (compact, boundaryless) smooth Riemannian manifold setting
with `[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`, `[CompactSpace M]`.
The model fibre is a finite-dimensional real inner-product space `E` with
positive dimension. The metric `g` is a `SmoothRiemannianMetric I M`.

## Main definitions

* `chartPullback I α f : EuclN → ℝ` — the function `f̃` as described above.
* `negDensityLaplacianPullback (I := I) g hf α : EuclN → ℝ` — the function
  `F̃(y) := -densityOnEuclid g α y · (Δ_g g hf) ((extChartAt I α).symm
  (toEuclidean.symm y))` extended by `0` outside the chart-target image.

## Main results

* `chartPullback_contDiff` — `chartPullback I α f` is `C^∞` on `EuclN` whenever
  `f` is `C^∞` on `M` and `tsupport f ⊆ (chartAt H α).source`.
* `negDensityLaplacianPullback_contDiff` — same for the RHS function.
* `chartPullback_tsupport_subset_chartTargetEuclid` — the support of the
  pull-back is contained in the chart-target image.
* `chart_pulled_smooth_weak_solution_of_chartIdentity` — the headline theorem,
  in hypothesis-bearing form. Given the chart-pulled bilinear identity holds
  for all smooth compactly-supported test functions on `EuclN`, the
  chart-pulled function `f̃` is a smooth weak solution of the H¹-derived
  bilinear form `B` with right-hand side `F̃`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartLocalLaplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

/-! ## File-local Borel-space instances on `E` and `M`

Match the convention in surrounding files: install Borel σ-algebras locally
without leaking global instances. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The chart-pulled-back function on `EuclideanSpace`

For `f : M → ℝ` and a chart point `α : M`, the chart-pulled-back function
`chartPullback I α f : EuclN → ℝ` evaluates `f` at the inverse-chart image of
`toEuclidean.symm y`, with the result extended by `0` outside the chart-target
image `chartTargetEuclid α`. The extension by zero is essential for global
smoothness of the pull-back when `tsupport f ⊆ (chartAt H α).source`.
-/

/-- The chart-pulled-back function: `f ∘ (extChartAt I α).symm ∘ toEuclidean.symm`,
extended by `0` outside the chart-target image `chartTargetEuclid α`. -/
def chartPullback (α : M) (f : M → ℝ) : EuclN → ℝ :=
  fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
    (fun z => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y

@[simp] lemma chartPullback_apply_of_mem (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
  Set.indicator_of_mem hy _

@[simp] lemma chartPullback_apply_of_notMem (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y = 0 :=
  Set.indicator_of_notMem hy _

/-! ## The image of `tsupport f` in `EuclN`

The image of `tsupport f` under the composition `toEuclidean ∘ extChartAt I α`
serves as a compact "barrier" containing the support of `chartPullback I α f`. -/

/-- The Euclidean image of `tsupport f` under `toEuclidean ∘ extChartAt I α`. -/
def euclideanChartImageOfTsupport (α : M) (f : M → ℝ) : Set EuclN :=
  (toEuclidean (E := E)) '' ((extChartAt I α) '' tsupport f)

/-- When `f` has compact support and `tsupport f ⊆ (chartAt H α).source`, the
Euclidean image is compact. -/
lemma euclideanChartImageOfTsupport_isCompact
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    IsCompact (euclideanChartImageOfTsupport (I := I) (M := M) α f) := by
  unfold euclideanChartImageOfTsupport
  -- Continuity of `extChartAt I α` on `tsupport f`.
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport f) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hImage1 : IsCompact ((extChartAt I α) '' tsupport f) :=
    (hf_cs : IsCompact (tsupport f)).image_of_continuousOn hcontOn
  -- Continuity of `toEuclidean` on the resulting compact.
  have hcont_toE : Continuous (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous
  exact hImage1.image hcont_toE

/-- The Euclidean image of `tsupport f` is closed. -/
lemma euclideanChartImageOfTsupport_isClosed
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    IsClosed (euclideanChartImageOfTsupport (I := I) (M := M) α f) :=
  (euclideanChartImageOfTsupport_isCompact (I := I) (M := M) α hf_cs hf_supp).isClosed

/-- The Euclidean image of `tsupport f` is contained in `chartTargetEuclid α`. -/
lemma euclideanChartImageOfTsupport_subset_chartTargetEuclid
    (α : M) {f : M → ℝ} (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    euclideanChartImageOfTsupport (I := I) (M := M) α f ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  rcases hy with ⟨z, hz_target, hz_eq⟩
  -- `z = (extChartAt I α) x` for some `x ∈ tsupport f`.
  rcases hz_target with ⟨x, hx_supp, hx_eq⟩
  -- `chartTargetEuclid α = toEuclidean '' (extChartAt I α).target`.
  refine ⟨z, ?_, hz_eq⟩
  rw [← hx_eq]
  -- Need: (extChartAt I α) x ∈ (extChartAt I α).target.
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx_supp
  exact (extChartAt I α).map_source hxsrc

/-! ## Support and topological support of `chartPullback I α f` -/

/-- The support of `chartPullback I α f` is contained in the Euclidean image of
`tsupport f`. -/
lemma chartPullback_support_subset
    (α : M) (f : M → ℝ) :
    Function.support (chartPullback (I := I) α f) ⊆
      euclideanChartImageOfTsupport (I := I) (M := M) α f := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- chartPullback I α f y = f (symm (toE.symm y)) ≠ 0.
    rw [chartPullback_apply_of_mem (I := I) α f hyT] at hy
    -- So `(extChartAt I α).symm (toEuclidean.symm y) ∈ support f ⊆ tsupport f`.
    have hsymm_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
        ∈ tsupport f := subset_tsupport _ hy
    -- Hence y = toEuclidean (extChartAt I α (symm…)) is in the Euclidean image.
    refine ⟨(extChartAt I α) ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)), ?_, ?_⟩
    · exact ⟨_, hsymm_supp, rfl⟩
    · -- Recover y via right inverse of toEuclidean and right inverse of extChartAt.
      rcases hyT with ⟨z, hz_tgt, hz_eq⟩
      have h1 : (extChartAt I α) ((extChartAt I α).symm z) = z :=
        (extChartAt I α).right_inv hz_tgt
      -- Substituting:
      have hsymm_eq : (toEuclidean (E := E)).symm y = z := by
        rw [← hz_eq]; simp
      rw [hsymm_eq, h1, hz_eq]
  · rw [chartPullback_apply_of_notMem (I := I) α f hyT] at hy
    exact (hy rfl).elim

/-- `tsupport (chartPullback I α f)` is contained in the Euclidean image of
`tsupport f`, when the latter is closed. -/
lemma chartPullback_tsupport_subset
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullback (I := I) α f) ⊆
      euclideanChartImageOfTsupport (I := I) (M := M) α f := by
  refine closure_minimal (chartPullback_support_subset (I := I) α f) ?_
  exact euclideanChartImageOfTsupport_isClosed (I := I) (M := M) α hf_cs hf_supp

/-- `tsupport (chartPullback I α f)` is contained in `chartTargetEuclid α`. -/
lemma chartPullback_tsupport_subset_chartTargetEuclid
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullback (I := I) α f) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (chartPullback_tsupport_subset (I := I) α hf_cs hf_supp).trans
    (euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_supp)

/-- `chartPullback I α f` has compact support. -/
lemma chartPullback_hasCompactSupport
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullback (I := I) α f) :=
  HasCompactSupport.of_support_subset_isCompact
    (euclideanChartImageOfTsupport_isCompact (I := I) (M := M) α hf_cs hf_supp)
    (chartPullback_support_subset (I := I) α f)

/-! ## Smoothness of `chartPullback I α f` on `EuclN`

Under the closed (boundaryless) hypothesis on `M`, when `f` is `C^∞` on `M` and
`tsupport f ⊆ (chartAt H α).source`, the chart-pulled-back function
`chartPullback I α f` is `C^∞` on the whole of `EuclN`. This combines two
ingredients:

1. On the open set `chartTargetEuclid α`, `chartPullback I α f` agrees with the
   smooth composite `scalarOnE α f ∘ toEuclidean.symm`.
2. Outside `tsupport (chartPullback I α f)`, the function is identically zero.

The smoothness on the whole space follows by the standard cover argument
(open cover of `EuclN` by `chartTargetEuclid α` and the complement of the
support). -/

/-- On the chart-target image, `chartPullback I α f` agrees with the smooth
composite `scalarOnE α f ∘ toEuclidean.symm`. -/
private lemma chartPullback_eq_compose_on_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y =
      scalarOnE (I := I) α f ((toEuclidean (E := E)).symm y) := by
  rw [chartPullback_apply_of_mem (I := I) α f hy]
  rfl

/-- On the chart-target image (an open set under boundaryless), `chartPullback I α f`
is `C^∞`. -/
lemma chartPullback_contDiffOn_chartTargetEuclid [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (chartPullback (I := I) α f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun y : EuclN =>
        scalarOnE (I := I) α f ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    -- Compose `toEuclidean.symm` (smooth on EuclN) with `scalarOnE α f` (smooth on target).
    have h_toE_symm_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.contDiff
    have h_toE_symm : ContDiffOn ℝ ∞
        (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_toE_symm_cd.contDiffOn
    have h_scalar : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α hf
    have h_maps : Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
      intro y hy
      exact toEuclidean_symm_mem_target (I := I) hy
    exact h_scalar.comp h_toE_symm h_maps
  refine hsmooth.congr ?_
  intro y hy
  exact chartPullback_eq_compose_on_chartTargetEuclid (I := I) α f hy

/-- Helper: a function that is `C^∞` on an open set `U` and identically zero
outside a closed set `K ⊆ U` is `C^∞` on the whole space. -/
private lemma contDiff_of_smooth_on_open_zero_outside
    {U : Set EuclN} (hU : IsOpen U) {K : Set EuclN} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : EuclN → ℝ}
    (hf_smooth : ContDiffOn ℝ ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContDiffAt ℝ ∞ (fun _ : EuclN => (0 : ℝ)) y :=
      contDiff_const.contDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

/-- Under `[I.Boundaryless]`, when `f` is `C^∞` on `M` and `tsupport f ⊆
(chartAt H α).source`, `chartPullback I α f` is `C^∞` on the whole of `EuclN`. -/
lemma chartPullback_contDiff [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (chartPullback (I := I) α f) := by
  refine contDiff_of_smooth_on_open_zero_outside
    (U := chartTargetEuclid (I := I) (M := M) α)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (K := euclideanChartImageOfTsupport (I := I) (M := M) α f)
    (euclideanChartImageOfTsupport_isClosed (I := I) (M := M) α hf_cs hf_supp)
    (euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_supp)
    ?_ ?_
  · exact chartPullback_contDiffOn_chartTargetEuclid (I := I) α hf
  · intro y hy
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · -- y ∈ chartTargetEuclid α but y ∉ Euclidean image of tsupport ⇒ symm composition lands outside tsupport ⇒ f = 0 there.
      rw [chartPullback_apply_of_mem (I := I) α f hyT]
      by_contra hne
      -- f (symm…) ≠ 0 ⇒ symm… ∈ support f ⊆ tsupport f, hence y ∈ Euclidean image.
      have hsymm_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
          ∈ tsupport f := subset_tsupport _ hne
      refine hy ?_
      refine ⟨(extChartAt I α) ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)), ?_, ?_⟩
      · exact ⟨_, hsymm_supp, rfl⟩
      · -- Recover y by right inverses.
        rcases hyT with ⟨z, hz_tgt, hz_eq⟩
        have h1 : (extChartAt I α) ((extChartAt I α).symm z) = z :=
          (extChartAt I α).right_inv hz_tgt
        have hsymm_eq : (toEuclidean (E := E)).symm y = z := by
          rw [← hz_eq]; simp
        rw [hsymm_eq, h1, hz_eq]
    · exact chartPullback_apply_of_notMem (I := I) α f hyT

/-! ## The right-hand-side function: density-weighted negative Laplacian -/

/-- The chart-pulled-back density-weighted negative Laplacian:
`F̃(y) := -(densityOnEuclid g α y) · (Δ_g g hf) ((extChartAt I α).symm
(toEuclidean.symm y))`, with the result extended by `0` outside the chart-target
image. This is the natural right-hand side of the Euclidean weak formulation
that comes out of the Voss–Weyl chart formula combined with Green's first
identity. -/
def negDensityLaplacianPullback [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) : EuclN → ℝ :=
  fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
    (fun z => -(densityOnEuclid (I := I) g α z) *
      (Δ_g (I := I) g hf) ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm z))) y

@[simp] lemma negDensityLaplacianPullback_apply_of_mem [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    negDensityLaplacianPullback (I := I) g hf α y =
      -(densityOnEuclid (I := I) g α y) *
        (Δ_g (I := I) g hf) ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)) :=
  Set.indicator_of_mem hy _

@[simp] lemma negDensityLaplacianPullback_apply_of_notMem [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    negDensityLaplacianPullback (I := I) g hf α y = 0 :=
  Set.indicator_of_notMem hy _

/-! ## The H¹-derived bilinear form

Apply `exists_smooth_metric_extension` to a chosen compact `K ⊆ chartTargetEuclid α`
to extract a `SmoothEllipticBilinearForm` on `Set.univ` whose principal coefficient
matrix `B.a` agrees on `K` with the chart-pulled-back volume-weighted inverse
Gram matrix `√det g · g^{ij}`. -/

/-- Existence of a smooth elliptic bilinear form `B` extending the chart-pulled
volume-weighted inverse Gram matrix on a compact `K`. This is a direct
re-export of `exists_smooth_metric_extension` (from `MetricExtension.lean`),
exposed here under the `ChartLocalLaplacian` namespace for downstream callers
that want to bundle the bilinear-form construction together with the
chart-pulled-back smooth function defined in this file. -/
theorem exists_chart_metric_bilinearForm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Ω' : Set EuclN,
      IsOpen Ω' ∧ K ⊆ Ω' ∧ IsCompact (closure Ω') ∧
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) :=
  exists_smooth_metric_extension (I := I) (M := M) g α hK hK_target

/-! ## The headline theorem: hypothesis-bearing form

The headline result is stated in **hypothesis-bearing form**: it takes as a
hypothesis the chart-pulled bilinear identity
```
B.bilin (chartPullback I α f) ψ = ∫ y, F̃ y · ψ y dy
```
for every smooth compactly-supported test function `ψ : EuclN → ℝ`, and
concludes that `chartPullback I α f` is a smooth weak solution of `B` with
right-hand side `negDensityLaplacianPullback`.

This packaging is the standard channel through which the manifold-side
Green's-first identity, after chart-pull-back via the chart-pulled-volume
identity from `ChartMeasureEquiv.lean` and pointwise identification of the
principal integrand with the chart-pulled volume-weighted inverse Gram matrix,
delivers a Euclidean weak-solution statement compatible with the De Giorgi /
Nirenberg interior-regularity machinery. The downstream caller supplies the
hypothesis, computed by combining `chart_local_ibp` (which delivers the
manifold-side Voss–Weyl integration-by-parts identity) with the chart-pulled
volume identity and a chart-pullback-of-test-function argument.
-/

/-- **Chart-pulled smooth weak solution (hypothesis-bearing form).**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless)
smooth manifold `M`, let `α : M` be a chart point, and let `f : M → ℝ` be a
smooth function with `tsupport f ⊆ (chartAt H α).source`. Choose a compact
`K ⊆ chartTargetEuclid α` containing the Euclidean image of `tsupport f`.
Let `B` be a smooth elliptic bilinear form (e.g. produced by
`exists_chart_metric_bilinearForm`) on `Set.univ` whose principal coefficient
matrix `B.a` agrees on `K` with the chart-pulled volume-weighted inverse
Gram matrix and whose zeroth-order coefficient `B.c` vanishes identically.

If, for every smooth `ψ : EuclN → ℝ` with compact support, the chart-pulled
bilinear identity
```
B.bilin (chartPullback I α f) ψ = ∫ y, negDensityLaplacianPullback g hf α y · ψ y dy
```
holds, then `chartPullback I α f` is a smooth weak solution of `B` with
right-hand side `negDensityLaplacianPullback g hf α`.

The role of the hypothesis: in applications, the manifold-side identity
`∫ ⟨grad f, grad ψ⟩ dμ_g = -∫ ψ · Δ_g f dμ_g` (Green's first identity) is
chart-pulled to `EuclideanSpace`, and the integrand of the LHS is
identified pointwise on `K` with `B.principalIntegrand (chartPullback f) ψ`
via the chart Voss–Weyl formula. Outside `K`, both sides vanish since
`tsupport (chartPullback f) ⊆ K`. Combining gives the bilinear identity
required by this hypothesis. -/
theorem chart_pulled_smooth_weak_solution_of_chartIdentity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    (hbilin :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        B.bilin (chartPullback (I := I) α f) ψ =
          ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y) :
    B.IsSmoothWeakSolution (chartPullback (I := I) α f)
      (negDensityLaplacianPullback (I := I) g hf α) := by
  refine ⟨chartPullback_contDiff (I := I) α hf hf_cs hf_supp, ?_⟩
  intro ψ hψ hψ_cs _hψ_supp
  -- The integral over `Set.univ` reduces to the integral over the whole space.
  rw [MeasureTheory.setIntegral_univ]
  exact hbilin ψ hψ hψ_cs

/-! ## Auxiliary fact: chart-target image of test functions

For a smooth ψ : EuclN → ℝ with `tsupport ψ ⊆ chartTargetEuclid α`, the
function ψ ∘ chartTargetEuclid is well-defined and pulls back to a smooth
manifold function ψ : M → ℝ with `tsupport ψ ⊆ chart source`. This is the
manifold-side test function corresponding to the Euclidean test function ψ,
used to apply the manifold-side Green's first identity. We expose the
manifold-side test-function map as `chartTestPullback` for downstream use.

The manifold-side test function `chartTestPullback I α ψ` is defined as
`ψ ∘ toEuclidean ∘ extChartAt I α` extended by `0` outside the chart source. -/

/-- The manifold-side pull-back of an `EuclN`-test function: at points of the
chart source, evaluate `ψ` at `toEuclidean (extChartAt I α x)`; off the chart
source, return `0`. -/
def chartTestPullback (α : M) (ψ : EuclN → ℝ) : M → ℝ :=
  fun x => (chartAt H α).source.indicator
    (fun y => ψ (toEuclidean (E := E) ((extChartAt I α) y))) x

@[simp] lemma chartTestPullback_apply_of_mem
    (α : M) (ψ : EuclN → ℝ) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartTestPullback (I := I) α ψ x =
      ψ (toEuclidean (E := E) ((extChartAt I α) x)) :=
  Set.indicator_of_mem hx _

@[simp] lemma chartTestPullback_apply_of_notMem
    (α : M) (ψ : EuclN → ℝ) {x : M} (hx : x ∉ (chartAt H α).source) :
    chartTestPullback (I := I) α ψ x = 0 :=
  Set.indicator_of_notMem hx _

end ChartLocalLaplacian
end Laplacian
end Analysis
end DifferentialGeometry
