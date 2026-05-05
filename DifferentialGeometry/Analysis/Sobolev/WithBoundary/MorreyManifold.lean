import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanMorrey
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import DifferentialGeometry.Analysis.Sobolev.MorreyManifold
import DifferentialGeometry.Integral.Measure.Family

/-!
# Manifold Morrey embedding `W^{1,p}_chart(M) ↪ C^0(M)` for `p > n`,
half-space (with-boundary) variant — smooth-input case

This is the with-boundary parallel of `Analysis/Sobolev/MorreyManifold.lean`.
For a smooth manifold `M` modelled on the canonical Euclidean half-space
`EuclideanHalfSpace n` (`n ≥ 1`) with a smooth Riemannian metric `g`, and for
`p > n`, every smooth `u : M → ℝ` whose canonical-POU-localised chart-pushed
functions all have `tsupport` strictly in the open interior parts of the
chart targets satisfies a uniform-in-`u` sup-norm bound

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`

The constant `C ≥ 0` depends only on the metric, the canonical chart-atlas
partition of unity, and the exponent `p`.

## Strategy

The chart-based with-boundary Sobolev predicate `MemWkpChart` and norm
`wkpNormChart` are by construction the Dirichlet-half-space variants:
the chart-target carriers `chartTargetEuclid α = (extChartAt I α).target`
are half-space-relatively-open subsets of `EuclideanSpace ℝ (Fin n)`, and the
underlying iterated Sobolev predicate is the boundaryless `MemWkp` evaluated
on the open interior part `interiorHalfSpace Ω = Ω ∩ openHalfSpace`.

When the chart-pushed function `chartPushed ρ_α α u` has `tsupport` strictly
inside `interiorHalfSpace (chartTargetEuclid α)`, its smooth extension by
zero across the boundary face is globally smooth on `EuclideanSpace ℝ (Fin n)`.
We apply the boundaryless smooth Morrey
`smooth_morrey_sup_bound_uniform` on a Euclidean ball containing the
chart-pushed carrier, and sum the per-chart bounds over the canonical
chart-atlas partition of unity.

Two parallel uniform-in-`u` per-chart bounds are delivered:

1. **Sup-norm per-chart**: each chart-extended `chartSmoothExt α (ρ_α · u)`
   is bounded uniformly in `u` by `(C_α : ℝ) · (wkpNormChart g 1 p u).toReal`.
2. **Hölder pair per-chart**: each chart-extended function is Hölder
   continuous with exponent `1 - n/p` on the chart-pushed carrier, with
   modulus uniformly controlled by `(wkpNormChart g 1 p u).toReal`.

These per-chart bounds combine via the canonical chart-atlas POU sum
identity to give the manifold-level sup-norm and per-chart Hölder modulus.

## Main results

### Smooth manifold-level Morrey sup-bound (with boundary)

* `smooth_manifold_morrey_sup_bound_uniform_withBoundary` — for smooth
  `u : M → ℝ` whose chart-pushed `tsupport`s lie in the open interior parts
  of all chart targets, `‖u(x)‖ ≤ C · (wkpNormChart u).toReal` for every
  `x ∈ M`.

### Per-chart smooth Hölder modulus (with boundary)

* `smooth_manifold_morrey_holder_modulus_per_chart_withBoundary` — for each
  chart `α`, smooth `u : M → ℝ` with chart-pushed `tsupport` strictly
  interior, and `p > n`, the canonical-POU-localised function `(ρ_α · u)`
  satisfies a chart-α Hölder modulus on `tsupport ρ_α`.

### Manifold-level decomposition

* `norm_sub_le_sum_pou_diff_withBoundary` — re-export of the canonical-POU
  triangle inequality `‖u(x) - u(y)‖ ≤ ∑_α ‖(ρ_α · u)(x) - (ρ_α · u)(y)‖`.

## Scope note

The fully general manifold Morrey embedding `W^{1,p}_chart(M) ↪ C^0(M)`
extending to all measurable `u ∈ MemWkpChart` (rather than just smooth
inputs) requires a smooth-density argument in `MemWkpChart` (analogous to
the boundaryless `contMDiff_dense_in_WkpChart`). In the with-boundary
setting this requires the boundary-trace / mollification-near-boundary
infrastructure that is currently developed only chart-locally
(`WithBoundary/EuclideanDensity.lean`); a manifold-level density bridge
is a downstream concern and out of scope for the present file. The
smooth-input version delivered here, together with the per-chart Hölder
modulus, is the engine used by every downstream parabolic / elliptic
regularity application.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-! ## Local notation -/

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

/-! ## File-local Borel-space instances on `M`

`EuN = EuclideanSpace ℝ (Fin n)` already carries Mathlib's canonical
measurable structure (the `WithLp` measurable space coming from the Pi
structure). We do NOT install a separate Borel instance for `EuN` to avoid
typeclass conflicts with the existing infrastructure. We do install the
Borel instance for `M`. -/

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Smooth chart-extended function

Given `f : M → ℝ`, we define a function on `EuN := EuclideanSpace ℝ (Fin n)`
by setting

  `chartSmoothExt α f y = f ((extChartAt I α).symm y)` if `y ∈ chartTarget`,
                         `0` otherwise.

When `f` is smooth on `M` and its tsupport lies in the chart source, the
extended function on `EuN` is smooth on the open interior part
`interiorHalfSpace (chartTarget) = chartTarget ∩ openHalfSpace`. To make
it smooth on ALL of `EuN`, we will additionally require that its tsupport
in `EuN` lies inside `interiorHalfSpace (chartTarget)` (equivalently:
strictly above the boundary face). -/

/-- The chart-extended function on `EuN`: equals `f ∘ (extChartAt I α).symm`
on the chart target, and `0` outside. -/
def chartSmoothExt (α : M) (f : M → ℝ) : EuN → ℝ := by
  classical
  exact fun y =>
    if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y =
      f ((extChartAt I_hs α).symm y) := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = f ((extChartAt I_hs α).symm y)
  rw [if_pos hy]

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = 0
  rw [if_neg hy]

/-! ## On the chart-target image, `chartSmoothExt` agrees with `chartPushed`. -/

omit [IsManifold I_hs ∞ M] in
/-- On the chart target, `chartSmoothExt α (ρ_α · u)` agrees pointwise with
`chartPushed ρ α u`. -/
private lemma chartSmoothExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) y =
      chartPushed (n := n) (M := M) ρ α u y := by
  classical
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hy]
  unfold chartPushed
  rfl

/-! ## Smoothness of `chartSmoothExt α f` on the open interior part

When `f` is smooth on `M` and its tsupport is in the chart source, the
extension equals `f ∘ extChartAt.symm` on the chart target and zero
outside, hence smooth on `interiorHalfSpace (chartTarget)` (open part)
and smooth outside the closure of the carrier. -/

private lemma image_extChartAt_tsupport_compact_subset_target
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    IsCompact ((extChartAt I_hs α) '' (tsupport f)) ∧
      (extChartAt I_hs α) '' (tsupport f) ⊆ (extChartAt I_hs α).target := by
  classical
  have h_supp_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_supp_ext_src : tsupport f ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  have h_cont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
    (continuousOn_extChartAt α).mono h_supp_ext_src
  refine ⟨h_supp_compact.image_of_continuousOn h_cont, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (h_supp_ext_src hx)

private lemma chartSmoothExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ (extChartAt I_hs α).target
  · rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hy_target]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I_hs α).symm y ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hy_eq : (extChartAt I_hs α) ((extChartAt I_hs α).symm y) = y :=
      (extChartAt I_hs α).right_inv hy_target
    refine ⟨(extChartAt I_hs α).symm y, hsymm_in_supp, hy_eq⟩
  · exact chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy_target

private lemma hasCompactSupport_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hyK

/-- `tsupport (chartSmoothExt α f) ⊆ extChartAt α image of tsupport f`. -/
private lemma tsupport_chartSmoothExt_subset
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    tsupport (chartSmoothExt (n := n) (M := M) α f) ⊆
      (extChartAt I_hs α) '' (tsupport f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (chartSmoothExt (n := n) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact chartSmoothExt_eq_zero_off_image_tsupport
      (n := n) (M := M) α (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

/-! ## Smoothness on the open interior part

The extended function `chartSmoothExt α f` agrees on the chart target with
`f ∘ (extChartAt I α).symm`, which is `ContDiffOn ℝ ∞` on the (half-space-
relatively-open) chart target. Restricted to the open interior part
`chartTarget ∩ openHalfSpace`, it is `ContDiffOn ℝ ∞`, and on points
in the open interior part the within-derivative coincides with the
ordinary Fréchet derivative (since the open interior part is a
neighborhood of every interior point). -/

private lemma contDiffOn_chartSmoothExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuN => f ((extChartAt I_hs α).symm y))
        (extChartAt I_hs α).target := by
  classical
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I_hs) α hf

/-! ## Strictly interior tsupport for the chart-pushed function

The smoothness of the extension by 0 across the boundary face requires
that the chart-pushed function has `tsupport` strictly inside the open
interior part of the chart target. We expose the predicate explicitly. -/

/-- Predicate on a smooth `f : M → ℝ`: the chart-pushed image of `tsupport f`
under `extChartAt I α` lies strictly inside the open interior part of
the chart target. -/
def chartSmoothExtInteriorSupport
    (α : M) (f : M → ℝ) : Prop :=
  (extChartAt I_hs α) '' (tsupport f) ⊆
    DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

private lemma chartSmoothExtInteriorSupport_image_subset_interior
    {α : M} {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    (extChartAt I_hs α) '' (tsupport f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨?_, h_int ⟨x, hx, rfl⟩⟩
  -- y ∈ (extChartAt I α).target
  have h_src : x ∈ (extChartAt I_hs α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  exact (extChartAt I_hs α).map_source h_src

/-! ## Smoothness of `chartSmoothExt α f` on `EuN` for strictly-interior tsupport -/

private lemma contDiffAt_chartSmoothExt_of_mem_interior_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) {y : EuN}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  -- The interior part is open in EuN.
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  -- y is in the open interior part, which is contained in chartTarget.
  have hy_target : y ∈ (extChartAt I_hs α).target := hy.1
  -- contDiffOn for f ∘ extChartAt.symm at y on chartTarget.
  have hContDiffOn := contDiffOn_chartSmoothExt_formula (n := n) (M := M) α hf
  -- Within-contDiff at y on chartTarget.
  have h_within : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (extChartAt I_hs α).target y := hContDiffOn y hy_target
  -- The interior part is open and contained in chartTarget, so we can extract
  -- contDiffAt from a neighborhood.
  have hInt_sub : DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α) ⊆ (extChartAt I_hs α).target := by
    intro z hz
    exact hz.1
  -- ContDiffWithinAt on chartTarget at y implies ContDiffWithinAt on interior part at y.
  have h_within_int : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) y :=
    h_within.mono hInt_sub
  -- The interior part is a neighborhood of y, so contDiffWithinAt becomes contDiffAt.
  have h_contDiffAt : ContDiffAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y)) y :=
    h_within_int.contDiffAt (hOpen.mem_nhds hy)
  -- Use congr on a neighborhood: chartSmoothExt α f = f ∘ extChartAt.symm
  -- on the open interior part (which contains a neighborhood of y).
  apply h_contDiffAt.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hz.1]

private lemma contDiffAt_chartSmoothExt_of_notMem_image_tsupport
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I_hs α).source := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hf_supp hx
    have hcont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    exact hf_compact.image_of_continuousOn hcont
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuN => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hz

private lemma contDiff_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  by_cases hyK : y ∈ K
  · -- y ∈ K = image of tsupport f. By interior-support hypothesis, K ⊆ interior part.
    have hy_int : y ∈
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) hf_supp h_int hyK
    exact contDiffAt_chartSmoothExt_of_mem_interior_target
      (n := n) (M := M) α hf hy_int
  · -- y ∉ K. The function vanishes in a neighborhood of y.
    have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
    exact contDiffAt_chartSmoothExt_of_notMem_image_tsupport
      (n := n) (M := M) α hf_supp hf_compact hyK

/-! ## Smoothness of `chartSmoothExt α (ρ_α · u)` for smooth `u : M → ℝ` -/

omit [IsManifold I_hs ∞ M] in
private lemma tsupport_pou_mul_subset_chart_source
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      (chartAt (EuclideanHalfSpace n) α).source := by
  have h1 : tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  exact h1.trans (hρ α)

private lemma contDiff_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I_hs, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact contDiff_chartSmoothExt (n := n) (M := M) α hf_smooth hf_supp h_int

private lemma hasCompactSupport_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (u : M → ℝ) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact hasCompactSupport_chartSmoothExt (n := n) (M := M) α hf_supp

/-! ## Compact support set independent of `u`

For the canonical chart-atlas POU `chartAtlasPOU I_hs M`, the carrier
`extChartAt I α '' tsupport (ρ_α : M → ℝ)` is a compact subset of the
chart target, depending on `α` but not on `u`. We bound the chart-pushed
carrier of `(ρ_α · u)` by this carrier and pick a Euclidean ball
containing it. -/

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The compact support carrier in `EuN`: the `extChartAt I α` image of
`tsupport ρ_α` for the canonical POU weight `ρ_α`. -/
private def chartCarrier (α : M) : Set EuN :=
  (extChartAt I_hs α) ''
    (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ))

private lemma chartCarrier_isCompact (α : M) :
    IsCompact (chartCarrier (n := n) (M := M) α) := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  have hcont_ext : ContinuousOn (extChartAt I_hs α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_src
  exact hTα_compact.image_of_continuousOn hcont_ext

private lemma chartCarrier_subset_chartTarget (α : M) :
    chartCarrier (n := n) (M := M) α ⊆ (extChartAt I_hs α).target := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (hTα_ext_src hx)

/-- A radius `R_α` such that `chartCarrier α ⊆ Metric.ball 0 (R_α / 2)` and
`R_α > 0`. -/
private noncomputable def chartRadius (α : M) : ℝ :=
  (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) * 2 + 1

private lemma chartRadius_pos (α : M) : 0 < chartRadius (n := n) (M := M) α := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  linarith [h.1]

private lemma chartCarrier_subset_half_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  have h1 : 0 < (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) := h.1
  have h2 : chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN)
        (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
          0 (0 : EuN)).choose) := h.2
  refine h2.trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h_ineq : (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) ≤
      (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
        0 (0 : EuN)).choose * 2 + 1) / 2 := by
    linarith
  linarith

private lemma chartCarrier_subset_full_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α) := by
  refine (chartCarrier_subset_half_ball (n := n) (M := M) α).trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h := chartRadius_pos (n := n) (M := M) α
  linarith

/-! ## Per-chart smooth sup bound on `chartSmoothExt α (ρ_α · u)`

Under the strict-interior tsupport hypothesis on the chart-pushed function,
the chart-extended `chartSmoothExt α (ρ_α · u)` is `ContDiff ℝ ⊤` on
`EuN = EuclideanSpace ℝ (Fin n)`. The boundaryless smooth Morrey applies
on a Euclidean ball containing the (compact) chart-pushed carrier. -/

/-- Predicate version: the canonical-POU chart-pushed image of
`(ρ_α · u)` has tsupport strictly inside the open interior part of the
chart target, for every chart `α`. -/
def AllChartsInteriorSupport (u : M → ℝ) : Prop :=
  ∀ α : M,
    chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)

/-- For smooth `u : M → ℝ` whose canonical POU localisation has chart-
pushed `tsupport` strictly inside the open interior part of every chart
target, `chartSmoothExt α (ρ_α · u)` is supported in `chartCarrier α`. -/
private lemma tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
    (α : M) (u : M → ℝ) :
    tsupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) ⊆
      chartCarrier (n := n) (M := M) α := by
  classical
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  -- tsupport (ρ_α · u) ⊆ Tα.
  have h_pou_supp_sub_tα : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ Tα := by
    have h_eq : (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_pou_supp_chart_src : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    h_pou_supp_sub_tα.trans hTα_chart_src
  have hstep := tsupport_chartSmoothExt_subset (n := n) (M := M) α (f :=
    fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) h_pou_supp_chart_src
  refine hstep.trans ?_
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h_pou_supp_sub_tα hx, rfl⟩

/-- The function `chartSmoothExt α (ρ_α · u)` vanishes outside
`Metric.ball 0 (chartRadius α / 2)`. -/
private lemma chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∉ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)) :
    chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) y = 0 := by
  by_contra hne
  apply hy
  -- y ∈ support → y ∈ tsupport ⊆ chartCarrier α ⊆ ball 0 (R/2).
  have h_in_supp : y ∈ Function.support (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := Function.mem_support.mpr hne
  have h_in_tsupport := subset_tsupport _ h_in_supp
  exact chartCarrier_subset_half_ball (n := n) (M := M) α
    (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
      h_in_tsupport)

/-! ## Smooth sup bound on `chartSmoothExt α (ρ_α · u)` via the boundaryless
Morrey

Under the strict-interior tsupport hypothesis the chart-extended function
is smooth on `EuN`. The boundaryless smooth Morrey applies on a Euclidean
ball containing the chart-pushed carrier. -/

private lemma chartSmoothExt_morrey_sup_uniform
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          ((eLpNorm (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
           (eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (n := n) (M := M) α := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_sup_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := chartRadius (n := n) (M := M) α) hR_pos
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int y
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    have : ContDiff ℝ ∞ f := hf_smooth
    exact this
  by_cases hy_half : y ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · -- f y = 0, so LHS = 0.
    have hf_y_zero : f y = 0 :=
      chartSmoothExt_pou_mul_eq_zero_off_half_ball (n := n) (M := M) α u hy_half
    rw [hf_y_zero, norm_zero]
    -- RHS ≥ 0.
    have h_nn1 : 0 ≤ (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_nn2 : 0 ≤ (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_RHS_nn : 0 ≤ C *
        ((eLpNorm f (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
         (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
      apply mul_nonneg hC_nn
      linarith
    exact h_RHS_nn

/-! ## Indicator-style equalities for the eLpNorm of `chartSmoothExt α (ρ_α · u)`

The chart-extended function vanishes off `chartCarrier α`. So the eLpNorm
on a ball containing the carrier equals the eLpNorm on the chart target
interior part (open). -/

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] in
private lemma chartSmoothExt_eq_zero_off_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 :=
  chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy

/-- For a function `h` with `tsupport h ⊆ K` and `K` closed, `fderiv h = 0`
outside `K`. -/
private lemma fderiv_eq_zero_off_tsupport_subset_closed
    {h : EuN → ℝ} {K : Set EuN} (hK_closed : IsClosed K)
    (hh_supp : tsupport h ⊆ K) {y : EuN} (hy : y ∉ K) :
    fderiv ℝ h y = 0 := by
  have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (hh_supp hyt)
  have h_compl : Kᶜ ∈ 𝓝 y := hK_closed.isOpen_compl.mem_nhds hy
  have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_compl ?_
    intro z hz
    have hz_off_tsupp : z ∉ tsupport h := fun hzt => hz (hh_supp hzt)
    exact image_eq_zero_of_notMem_tsupport hz_off_tsupp
  rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
  simp

/-- The full-space eLpNorm of `chartSmoothExt α (ρ_α · u)` equals the
eLpNorm restricted to a ball containing the carrier. -/
private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  -- For y ∉ BR, h y = 0. So h has tsupport in K ⊆ BR.
  have h_eq_BR : h = BR.indicator h := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hyK (hK_supp hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q (volume.restrict BR)
      = eLpNorm (BR.indicator h) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm h q volume := by rw [← h_eq_BR]

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_supp hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]

/-! ## Bridge between `chartSmoothExt α (ρ_α · u)` and `chartPushed ρ α u`

On the open interior part of the chart target, the chart-extended
function and the chart-pushed function agree pointwise. Since the
boundary face is a measure-zero subset of the chart target, the two
agree a.e. on the interior part. -/

omit [CompactSpace M] in
/-- `chartSmoothExt α (ρ_α · u)` and `chartPushed ρ α u` agree a.e. on
`volume.restrict (interiorHalfSpace (chartTargetEuclid α))`. -/
private lemma chartSmoothExt_ae_eq_chartPushed_interior
    (α : M) (u : M → ℝ) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u := by
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  refine (MeasureTheory.ae_restrict_iff' hOpen.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartSmoothExt_eq_chartPushed_on_target
    (n := n) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u hy.1

/-- The eLpNorm of `chartSmoothExt α (ρ_α · u)` on the interior part of the
chart target equals the eLpNorm of `chartPushed ρ α u` there. -/
private lemma eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) =
      eLpNorm (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) :=
  eLpNorm_congr_ae (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

/-! ## eLpNorm of `chartSmoothExt α (ρ_α · u)` on `B(0, R_α)` equals the
eLpNorm on the open interior part

When the chart-pushed `tsupport` lies strictly inside the open interior
part, both quantities equal the full-space eLpNorm and the per-chart
half-space norm `wkpNormHalfSpace 1 p u (chartTargetEuclid α)` controls them. -/

private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  -- Strategy: both equal eLpNorm h q volume.
  -- LHS = full-space (we already proved this when carrier ⊆ ball).
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  -- Now we need: eLpNorm h q volume = eLpNorm h q (volume.restrict (interior part)).
  -- Since h = 0 outside `extChartAt α image of tsupport (ρ_α · u)` (interior subset).
  -- We show h has tsupport in the interior part (using h_int hypothesis).
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  -- We need: h has tsupport in IntΩ.
  -- This follows from: tsupport h ⊆ chartCarrier α and chartCarrier α refers to ρ_α (not ρ_α · u).
  -- However the strict-interior hypothesis is on the chart-pushed (ρ_α · u), not ρ_α alone.
  -- Re-prove tsupport via the strict-interior hypothesis on (ρ_α · u).
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  -- Now use indicator argument: h = 0 outside tsupport h, in particular outside IntΩ.
  have h_eq_IntΩ : h = IntΩ.indicator h := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q volume
      = eLpNorm (IntΩ.indicator h) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm h q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  have hK_closed_int : IsClosed (tsupport h) := isClosed_tsupport _
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_IntΩ : fnNorm = IntΩ.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      have h_fderiv_zero : fderiv ℝ h y = 0 := by
        have h_compl : (tsupport h)ᶜ ∈ 𝓝 y :=
          hK_closed_int.isOpen_compl.mem_nhds hy_off_tsupp
        have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
          refine Filter.eventuallyEq_of_mem h_compl ?_
          intro z hz
          exact image_eq_zero_of_notMem_tsupport hz
        rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
        simp
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q volume
      = eLpNorm (IntΩ.indicator fnNorm) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm fnNorm q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

/-! ## Bound `eLpNorm chartSmoothExt q (B(0, R_α))` by `wkpNormChart`

Given the indicator-style equality with the eLpNorm on the open interior
part, and the ae-equality between `chartSmoothExt` and `chartPushed`,
the eLpNorm reduces to the per-chart half-space norm
`wkpNormHalfSpace 0 q (chartPushed) (chartTargetEuclid α)`. The latter
is bounded by the chart-based norm `wkpNormChart g 1 q u`. -/

private lemma eLpNorm_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  rw [eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (n := n) (M := M) α u q]
  -- Now the LHS is eLpNorm (chartPushed) q (volume.restrict IntΩ).
  -- The RHS is wkpNormChart u, defined as a tsum over β of wkpNormHalfSpace 1 q (chartPushed β).
  -- For the specific α, wkpNormHalfSpace 0 q ≤ wkpNormHalfSpace 1 q (since order-zero norm is included).
  -- So we'd need to first show LHS ≤ wkpNormHalfSpace 1 q (chartPushed α) (chartTargetEuclid α),
  -- then ≤ tsum.
  -- LHS = wkpNormHalfSpace 0 q (chartPushed α) (chartTargetEuclid α)
  --     ≤ wkpNormHalfSpace 1 q (chartPushed α) (chartTargetEuclid α)
  --     ≤ tsum α, ... = wkpNormChart u.
  set Ω : Set EuN := chartTargetEuclid (n := n) (M := M) α with hΩ_def
  have h_zero_eq : eLpNorm (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 0 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero]
  rw [h_zero_eq]
  -- wkpNormHalfSpace 0 q ≤ wkpNormHalfSpace 1 q.
  have h_le_succ : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) 0 q
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    -- This is wkpNorm 0 q ≤ wkpNorm 1 q on interiorHalfSpace Ω.
    -- Use the wkpNorm_eq_sum decomposition.
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 0 q,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q]
    rw [Finset.sum_range_one]
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    rw [show Finset.range 2 = {0, 1} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    refine le_add_of_nonneg_right ?_
    exact zero_le _
  refine h_le_succ.trans ?_
  -- Now ≤ tsum.
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-! ## Per-partial gradient bound for `chartSmoothExt α (ρ_α · u)`

We bound the L^p norm of the gradient `‖fderiv ℝ f‖` by `n * wkpNormChart`.
The key step uses the equality of classical Fréchet partials with the
chosen weak partial on the open interior part. -/

/-- `‖w‖ ≤ ∑ i, ‖w i‖` in `EuclideanSpace`. -/
private lemma euN_norm_le_sum_components_norms (w : EuN) :
    ‖w‖ ≤ ∑ i : Fin n, ‖w i‖ := by
  classical
  have h_w_sum :
      w = ∑ i : Fin n, EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

/-- `‖fderiv ℝ ψ y‖ = ‖(WithLp.toLp 2 (...components...))‖` for ψ : EuN → ℝ. -/
private lemma norm_fderiv_eq_norm_partials_local
    {ψ : EuN → ℝ} (y : EuN) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : EuN)‖ := by
  classical
  set v : EuN :=
    (InnerProductSpace.toDual ℝ EuN).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuN) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin n =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

/-- For ψ : EuN → ℝ, `‖fderiv ℝ ψ y‖ ≤ ∑ i, ‖(fderiv ℝ ψ y) (e_i)‖`. -/
private lemma norm_fderiv_le_sum_partials_local
    (ψ : EuN → ℝ) (y : EuN) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin n, ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
  rw [norm_fderiv_eq_norm_partials_local (n := n) y]
  refine (euN_norm_le_sum_components_norms _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

/-- For smooth `f` with compact support, `eLpNorm (norm fderiv f) ≤ ∑_i eLpNorm partial_i f`. -/
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuN}
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin n,
      AEStronglyMeasurable
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuN,
      ‖fderiv ℝ f z‖ ≤ ∑ i : Fin n,
        ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local f z
  have h_step1 : eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      eLpNorm (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ f z‖‖ = ‖fderiv ℝ f z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin n,
          fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

/-- The classical partial of a smooth `f`, compactly supported in open `Ω`,
agrees a.e. with `chosenWeakPartial' p i f Ω`. -/
private lemma classical_partial_ae_eq_chosenWeakPartial_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω)
    (i : Fin n) :
    (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω := by
  classical
  have hf_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := n) 1 q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := n) hΩ_open hf_smooth hf_compact hf_supp hq_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := n) q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
      (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

/-- For smooth `f` with compact support inside open `Ω`, the eLpNorm of
`‖fderiv ℝ f‖` is bounded by `n * wkpNorm 1 q f Ω`. -/
private lemma eLpNorm_norm_fderiv_le_n_mul_wkpNorm
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q (volume.restrict Ω) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    (q := q) hq_one (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin n,
      eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
        q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local
      hq_one hΩ_open hf_smooth hf_compact hf_supp i)
  have h_step1 :
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin n,
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := n) q j β f Ω)
              q (volume.restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω) q (volume.restrict Ω)) =
        ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin n,
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := n) q 1 β f Ω) q (volume.restrict Ω) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
            q (volume.restrict Ω) := by
      intro β
      have hit :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω := by
        rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
        simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin n) ≃ Fin n :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
          q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
          q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q f Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le _
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < n := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((n : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
    (d := n) 1 q f Ω = 1 *
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := n) 1 q f Ω from
    (one_mul _).symm]
  gcongr

/-! ## Bound the gradient eLpNorm of `chartSmoothExt α (ρ_α · u)` by `n · wkpNormChart`

By the eLpNorm-on-ball-equals-eLpNorm-on-interior identity, the gradient
eLpNorm reduces to the eLpNorm on the open interior part. The smooth
function `chartSmoothExt α (ρ_α · u)` is supported in
`extChartAt α image of tsupport (ρ_α · u)`, which by the strict-interior
hypothesis lies inside the open `interiorHalfSpace (chartTargetEuclid α)`.
Apply the previous lemma with `Ω = interiorHalfSpace (chartTargetEuclid α)`. -/

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := n) 1 q
          (chartSmoothExt (n := n) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x))
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) := by
  classical
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  set Ω : Set EuN := DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
    (chartTargetEuclid (n := n) (M := M) α) with hΩ_def
  have hΩ_open : IsOpen Ω :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  have hf_compact : HasCompactSupport f := by
    rw [hf_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
  -- tsupport f ⊆ Ω, by strict-interior hypothesis on chart-pushed.
  have hf_supp : tsupport f ⊆ Ω := by
    rw [hf_def, hΩ_def]
    set ff : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hff_def
    have hff_supp_chart_src : tsupport ff ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport ff) ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := ff) hff_supp_chart_src (h_int α)
    have h1 : tsupport (chartSmoothExt (n := n) (M := M) α ff) ⊆
        (extChartAt I_hs α) '' (tsupport ff) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hff_supp_chart_src
    exact h1.trans hint_image
  exact eLpNorm_norm_fderiv_le_n_mul_wkpNorm hq_one hΩ_open hf_smooth_top hf_compact hf_supp

/-- The Euclidean wkpNorm of `chartSmoothExt α (ρ_α · u)` on the interior part
equals that of `chartPushed ρ α u`. -/
private lemma wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := n) 1 q
        (chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x))
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := n) hq_one
    (interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

/-- The Euclidean half-space wkpNormHalfSpace of `chartPushed ρ α u` at chart α
is bounded by `wkpNormChart u`. -/
private lemma wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

/-- Bound `eLpNorm fderiv chartSmoothExt q (B(0, R_α))` by `n · wkpNormChart`. -/
private lemma eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  refine (eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    (n := n) (M := M) hq_one hu h_int α).trans ?_
  rw [wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    (n := n) (M := M) hq_one α u]
  gcongr
  -- wkpNorm 1 q (chartPushed) (interiorHalfSpace) = wkpNormHalfSpace 1 q (chartPushed) (chartTargetEuclid)
  -- ≤ wkpNormChart u.
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
    wkpNormChart (n := n) (M := M) g 1 q u
  exact wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (n := n) (M := M) g α u

/-! ## Per-chart smooth Morrey bound on the chart-pushed value

Combining the per-chart sup bound `chartSmoothExt_morrey_sup_uniform` with
the indicator-style equalities and the L^p bounds, we obtain a uniform-
in-`u` per-chart sup bound:

  `‖chartSmoothExt α (ρ_α · u) y‖ ≤ C_α · (wkpNormChart u).toReal`

for all `y : EuN`, with `C_α` depending on `α, g, p, n`. -/

private lemma per_chart_smooth_sup_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast NeZero.pos n
    have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_sup_uniform (n := n) (M := M) α hp
  refine ⟨Cmorrey * (1 + (n : ℝ)), ?_, ?_⟩
  · have hd_nn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  · intro u hu h_int y
    have hbound_y := hbound hu h_int y
    set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
    have hLp_bd := eLpNorm_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g h_int α (ENNReal.ofReal p)
    have hgrad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g hp_enn_one hu h_int α
    have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
      -- We need MemWkpChart for u; we'll bound by ⊤ directly using the per-chart finiteness.
      -- But MemWkpChart_of_smooth is not available; since u is smooth and POU sums to 1,
      -- the per-chart half-space norm is finite if chartPushed has compact support and
      -- tsupport in interior. For the manifold case, the canonical POU has finitely many
      -- nonzero charts.
      -- Use: MemWkpHalfSpace iff MemWkp on interior. For smooth chart-pushed with compact
      -- support and tsupport in interior, MemWkp follows from MemWkp_of_smooth_compactSupport_pub.
      have h_per_α_mem : ∀ β : M,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (chartTargetEuclid (n := n) (M := M) β) := by
        intro β
        -- chartPushed = chartSmoothExt on interior up to ae.
        set fβ : M → ℝ := fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
            : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
        have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
          tsupport_pou_mul_subset_chart_source (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            β u
        have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) :=
          chartSmoothExtInteriorSupport_image_subset_interior
            (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
        set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
        -- MemWkp 1 p ext_β on interior part of chart target.
        have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
          rw [hext_β_def]
          exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            hu (h_int β)
        have hext_β_compact : HasCompactSupport ext_β := by
          rw [hext_β_def]
          exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
        have hext_β_supp : tsupport ext_β ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) := by
          have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
            rw [hext_β_def]
            exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
          exact h1.trans hint_image
        have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
          interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
        have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p) ext_β
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
            (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
        -- chartPushed equals chartSmoothExt = ext_β on interior up to ae.
        -- So MemWkp on interior is the same predicate up to congr_ae.
        have h_ae : ext_β =ᵐ[volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β))]
            chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
          rw [hext_β_def, hfβ_def]
          exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
        have h_chartPushed_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
            (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
        -- This is exactly MemWkpHalfSpace.
        exact h_chartPushed_W1p
      have h_mem_chart : MemWkpChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u :=
        h_per_α_mem
      exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_mem_chart
    have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
      hwkp_lt_top.ne
    set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
    have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
    have hLp_real : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ N := by
      apply ENNReal.toReal_mono hwkp_ne_top
      exact hLp_bd
    have hgrad_real : (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ (n : ℝ) * N := by
      have h_ne_top : ((n : ℕ) : ℝ≥0∞) *
          wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
      have h_le := ENNReal.toReal_mono h_ne_top hgrad_bd
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    have h_combined : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal ≤
      N + (n : ℝ) * N := by
      linarith
    have h_final : Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) ≤
      Cmorrey * (1 + (n : ℝ)) * N := by
      have h1 : Cmorrey * (N + (n : ℝ) * N) = Cmorrey * (1 + (n : ℝ)) * N := by ring
      calc Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
        (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal)
          ≤ Cmorrey * (N + (n : ℝ) * N) :=
            mul_le_mul_of_nonneg_left h_combined hCmorrey_nn
        _ = Cmorrey * (1 + (n : ℝ)) * N := h1
    rw [hf_def] at h_final
    exact le_trans hbound_y h_final

/-! ## Per-point evaluation: relating `(ρ_α · u)(x)` to `chartSmoothExt α (ρ_α · u)(...)` -/

omit [CompactSpace M] in
/-- For `x ∈ chartAt α source`, `(ρ_α · u)(x) = chartSmoothExt α (ρ_α · u) (extChartAt I α x)`. -/
private lemma chartSmoothExt_pou_mul_apply_at_chart_image
    (α : M) (u : M → ℝ) {x : M} (hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source) :
    chartSmoothExt (n := n) (M := M) α
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y)
        (extChartAt I_hs α x) =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
  classical
  have hx_target : extChartAt I_hs α x ∈ (extChartAt I_hs α).target :=
    (extChartAt I_hs α).map_source (by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hx)
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hx_target]
  rw [(extChartAt I_hs α).left_inv (by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hx)]

/-- For each `x : M`, `‖(ρ_α · u)(x)‖` is bounded by the sup norm of
`chartSmoothExt α (ρ_α · u)`. -/
private lemma norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (α : M) (u : M → ℝ) (x : M) {Cmod : ℝ}
    (hbound : ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
      (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤ Cmod) (hCmod : 0 ≤ Cmod) :
    ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x‖ ≤ Cmod := by
  classical
  by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · have h_eq := chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx
    rw [← h_eq]
    exact hbound _
  · have hρ_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x = 0 := by
      have hsubord :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).IsSubordinate
            (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M
      have h_supp := hsubord α
      by_contra hne
      apply hx
      apply h_supp
      apply subset_tsupport
      exact Function.mem_support.mpr hne
    rw [hρ_zero, zero_mul, norm_zero]
    exact hCmod

/-! ## Smooth manifold-side Morrey sup bound (uniform in `u`) -/

/-- Per-chart constant from `per_chart_smooth_sup_bound`, packaged as a
function `M → ℝ`. -/
private noncomputable def perChartMorreyConst
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)

private lemma perChartMorreyConst_nn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).1

private lemma perChartMorreyConst_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (y : EuN) :
    ‖chartSmoothExt (n := n) (M := M) α
        (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤
      perChartMorreyConst (n := n) (M := M) g hp α *
        (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).2 hu h_int y

/-- **Smooth manifold-level Morrey sup bound, with-boundary case** (uniform in
`u`). For a closed Riemannian manifold-with-boundary modelled on the
canonical Euclidean half-space `EuclideanHalfSpace n` and `p > n`, there is
a constant `C ≥ 0` (depending on `g`, `p`, and the canonical chart-atlas
POU) such that for every smooth `u : M → ℝ` whose canonical-POU chart-pushed
functions all have `tsupport` strictly inside the open interior parts of
the chart targets and every `x : M`,

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`. -/
theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  refine ⟨∑ α ∈ S, perChartMorreyConst (n := n) (M := M) g hp α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α _ =>
      perChartMorreyConst_nn (n := n) (M := M) g hp α)
  intro u hu h_int x
  have h_decomp : u x = ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x := by
    have hsum : ∑ α ∈ S,
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I_hs) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_decomp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  have hC_α_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
    perChartMorreyConst_nn (n := n) (M := M) g hp α
  have hCN_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α *
      (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
    mul_nonneg hC_α_nn ENNReal.toReal_nonneg
  refine norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (n := n) (M := M) α u x ?_ hCN_nn
  intro y
  exact perChartMorreyConst_bound (n := n) (M := M) g hp α hu h_int y

/-! ## Smooth Hölder modulus on the partition-of-unity-localized function

For each chart `α`, the smooth Euclidean Hölder modulus
(`smooth_morrey_pair_bound_uniform` from `EuclideanMorrey.lean`) applied to the
smooth chart-extended function `chartSmoothExt α (ρ_α · u)` on the half-ball
`B(0, R_α / 2)` of the chart-radius ball yields a Hölder bound on
`(ρ_α · u)` over the manifold-side compact `tsupport ρ_α ⊆ chart source`. -/

private lemma chartSmoothExt_holder_uniform_half_ball
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y₁ y₂ : EuN,
          y₁ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          y₂ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          ‖chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₁ -
            chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₂‖ ≤
            C * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hd_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : 1 ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set R : ℝ := chartRadius (n := n) (M := M) α with hR_def
  have hR_pos : 0 < R := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C₀, hC₀_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_pair_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := R) hR_pos
  refine ⟨C₀ * (n : ℝ), mul_nonneg hC₀_nn (Nat.cast_nonneg _), ?_⟩
  intro u hu h_int y₁ y₂ hy₁ hy₂
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have h_pair := hbound (u := f) hf_smooth_top hy₁ hy₂
  have h_grad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (n := n) (M := M) g (q := ENNReal.ofReal p) hp_enn_one hu h_int α
  have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
    -- Same argument as in per_chart_smooth_sup_bound.
    have h_per_α_mem : ∀ β : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
          (chartTargetEuclid (n := n) (M := M) β) := by
      intro β
      set fβ : M → ℝ := fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
          : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
      have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
        tsupport_pou_mul_subset_chart_source (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          β u
      have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) :=
        chartSmoothExtInteriorSupport_image_subset_interior
          (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
      set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
      have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
        rw [hext_β_def]
        exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          hu (h_int β)
      have hext_β_compact : HasCompactSupport ext_β := by
        rw [hext_β_def]
        exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
      have hext_β_supp : tsupport ext_β ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) := by
        have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
          rw [hext_β_def]
          exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
        exact h1.trans hint_image
      have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) β)) :=
        interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
      have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := n) 1 (ENNReal.ofReal p) ext_β
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
          (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
      have h_ae : ext_β =ᵐ[volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β))]
          chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
        rw [hext_β_def, hfβ_def]
        exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
      exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
        (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
    exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_per_α_mem
  have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    hwkp_lt_top.ne
  set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_d_wkp_ne_top : ((n : ℕ) : ℝ≥0∞) *
      wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
  have h_grad_real :
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) R))).toReal ≤
        (n : ℝ) * N := by
    have h_le := ENNReal.toReal_mono h_d_wkp_ne_top h_grad_bd
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    exact h_le
  have h_dist_eq : dist y₁ y₂ = ‖y₁ - y₂‖ := dist_eq_norm y₁ y₂
  have h_dist_pow_nn : 0 ≤ dist y₁ y₂ ^ (1 - (n : ℝ) / p) :=
    Real.rpow_nonneg dist_nonneg _
  calc ‖f y₁ - f y₂‖
      ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) *
          (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) R))).toReal := h_pair
    _ ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) * ((n : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_left h_grad_real
        exact mul_nonneg hC₀_nn h_dist_pow_nn
    _ = C₀ * (n : ℝ) * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) * N := by
        rw [h_dist_eq]; ring

/-- For `x ∈ tsupport ρ_α`, `extChartAt I α x ∈ Metric.ball 0 (R_α / 2)`. -/
private lemma extChartAt_mem_half_ball_of_mem_tsupport_pou
    (α : M) {x : M}
    (hx : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)) :
    extChartAt I_hs α x ∈
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  classical
  have h_in : extChartAt I_hs α x ∈ chartCarrier (n := n) (M := M) α :=
    ⟨x, hx, rfl⟩
  exact chartCarrier_subset_half_ball (n := n) (M := M) α h_in

/-- **Per-chart smooth Hölder modulus on the partition-of-unity-localized
function (with-boundary)**. For each chart `α`, smooth `u : M → ℝ` with
all-charts strict-interior support, and `p > n`, the canonical-POU
localised function `(ρ_α · u)` satisfies a Hölder modulus on the compact
`tsupport ρ_α`:

  `‖(ρ_α x · u x) - (ρ_α y · u y)‖ ≤
      C_α · ‖extChartAt I α x - extChartAt I α y‖^(1 - n/p) ·
        (wkpNormChart g 1 p u).toReal`,

uniformly in `u`. -/
private lemma pou_mul_holder_chart_uniform_tsupport
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
        ∀ y ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    chartSmoothExt_holder_uniform_half_ball (n := n) (M := M) g α hp
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int x hx y hy
  have h_subord :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hx_src : x ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hx
  have hy_src : y ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hy
  set y₁ : EuN := extChartAt I_hs α x with hy₁_def
  set y₂ : EuN := extChartAt I_hs α y with hy₂_def
  have hy₁_R2 : y₁ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hx
  have hy₂_R2 : y₂ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hy
  have h_pair := hbound hu h_int y₁ y₂ hy₁_R2 hy₂_R2
  have h_eq_x :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₁ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
    rw [hy₁_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx_src
  have h_eq_y :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₂ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y := by
    rw [hy₂_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hy_src
  rw [h_eq_x, h_eq_y] at h_pair
  exact h_pair

/-- **Smooth manifold-level Hölder modulus on the canonical POU localization,
per chart, with-boundary**. For a closed Riemannian manifold-with-boundary
modelled on `EuclideanHalfSpace n` and `p > n`, for each chart `α : M`,
there exists a compact `K_α ⊆ chart α source` and a constant `C_α ≥ 0`
(depending on `g`, `p`, the canonical POU and the chart `α`, but **not**
on `u`) such that for every smooth `u : M → ℝ` whose canonical-POU
chart-pushed functions all have strict-interior support and every
`x, y ∈ K_α`, the canonical chart-atlas POU localization `(ρ_α · u)`
satisfies the chart-α Hölder modulus

  `‖(ρ_α x · u x) - (ρ_α y · u y)‖ ≤
      C_α · ‖extChartAt I α x - extChartAt I α y‖^(1 - n/p) ·
        (wkpNormChart g 1 p u).toReal`,

with the compact set `K_α := tsupport ρ_α`. -/
theorem smooth_manifold_morrey_holder_modulus_per_chart_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ (chartAt (EuclideanHalfSpace n) α).source ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ K, ∀ y ∈ K,
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  refine ⟨Tα, (isClosed_tsupport _).isCompact, ?_, ?_⟩
  · exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  · obtain ⟨C, hC_nn, hbound⟩ :=
      pou_mul_holder_chart_uniform_tsupport (n := n) (M := M) g α hp
    exact ⟨C, hC_nn, fun {u} hu h_int x hx y hy => hbound hu h_int x hx y hy⟩

/-! ## Manifold-level decomposition: from the per-chart POU Hölder bound to
a finite-sum bound on `‖u(x) - u(y)‖`

For x, y in M and the canonical chart-atlas POU finset `S`, the triangle
inequality gives `‖u(x) - u(y)‖ ≤ ∑_{α ∈ S} ‖(ρ_α x · u x) - (ρ_α y · u y)‖`.
This is the same identity as in the boundaryless setting, since both
formulations have the canonical POU summing to `1` pointwise on `M`. -/

/-- The triangle decomposition: `‖u(x) - u(y)‖ ≤ ∑_α ‖(ρ_α x · u x) -
(ρ_α y · u y)‖`, with the sum over the canonical chart-atlas POU finset `S`. -/
theorem norm_sub_le_sum_pou_diff_withBoundary
    (u : M → ℝ) (x y : M) :
    ‖u x - u y‖ ≤
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I_hs) (M := M),
        ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  have hsum_x : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) x
  have hsum_y : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) y
  have h_diff_eq : u x - u y =
      ∑ α ∈ S,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hsum_x, hsum_y, one_mul, one_mul]
  rw [h_diff_eq]
  exact norm_sum_le (E := ℝ) S (fun α =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y)

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
