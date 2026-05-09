import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.GreenWithBoundary
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.OutwardNormal
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.SurfaceMeasure
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Identification of the chart-by-chart boundary face sum with the intrinsic
surface integral

For a smooth Riemannian metric `g` on a compact smooth manifold-with-boundary
`M` modelled on `EuclideanHalfSpace n` (with `[NeZero n]`), this file
establishes the identification

  `boundaryFaceSum g X = ∫_{∂M} g.inner x.val (outwardNormal g x) (X x.val) dS`,

linking the chart-by-chart presentation of the with-boundary divergence theorem
boundary contribution (`boundaryFaceSum`, defined via the chart-atlas partition
of unity in `GreenWithBoundary.lean`) with the intrinsic surface integral
against the smooth outward unit normal (`outwardNormal`, from
`OutwardNormal.lean`) and the surface measure (`surfaceMeasure`, from
`SurfaceMeasure.lean`).

## Strategy

The identification proceeds in two layers:

* **Per-chart identification (hypothesis).** For each base point
  `α ∈ chartAtlasPOU_finset`, the chart-α boundary face integral
  `chartBoundaryFaceIntegral g α X (ρ α)` equals an integral over
  `BoundaryManifold I M` of the chart-α-POU-weighted intrinsic surface
  integrand. This is the deep step: it amounts to the chart-local Voss–Weyl
  formula applied at the boundary face, plus the matching of chart-target
  Lebesgue measure on the boundary face with the induced metric volume on the
  boundary submanifold.

* **Global assembly.** Granted the per-chart identification, summing over `α`
  in the chart-atlas POU support set and exchanging the finite sum with the
  Bochner integral yields the global statement, after using the partition of
  unity sum-to-one identity to collapse the POU sum to `1`.

This file delivers the global assembly as a single named theorem
`boundaryFaceSum_eq_surface_integral_of_chartIdentification`, taking the
per-chart identifications as a hypothesis. The chart-level identification
itself is the subject of subsequent work and is not established here; the
hypothesis form makes the structural reduction explicit and permits downstream
clients to consume the identification once the per-chart step is proved.

## Main definitions and results

* `chartFaceIntegralEqualsSurfaceIntegralOnChart` — the per-chart
  identification predicate: for a base point `α`, the chart-α boundary face
  integral against a smooth weight `f` equals the surface integral of
  `f(x.val) · g.inner x.val (outwardNormal g x) (X x.val)` over the boundary
  submanifold.

* `boundaryFaceSum_eq_surface_integral_of_chartIdentification` — the global
  identification, taking the per-chart hypothesis specialised to the chart-α
  POU weight `ρ α` for each `α` in the chart-atlas POU support.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Function
open scoped Manifold Topology ContDiff Matrix ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open DifferentialGeometry.Integral.Measure

/-! ## File-local Borel-space instances

Match the convention in the surrounding files: `M` carries its canonical
Borel σ-algebra, and likewise the boundary submanifold. Declared `local` to
avoid leaking into callers. -/

private local instance instMeasurableSpaceM
    {M : Type*} [TopologicalSpace M] : MeasurableSpace M := borel M

private local instance instBorelSpaceM
    {M : Type*} [TopologicalSpace M] :
    @BorelSpace M _ (borel M) := letI : MeasurableSpace M := borel M; ⟨rfl⟩

/-! ## Per-chart identification predicate -/

/-- The per-chart identification predicate: the chart-α boundary face integral
of `X` against a smooth weight `f : M → ℝ` equals the surface integral of
`f` (precomposed with the boundary inclusion) times the intrinsic surface
integrand `g.inner x.val (outwardNormal g x) (X x.val)`.

Concretely:
$$\chartBoundaryFaceIntegral g \alpha X f
   = \int_{\partial M} f(x.\mathrm{val}) \cdot
       g.\mathrm{inner}\, x.\mathrm{val}\, (\nu\, x)\, (X\, x.\mathrm{val})\,
       dS,$$
where `\nu := outwardNormal g` and `dS := surfaceMeasure g`.

This predicate is the chart-by-chart content of the matching: when satisfied
for every `α ∈ chartAtlasPOU_finset` (with `f := chartAtlasPOU I M α`), the
global identification of `boundaryFaceSum g X` with the intrinsic surface
integral follows by linearity and the partition-of-unity sum-to-one identity,
as established in
`boundaryFaceSum_eq_surface_integral_of_chartIdentification`. -/
def chartFaceIntegralEqualsSurfaceIntegralOnChart
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (α : M)
    (X : Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯)
    (f : M → ℝ) : Prop :=
  chartBoundaryFaceIntegral
      (I := modelWithCornersEuclideanHalfSpace n) g α X f =
    ∫ x : (modelWithCornersEuclideanHalfSpace n).boundary M,
        f (x.val) *
          g.inner x.val
            (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g x :
              TangentSpace _ x.val)
            (X x.val)
        ∂(surfaceMeasure
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)

/-! ## Global assembly

Granted the per-chart identifications, the global identification
`boundaryFaceSum g X = ∫_{∂M} g.inner ⋯ dS` follows by summing the per-chart
identities over `α ∈ chartAtlasPOU_finset` and applying the
partition-of-unity sum-to-one identity to collapse the weighted integrand to
the unweighted one. -/

section GlobalAssembly

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ### Topological prerequisites

The boundary submanifold of a compact ambient manifold is itself compact
(closed subspace of a compact space). The surface measure, being the
Riemannian volume measure of the induced metric on the boundary submanifold,
is then a finite measure on a compact space — used for integrability bounds
on continuous integrands. -/

omit [T2Space M] [SigmaCompactSpace M] in
/-- The boundary submanifold of a compact ambient manifold is compact. -/
private lemma compactSpace_boundaryManifold :
    CompactSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) := by
  -- `BoundaryManifold I M = {x : M // x ∈ I.boundary M}`. The boundary is
  -- closed in a smooth manifold, hence as a subtype it inherits compactness
  -- from the ambient compact manifold.
  have h_one : (∞ : WithTop ℕ∞) ≠ 0 := by
    intro h
    exact ENat.top_ne_zero
      (WithTop.coe_eq_coe.mp
        (h : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞)))
  have h_closed :
      IsClosed ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) (n := ∞) h_one
  have h_compact :
      IsCompact ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    h_closed.isCompact
  -- `BoundaryManifold I M = ↥(I.boundary M)` (definitionally a subtype).
  have h_compact_subtype :
      CompactSpace
        (((modelWithCornersEuclideanHalfSpace n).boundary M) : Set M) :=
    isCompact_iff_compactSpace.mp h_compact
  exact h_compact_subtype

/-- The surface measure on a compact boundary submanifold is finite. -/
private lemma surfaceMeasure_isFiniteMeasure
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M) :
    IsFiniteMeasure
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  haveI : CompactSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :=
    compactSpace_boundaryManifold (n := n) (M := M)
  haveI :=
    surfaceMeasure_isFiniteMeasureOnCompacts
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g
  exact CompactSpace.isFiniteMeasure

/-! ### Per-summand integrability bound

For each `α : M`, the weighted integrand
`b ↦ ((chartAtlasPOU I M) α) b.val * g.inner b.val (outwardNormal g b) (X b.val)`
is integrable, given the integrability of the unweighted integrand and the
boundedness of `(chartAtlasPOU I M) α` (a partition of unity weight, bounded
above by `1`). This is `Integrable.bdd_mul` with the bound `‖ρ α‖ ≤ 1`. -/

omit [CompactSpace M] in
private lemma weighted_integrand_integrable
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (X : Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯)
    (h_int : Integrable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        g.inner b.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
            TangentSpace _ b.val)
          (X b.val))
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g))
    (α : M) :
    Integrable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α : M → ℝ)
            b.val *
          g.inner b.val
            (outwardNormal
                (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
              TangentSpace _ b.val)
            (X b.val))
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  -- Use `Integrable.bdd_mul` with bound `1` for `ρ α`.
  set ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M
      (univ : Set M) :=
    chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M
  -- Strong measurability of `ρ α ∘ val` via continuity.
  have h_meas_pou : AEStronglyMeasurable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        (ρ α : M → ℝ) b.val)
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
    have h_pou_cont : Continuous ((ρ α : M → ℝ)) := (ρ α).contMDiff.continuous
    have h_val_cont :
        Continuous
          (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
            (b.val : M)) := continuous_subtype_val
    exact (h_pou_cont.comp h_val_cont).aestronglyMeasurable
  -- Boundedness: `‖ρ α b.val‖ ≤ 1`.
  have h_bound : ∀ᵐ b
      ∂(surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g),
      ‖(ρ α : M → ℝ) b.val‖ ≤ 1 := by
    refine Filter.Eventually.of_forall (fun b => ?_)
    have h_le : (ρ α : M → ℝ) b.val ≤ 1 := ρ.le_one α b.val
    have h_nn : 0 ≤ (ρ α : M → ℝ) b.val := ρ.nonneg α b.val
    rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    exact h_le
  exact h_int.bdd_mul h_meas_pou h_bound

/-! ### Partition-of-unity sum collapse

At any boundary point `b : BoundaryManifold I M`, the partition-of-unity
weights `(ρ α) b.val` summed over the chart-atlas POU support set `S` collapse
to `1`. This relies on:

* `(ρ α)` being zero outside the finite support set `S` (by
  `chartAtlasPOU_weight_zero_of_notMem`);
* the partition-of-unity sum-to-one identity (by
  `SmoothPartitionOfUnity.sum_eq_one`, applied at the universal subordinate
  set);
* the conversion `finsum_eq_sum_of_support_subset`.
-/

private lemma chartAtlasPOU_finset_sum_eq_one_at_val
    (b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    ∑ α ∈ chartAtlasPOU_finset
        (I := modelWithCornersEuclideanHalfSpace n) (M := M),
      ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
        M → ℝ) b.val = 1 := by
  classical
  set ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M
      (univ : Set M) :=
    chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M with hρ_def
  set S : Finset M := chartAtlasPOU_finset
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) with hS_def
  -- The pointwise function `α ↦ (ρ α) b.val` has support in `S`.
  have h_supp_subset :
      Function.support (fun α : M => (ρ α : M → ℝ) b.val) ⊆ (S : Set M) := by
    intro α hα
    -- `α ∈ support f ↔ f α ≠ 0`. Need `α ∈ S`.
    -- If `α ∉ S`, then `(ρ α)` is identically zero by
    -- `chartAtlasPOU_weight_zero_of_notMem`, contradicting `(ρ α) b.val ≠ 0`.
    by_contra hαS
    have hzero :
        ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α : M → ℝ)
          b.val = 0 :=
      chartAtlasPOU_weight_zero_of_notMem
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) hαS b.val
    exact hα hzero
  -- Convert finsum ↦ Finset sum on support set.
  have h_finsum_eq_sum :
      (∑ᶠ α : M, (ρ α : M → ℝ) b.val) =
        ∑ α ∈ S, (ρ α : M → ℝ) b.val :=
    finsum_eq_sum_of_support_subset _ h_supp_subset
  -- Use POU sum-to-one at `b.val ∈ univ`.
  have h_sum_one : (∑ᶠ α : M, (ρ α : M → ℝ) b.val) = 1 :=
    ρ.sum_eq_one (Set.mem_univ b.val)
  rw [← h_finsum_eq_sum]; exact h_sum_one

/-! ### Sum-of-integrals to integral-of-sum

The standard linearity step: given the per-summand integrability, swap
`∑_α ∫ … = ∫ ∑_α …`. -/

private lemma sum_integral_eq_integral_sum_pou
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (X : Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯)
    (h_int : Integrable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        g.inner b.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
            TangentSpace _ b.val)
          (X b.val))
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ∑ α ∈ chartAtlasPOU_finset
            (I := modelWithCornersEuclideanHalfSpace n) (M := M),
        ∫ b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M,
          ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
              M → ℝ) b.val *
            g.inner b.val
              (outwardNormal
                  (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
                TangentSpace _ b.val)
              (X b.val)
          ∂(surfaceMeasure
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)
      = ∫ b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M,
          (∑ α ∈ chartAtlasPOU_finset
                  (I := modelWithCornersEuclideanHalfSpace n) (M := M),
              ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
                  M → ℝ) b.val) *
            g.inner b.val
              (outwardNormal
                  (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
                TangentSpace _ b.val)
              (X b.val)
          ∂(surfaceMeasure
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  classical
  -- Step 1: pull `∑ α ∈ S, ρ α (b.val) * Φ b` into `(∑ α ρ α b.val) * Φ b`.
  -- Step 2: apply `integral_finset_sum` with per-α integrability.
  set S : Finset M := chartAtlasPOU_finset
      (I := modelWithCornersEuclideanHalfSpace n) (M := M)
  have h_per :=
    fun α : M =>
      weighted_integrand_integrable (n := n) (M := M) g X h_int α
  -- `integral_finset_sum` gives: `∫ ∑_α f_α b dμ = ∑_α ∫ f_α b dμ` (forward).
  -- We need the reverse direction: `∑_α ∫ f_α b dμ = ∫ ∑_α f_α b dμ`.
  -- Then identify `∑_α (ρ α b.val * Φ b) = (∑_α ρ α b.val) * Φ b` via
  -- `Finset.sum_mul`.
  have h_swap :
      ∫ b, (∑ α ∈ S,
            ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
                M → ℝ) b.val *
              g.inner b.val
                (outwardNormal
                    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
                  TangentSpace _ b.val)
                (X b.val))
          ∂(surfaceMeasure
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)
      = ∑ α ∈ S,
          ∫ b,
            ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
                M → ℝ) b.val *
              g.inner b.val
                (outwardNormal
                    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
                  TangentSpace _ b.val)
                (X b.val)
            ∂(surfaceMeasure
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    integral_finset_sum (s := S)
      (fun α _ => h_per α)
  rw [← h_swap]
  -- Now identify `∑_α (ρ α b.val * Φ b) = (∑_α ρ α b.val) * Φ b`.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
  -- `∑ α ∈ S, ρ α b.val * Φ b = (∑ α ∈ S, ρ α b.val) * Φ b`.
  -- The lambda wraps the goal; simp only with `Finset.sum_mul` works.
  simp only [Finset.sum_mul]

/-! ### The main global theorem -/

/-- **Global identification of the boundary face sum with the intrinsic
surface integral**, assuming the per-chart matching for the chart-atlas POU.

Given the per-chart identification
`chartBoundaryFaceIntegral g α X (ρ α) = ∫_{∂M} (ρ α)(x.val) · g.inner ⋯ dS`
for every `α ∈ chartAtlasPOU_finset`, this theorem assembles the global
identification:

$$\mathrm{boundaryFaceSum}\, g\, X
   = \int_{\partial M} g.\mathrm{inner}\, x.\mathrm{val}\, (\nu\, x)\,
     (X\, x.\mathrm{val})\, dS,$$

where `\nu := outwardNormal g` and `dS := surfaceMeasure g`.

The proof has three structural steps. (i) Sum the per-chart identifications
over the chart-atlas POU support set (a Finset). (ii) Exchange the finite
sum with the Bochner integral via `integral_finset_sum`, with per-summand
integrability obtained from `Integrable.bdd_mul` (the POU weights are
bounded by `1`). (iii) Use the partition-of-unity sum-to-one identity
(specialised to the support Finset via `finsum_eq_sum_of_support_subset`) to
collapse the integrand to the unweighted form.

The integrability hypothesis `h_int` on the unweighted integrand is supplied
by the caller; it is automatically satisfied whenever the integrand is
continuous on the compact boundary submanifold (a standard application of
`Continuous.integrable_of_hasCompactSupport`). -/
theorem boundaryFaceSum_eq_surface_integral_of_chartIdentification
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (X : Cₛ^∞⟮(modelWithCornersEuclideanHalfSpace n);
        EuclideanSpace ℝ (Fin n),
        (TangentSpace (modelWithCornersEuclideanHalfSpace n) : M → Type _)⟯)
    (h_chart : ∀ α ∈ chartAtlasPOU_finset
        (I := modelWithCornersEuclideanHalfSpace n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α X
        ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α : M → ℝ))
    (h_int : Integrable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        g.inner b.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
            TangentSpace _ b.val)
          (X b.val))
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    boundaryFaceSum (I := modelWithCornersEuclideanHalfSpace n) g X =
      ∫ x : (modelWithCornersEuclideanHalfSpace n).boundary M,
        g.inner x.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g x :
            TangentSpace _ x.val)
          (X x.val)
        ∂(surfaceMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  classical
  -- Set up the partition-of-unity, the Finset, and the integrand.
  set S : Finset M := chartAtlasPOU_finset
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) with hS_def
  -- `boundaryFaceSum g X = ∑ α ∈ S, chartBoundaryFaceIntegral g α X (ρ α)`.
  rw [boundaryFaceSum_def]
  -- Per-chart: identify each `chartBoundaryFaceIntegral g α X (ρ α)` with
  -- the surface integral of `(ρ α) ∘ val * Φ`.
  have h_sum_chart :
      ∑ α ∈ S,
          chartBoundaryFaceIntegral
            (I := modelWithCornersEuclideanHalfSpace n) g α X
              (((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
                M → ℝ))
        =
      ∑ α ∈ S,
          ∫ b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M,
            ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
                M → ℝ) b.val *
              g.inner b.val
                (outwardNormal
                    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
                  TangentSpace _ b.val)
                (X b.val)
            ∂(surfaceMeasure
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
    refine Finset.sum_congr rfl (fun α hα => ?_)
    -- `chartFaceIntegralEqualsSurfaceIntegralOnChart` unfolds to the equality.
    exact h_chart α hα
  rw [h_sum_chart]
  -- Sum-of-integrals = integral-of-sum.
  rw [sum_integral_eq_integral_sum_pou (n := n) (M := M) g X h_int]
  -- Collapse the POU sum to `1`.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
  change (∑ α ∈ chartAtlasPOU_finset
              (I := modelWithCornersEuclideanHalfSpace n) (M := M),
            ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α :
              M → ℝ) b.val) *
        g.inner b.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
            TangentSpace _ b.val)
          (X b.val) =
      g.inner b.val
        (outwardNormal
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
          TangentSpace _ b.val)
        (X b.val)
  rw [chartAtlasPOU_finset_sum_eq_one_at_val (n := n) (M := M) b, one_mul]

end GlobalAssembly

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
