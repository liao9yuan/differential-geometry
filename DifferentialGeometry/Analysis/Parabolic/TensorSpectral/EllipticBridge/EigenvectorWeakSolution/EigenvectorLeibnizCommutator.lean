import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.TensorChartBilinearData
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1Compl
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

/-!
# The Leibniz-commutator integration-by-parts step for a generic chart-bilinear datum

For a closed Riemannian manifold `(M, g)` and a chart center `α : M`, the
chart-local divergence-form weak-elliptic data of a possibly non-smooth scalar
chart component is packaged in `ChartBilinearH1ComplData g α` (and its tensor
wrapper `TensorChartBilinearH1ComplData g r s α P₀`). Its variational identity
reads

```
∫_{Ω} ∑_{i, j} weightedInvGramOnEuclid · (weak_partial i) · ∂_jψ
  + ∫_{Ω} densityOnEuclid · u_chart · ψ = ∫_{Ω} densityOnEuclid · f_chart · ψ
```

on `Ω = chartTargetEuclid α`, for every smooth compactly supported `ψ` with
`tsupport ψ ⊆ Ω`.

The standard elliptic bootstrap raises the Sobolev order by *differentiating*
this identity once. This module ships exactly that step, as the cleanest
reusable lemma a downstream "iterated data" constructor consumes: assuming the
chart component `u_chart` lies in `W^{1,2}(Ω)` and *each* of its weak partials
`weak_partial i` again lies in `W^{1,2}(Ω)`, the chosen `l`-th weak partial
`chosenWeakPartial' 2 l u_chart Ω` satisfies a new divergence-form identity with
the **same** principal symbol `weightedInvGramOnEuclid` and a right-hand side
shifted by the integrated-by-parts Leibniz commutator

```
−∑_{i, j} (∂_l weightedInvGramOnEuclid_{ij}) · (weak_partial i) · ∂_jψ.
```

## The differentiated source

The differentiated right-hand side is recorded as the explicit pointwise
function `diffVariationalSource g α D l` (`EuclN → ℝ`). It collects the five
contributions produced by integrating by parts once more in direction `l`:

* `A` — the Leibniz commutator of the principal symbol, integrated by parts in
  `j`, contributing the partial of `weightedInvGramDerivOnEuclid` against the
  weak partials of `u_chart`;
* `B` — the same commutator, contributing `weightedInvGramDerivOnEuclid` against
  the second weak partials `∂_j ∂_l u_chart`;
* `C` — the zeroth-order Leibniz term `(∂_l density) · u_chart`, with a sign;
* `D`, `E` — the differentiated genuine source `(∂_l density) · f_chart` and
  `density · (∂_l f_chart)`.

`diffVariationalSource` is the value a downstream producer plugs into
`f_chart` of the next-level `(Tensor)ChartBilinearH1ComplData`.

## Main results

* `chartBilinear_diff_variational_identity` — the generic Leibniz-commutator
  integration-by-parts step, for a scalar `ChartBilinearH1ComplData g α`.

* `tensorChartComponent_diff_variational_identity` — the same step for the
  tensor wrapper `TensorChartBilinearH1ComplData g r s α P₀`.

## Sign convention

We follow the geometer convention `Δ = div ∘ grad`, with spectrum `⊆ (-∞, 0]`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Test-function helpers for the once-more-differentiated test factor `∂_l ψ`

The differentiated identity is obtained by applying the level-`0` variational
identity to the test function `ψ_l := ∂_l ψ`. The following lemmas record that
`ψ_l` is again a smooth compactly supported test function with topological
support inside the chart target, and that mixed second partials commute
(Schwarz symmetry). -/

/-- The partial `∂_l ψ` of a smooth function is smooth. -/
private lemma contDiff_partial
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

/-- The partial `∂_l ψ` of a compactly supported function is compactly
supported. -/
private lemma hasCompactSupport_partial
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

/-- The topological support of `∂_l ψ` is contained in that of `ψ`. -/
private lemma tsupport_partial_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

/-- Schwarz symmetry of mixed second partials of a smooth function:
`∂_j ∂_l ψ = ∂_l ∂_j ψ`. -/
private lemma partial_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

/-! ## `MemW1p`-to-local-`MemLp` plumbing

The Euclidean integration-by-parts primitive `integral_smul_weak_partial_eq`
consumes *local* `L²` integrability of the weakly differentiable factor and of
its weak partials. The lemma below converts a global `MemW1p 2 Ω` membership
into the per-compact-subset local `MemLp 2` it needs. -/

/-- A function in `MemLp 2 (volume.restrict Ω)` is in `MemLp 2
(volume.restrict K)` for every compact `K ⊆ Ω`. -/
private lemma memLp_restrict_of_memLp_restrict
    {Ω : Set EuclN} {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict Ω))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_in : K ⊆ Ω) :
    MemLp f 2 ((volume : Measure EuclN).restrict K) := by
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact hf.restrict K

/-! ## Smooth global extension of a chart-target smooth coefficient

The Euclidean integration-by-parts primitive consumes a *globally* smooth
coefficient. The principal symbol `weightedInvGramOnEuclid g α` (and the other
chart coefficients) are only smooth on the open chart target, with junk values
elsewhere. The lemma below extends any chart-target-smooth coefficient to a
globally smooth representative agreeing with it on a neighbourhood of a
prescribed compact subset of the chart target — by multiplying by a smooth
cutoff equal to `1` on that neighbourhood. -/

/-- Smooth global extension of a function `φ` that is `ContDiffOn` of any order
on the open chart target, agreeing with `φ` on a neighbourhood of a prescribed
compact `K ⊆ chartTargetEuclid α`. The output `(δ, φExt)` has `φExt` globally
smooth and `φExt = φ` pointwise on `cthickening δ K`. -/
private lemma exists_smooth_global_extension
    {φ : EuclN → ℝ} (α : M)
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_subset, hη_smooth, _hη_cs, _hη_range, hη_one,
      hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hK_in
  refine ⟨δ, fun y => η y * φ y, hδ_pos, hδ_subset, ?_, ?_⟩
  · -- `η · φ` is globally smooth: smooth on `tsupport η ⊆ chartTarget`, and
    -- `≡ 0` (hence smooth) on the open complement of `tsupport η`.
    have h_open_chart : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport η)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport η
    · have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α :=
        hη_tsupp hy_supp
      exact hη_smooth.contDiffAt.mul
        ((hφ_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => η y * φ y) =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  · intro y hy
    change η y * φ y = φ y
    rw [hη_one y hy, one_mul]

/-! ## The generic per-pair integration-by-parts primitive

The core reusable engine: for any function `v` on the open chart target with
`MemW1p 2`, and any smooth chart-target scalar coefficient `φ`, integrating the
product `φ · v · ∂_l ψ` by parts in direction `l` shifts the derivative onto
`φ` and onto the `l`-th chosen weak partial of `v`. This is the generic
analogue of the scalar campaign's `per_pair_ibp_chosenMthMixed`: there the
weakly differentiable factor was the hardcoded representative
`chosenMthMixedPartialChartPushedU`; here it is an arbitrary `MemW1p 2`
function. -/

/-- **Generic per-pair integration by parts on the chart target.** For a
function `v` lying in `W^{1,2}` of the open chart target `Ω = chartTargetEuclid α`
and a smooth chart-target scalar coefficient `φ`, integrating `φ · v · ∂_l ψ`
by parts in direction `l` against a smooth compactly supported test function
`ψ` with `tsupport ψ ⊆ Ω` yields

```
∫_Ω φ · v · ∂_l ψ
  = -((∫_Ω (∂_l φ) · v · ψ) + (∫_Ω φ · (chosenWeakPartial' 2 l v Ω) · ψ)).
```

The smooth coefficient `φ` is only required to be `ContDiffOn` on the open
chart target; it is extended to a globally smooth representative agreeing with
`φ` on a neighbourhood of `tsupport ψ` via `exists_smooth_global_extension`. -/
private theorem generic_per_pair_ibp
    (α : M)
    {v : EuclN → ℝ}
    (hv : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 v
      (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        φ y * v y * (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l 1) * v y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l v
              (chartTargetEuclid (I := I) (M := M) α) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- The weak partials of `v`: the chosen weak partial in each direction.
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j v Ω with hw_def
  -- Local `L²` integrability of `v`.
  have h_v_memLp : MemLp v 2 ((volume : Measure EuclN).restrict Ω) := hv.1
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := fun K' hK'c hK'i =>
    memLp_restrict_of_memLp_restrict h_v_memLp hK'c hK'i
  -- Each `w j` is a weak `j`-partial of `v` and lies in `MemLp 2`.
  have hw_global : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (w j) 2 ((volume : Measure EuclN).restrict Ω) := fun j =>
    chosenWeakPartial'_memLp_of_mem hv j
  have hw_locMemLp : ∀ (j : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j) 2 ((volume : Measure EuclN).restrict K') := fun j K' hK'c hK'i =>
    memLp_restrict_of_memLp_restrict (hw_global j) hK'c hK'i
  have hw_isWeakPartial : ∀ j : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j (w j) v Ω :=
    fun j => chosenWeakPartial'_isWeakPartial_of_mem hv j
  -- Compact tsupport of the test factor.
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  -- Smooth global extension of `φ`.
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α hφ_chart
      hK_compact hK_in
  -- Apply the generic Euclidean IBP primitive to `(φExt, v, w)` in direction `l`.
  have h_ibp_ext :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  -- Replace `φExt` by `φ` on `Ω` in every integral.
  have hK_in_thick : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  -- `fderiv ψ` vanishes outside `tsupport ψ`.
  have h_fderiv_zero : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  -- ψ vanishes outside `tsupport ψ`.
  have h_ψ_zero : ∀ x ∉ K, ψ x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport hx
  -- LHS replacement: `∫_Ω φExt · v · ∂_lψ = ∫_Ω φ · v · ∂_lψ`.
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thick hy_K)]
    · rw [h_fderiv_zero y hy_K]; simp
  -- `fderiv φExt = fderiv φ` on `K` (both agree on a neighbourhood).
  have h_fderiv_φExt_eq_φ : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l 1) := by
    intro y hy_K
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  -- First Leibniz integral: `∫_Ω (∂_l φExt) · v · ψ = ∫_Ω (∂_l φ) · v · ψ`.
  have hLeib1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ y hy_K]
    · rw [h_ψ_zero y hy_K]; ring
  -- Second Leibniz integral: `∫_Ω φExt · w l · ψ = ∫_Ω φ · w l · ψ`.
  have hLeib2_eq :
      ∫ y in Ω, φExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thick hy_K)]
    · rw [h_ψ_zero y hy_K]; ring
  rw [← hLHS_eq, ← hLeib1_eq, ← hLeib2_eq]
  exact h_ibp_ext

/-! ## The differentiated variational source

The right-hand side of the differentiated identity, recorded as an explicit
pointwise function on `EuclN`. It collects the five contributions produced by
integrating by parts once more in direction `l`. -/

/-- The differentiated right-hand side of the chart-bilinear variational
identity, after one integration by parts in direction `l`.

For a scalar `ChartBilinearH1ComplData g α` whose chart component and weak
partials lie in `W^{1,2}` of the chart target, this is the explicit pointwise
function whose integral against a test function `ψ` equals the differentiated
right-hand side. It is the sum of five contributions:

* `A` (with sign `+`): the partial `∂_j` of `weightedInvGramDerivOnEuclid g α
  i j l` against the weak partial `weak_partial i` — the Leibniz commutator of
  the principal symbol, integrated by parts in `j`;
* `B` (with sign `+`): `weightedInvGramDerivOnEuclid g α i j l` against the
  `j`-th chosen weak partial of `weak_partial i` — the residual second-order
  commutator term;
* `C` (with sign `−`): `densityDerivOnEuclid g α l · u_chart` — the zeroth-order
  Leibniz term;
* `D` (with sign `+`): `densityDerivOnEuclid g α l · f_chart` — the
  differentiated genuine source, density part;
* `E` (with sign `+`): `densityOnEuclid g α · (chosenWeakPartial' 2 l f_chart Ω)`
  — the differentiated genuine source, source part.

This is the value a downstream producer plugs into `f_chart` of the next-level
chart-bilinear datum. -/
def diffVariationalSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ := fun y =>
  (∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) * D.weak_partial i y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j (D.weak_partial i)
            (chartTargetEuclid (I := I) (M := M) α) y)
  - densityDerivOnEuclid (I := I) g α l y * D.u_chart y
  + densityDerivOnEuclid (I := I) g α l y * D.f_chart y
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.f_chart
        (chartTargetEuclid (I := I) (M := M) α) y

/-! ## Triple-product integrability on the chart target

The differentiated identity is an equation between sums of integrals of
triple products `coefficient · weak-factor · test-factor`. Each such product is
integrable on `volume.restrict Ω` because the coefficient is continuous, the
weak factor is locally `L²` (hence locally integrable), and the test factor is
continuous with compact support. -/

/-- Triple-product integrability: `a · u · h` is integrable on
`volume.restrict Ω` when `a` is continuous on `Ω`, `u` is `MemLp 2` on every
compact subset of `Ω`, and `h` is continuous with `tsupport h ⊆ Ω` compact. -/
private lemma integrable_triple
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {a : EuclN → ℝ} (ha : ContinuousOn a Ω)
    {u : EuclN → ℝ}
    (hu : ∀ K : Set EuclN, IsCompact K → K ⊆ Ω →
      MemLp u 2 ((volume : Measure EuclN).restrict K))
    {h : EuclN → ℝ} (hh_cont : Continuous h)
    (hh_cs : HasCompactSupport h) (hh_supp : tsupport h ⊆ Ω) :
    Integrable (fun y => a y * u y * h y)
      ((volume : Measure EuclN).restrict Ω) := by
  classical
  set K : Set EuclN := tsupport h with hK_def
  have hK_compact : IsCompact K := hh_cs
  have hK_meas : MeasurableSet K := (isClosed_tsupport h).measurableSet
  have hK_in : K ⊆ Ω := hh_supp
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- `K` has finite volume.
  have hvolK_finite' :
      ((volume : Measure EuclN).restrict K) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hK_compact.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  -- `u` is integrable on `K`.
  have hu_int_K : IntegrableOn u K (volume : Measure EuclN) :=
    (hu K hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- `a · h` is continuous with support inside `K`.
  set ah : EuclN → ℝ := fun y => a y * h y with hah_def
  have hah_supp : tsupport ah ⊆ K := by
    refine closure_minimal (fun y hy => ?_) hK_closed
    by_contra hy_notin
    have hh_y : h y = 0 := image_eq_zero_of_notMem_tsupport hy_notin
    exact hy (by simp [hah_def, hh_y])
  have hah_cont : Continuous ah := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ K
    · exact (ha.continuousAt (hΩ_open.mem_nhds (hK_in hy))).mul hh_cont.continuousAt
    · have h_eq_zero : ∀ᶠ z in 𝓝 y, ah z = 0 := by
        filter_upwards [hK_closed.isOpen_compl.mem_nhds hy] with z hz
        have hh_z : h z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [hah_def, hh_z]
      rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
  -- `u · (a · h)` is integrable on `K`, then extended by zero off `K`.
  have hu_ah_int_K : IntegrableOn (fun y => u y * ah y) K
      (volume : Measure EuclN) :=
    hu_int_K.mul_continuousOn hah_cont.continuousOn hK_compact
  have h_vanish : ∀ y, y ∉ K → u y * ah y = 0 := by
    intro y hy
    have hp : ah y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hah_supp hy_supp))
    simp [hp]
  have h_eq_ind :
      (fun y => u y * ah y) = K.indicator (fun y => u y * ah y) := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, h_vanish y hy]
  have full_int : Integrable (fun y => u y * ah y) (volume : Measure EuclN) := by
    rw [h_eq_ind]
    exact (integrable_indicator_iff hK_meas).mpr hu_ah_int_K
  have h_reassoc : (fun y => u y * ah y) = (fun y => a y * u y * h y) := by
    funext y; simp only [hah_def]; ring
  rw [h_reassoc] at full_int
  exact full_int.restrict

/-! ## The generic Leibniz-commutator integration-by-parts step

The headline of the module: the differentiated variational identity for a
generic scalar `ChartBilinearH1ComplData`. -/

set_option maxHeartbeats 1600000 in
/-- **Generic Leibniz-commutator integration-by-parts step.**

Let `D : ChartBilinearH1ComplData g α` be a scalar divergence-form chart-bilinear
datum on a closed Riemannian manifold `(M, g)`, and let `l` be a chart
direction. Suppose the chart component `D.u_chart` lies in `W^{1,2}` of the
chart target `Ω = chartTargetEuclid α`, that each weak partial `D.weak_partial i`
lies in `W^{1,2}(Ω)`, and that the right-hand side `D.f_chart` lies in
`W^{1,2}(Ω)`.

Then the chosen `l`-th weak partial `chosenWeakPartial' 2 l D.u_chart Ω`
satisfies the *differentiated* divergence-form variational identity

```
∫_Ω ∑_{i, j} weightedInvGramOnEuclid · (∂_l-weak-partial of weak_partial i) · ∂_jψ
  + ∫_Ω densityOnEuclid · (chosenWeakPartial' 2 l u_chart Ω) · ψ
  = ∫_Ω (diffVariationalSource g α D l) · ψ
```

for every smooth compactly supported test function `ψ` with
`tsupport ψ ⊆ Ω`.

The **principal symbol is unchanged** — it is again `weightedInvGramOnEuclid g α`
— and the right-hand side `diffVariationalSource g α D l` is the original source
shifted by the integrated-by-parts Leibniz commutator
`−∑_{i,j} (∂_l weightedInvGramOnEuclid_{ij}) · (weak_partial i) · ∂_jψ`.

The hypotheses (`u_chart`, every `weak_partial i`, and `f_chart` all lie in
`W^{1,2}(Ω)`) are the honest statement of one elliptic-bootstrap increment: the
chart component is `W^{2,2}`-regular and the source is `W^{1,2}`-regular. -/
theorem chartBilinear_diff_variational_identity
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (l : Fin (Module.finrank ℝ E))
    (h_u_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_wp_memW1p : ∀ i : Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_f_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i)
              (chartTargetEuclid (I := I) (M := M) α) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.u_chart
          (chartTargetEuclid (I := I) (M := M) α) y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      diffVariationalSource (I := I) (M := M) g α D l y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- The once-more-differentiated test factor `ψ_l := ∂_l ψ`.
  set ψ_l : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψ_l_def
  have hψ_l_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_l :=
    contDiff_partial (ψ := ψ) hψ_smooth l
  have hψ_l_cs : HasCompactSupport ψ_l :=
    hasCompactSupport_partial (ψ := ψ) hψ_cs l
  have hψ_l_supp : tsupport ψ_l ⊆ Ω :=
    (tsupport_partial_subset ψ l).trans hψ_supp
  -- Step 1: the level-0 variational identity applied to `ψ_l`.
  have h_level0 := D.variational_identity ψ_l hψ_l_smooth hψ_l_cs hψ_l_supp
  -- Smoothness / continuity helpers for the coefficients.
  have h_a_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) Ω :=
    fun i j => (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_da_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
    fun i j =>
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l).continuousOn
  have h_dens_cont : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_dens_deriv_cont : ContinuousOn (densityDerivOnEuclid (I := I) g α l) Ω :=
    (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn
  -- `∂_j` of `weightedInvGramDerivOnEuclid` is continuous on `Ω`.
  have h_da_fderiv_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun y : EuclN =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1)) Ω := by
    intro i j
    have h_diffOn :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
    have h_fderiv_diff :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y => fderiv ℝ
            (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact (h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)).continuousOn
  -- Continuity / support of the test factors.
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_partial_cs : ∀ j : Fin (Module.finrank ℝ E),
      HasCompactSupport (fun y : EuclN =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => hasCompactSupport_partial (ψ := ψ) hψ_cs j
  have hψ_partial_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ Ω :=
    fun j => (tsupport_partial_subset ψ j).trans hψ_supp
  have hψ_l_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_l_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_l_partial_cs : ∀ j : Fin (Module.finrank ℝ E),
      HasCompactSupport (fun y : EuclN =>
        (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) :=
    fun j => hasCompactSupport_partial (ψ := ψ_l) hψ_l_cs j
  have hψ_l_partial_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) ⊆ Ω :=
    fun j => (tsupport_partial_subset ψ_l j).trans hψ_l_supp
  -- Local `L²` integrability of the various weak factors on `Ω`.
  have h_u_loc : ∀ K : Set EuclN, IsCompact K → K ⊆ Ω →
      MemLp D.u_chart 2 ((volume : Measure EuclN).restrict K) :=
    fun K hKc hKi => memLp_restrict_of_memLp_restrict h_u_memW1p.1 hKc hKi
  have h_f_loc : ∀ K : Set EuclN, IsCompact K → K ⊆ Ω →
      MemLp D.f_chart 2 ((volume : Measure EuclN).restrict K) :=
    fun K hKc hKi => memLp_restrict_of_memLp_restrict h_f_memW1p.1 hKc hKi
  have h_wp_loc : ∀ (i : Fin (Module.finrank ℝ E)) (K : Set EuclN),
      IsCompact K → K ⊆ Ω →
      MemLp (D.weak_partial i) 2 ((volume : Measure EuclN).restrict K) :=
    fun i K hKc hKi => memLp_restrict_of_memLp_restrict (h_wp_memW1p i).1 hKc hKi
  have h_wp_wp_loc : ∀ (i j : Fin (Module.finrank ℝ E)) (K : Set EuclN),
      IsCompact K → K ⊆ Ω →
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j (D.weak_partial i) Ω)
        2 ((volume : Measure EuclN).restrict K) :=
    fun i j K hKc hKi =>
      memLp_restrict_of_memLp_restrict
        (chosenWeakPartial'_memLp_of_mem (h_wp_memW1p i) j) hKc hKi
  have h_f_wp_loc : ∀ (K : Set EuclN), IsCompact K → K ⊆ Ω →
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.f_chart Ω)
        2 ((volume : Measure EuclN).restrict K) :=
    fun K hKc hKi =>
      memLp_restrict_of_memLp_restrict
        (chosenWeakPartial'_memLp_of_mem h_f_memW1p l) hKc hKi
  have h_u_wp_loc : ∀ (K : Set EuclN), IsCompact K → K ⊆ Ω →
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.u_chart Ω)
        2 ((volume : Measure EuclN).restrict K) :=
    fun K hKc hKi =>
      memLp_restrict_of_memLp_restrict
        (chosenWeakPartial'_memLp_of_mem h_u_memW1p l) hKc hKi
  -- Step 2: per-pair principal IBP. For each `(i, j)`:
  --   ∫ a_ij · (wp i) · ∂_j ψ_l
  --     = A_ij + B_ij - PR_ij
  -- where `A`, `B` are integrals against `ψ` and `PR` against `∂_j ψ`.
  set A_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) * D.weak_partial i y * ψ y
        ∂(volume : Measure EuclN) with hA_pair_def
  set B_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j (D.weak_partial i) Ω y *
          ψ y
        ∂(volume : Measure EuclN) with hB_pair_def
  set PR_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i) Ω y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) with hPR_pair_def
  set LHS_m_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) with hLHS_m_pair_def
  -- The principal-pair decomposition.
  have h_principal_pair : ∀ i j : Fin (Module.finrank ℝ E),
      LHS_m_pair i j = A_pair i j + B_pair i j - PR_pair i j := by
    intro i j
    -- IBP of the principal: smooth coef `a_ij`, weak factor `wp i`, direction `l`.
    -- Schwarz pre-step: `∂_j ψ_l = ∂_l (∂_j ψ)`.
    set ψ_j : EuclN → ℝ := fun y =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hψ_j_def
    have hψ_j_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_j :=
      contDiff_partial (ψ := ψ) hψ_smooth j
    have hψ_j_cs : HasCompactSupport ψ_j :=
      hasCompactSupport_partial (ψ := ψ) hψ_cs j
    have hψ_j_supp : tsupport ψ_j ⊆ Ω :=
      (tsupport_partial_subset ψ j).trans hψ_supp
    -- Rewrite the LHS principal pair via Schwarz.
    have h_lhs_schwarz : LHS_m_pair i j =
        ∫ y in Ω,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1)
          ∂(volume : Measure EuclN) := by
      change (∫ y in Ω,
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) = _
      refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
      rw [partial_swap (ψ := ψ) hψ_smooth y j l]
    -- IBP in `l` of `a_ij · (wp i) · ∂_l ψ_j`.
    have h_pp := generic_per_pair_ibp (I := I) (M := M) α
      (h_wp_memW1p i)
      (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j)
      hψ_j_smooth hψ_j_cs hψ_j_supp l
    -- IBP in `j` of `(∂_l a_ij) · (wp i) · ∂_j ψ`.
    have h_inner := generic_per_pair_ibp (I := I) (M := M) α
      (h_wp_memW1p i)
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l)
      hψ_smooth hψ_cs hψ_supp j
    -- `h_pp` rewrites `LHS_m_pair i j` (via Schwarz) into
    --   -((∫ (∂_l a_ij) · (wp i) · ψ_j) + PR_ij),
    -- where the Leibniz coefficient `(fderiv (a_ij) y)(e_l)` is, definitionally,
    -- `weightedInvGramDerivOnEuclid g α i j l y`.
    -- `h_inner` rewrites `∫ (weightedInvGramDerivOnEuclid g α i j l) · (wp i) · ∂_j ψ`
    -- into `-(A_ij + B_ij)`. Since `ψ_j = ∂_j ψ`, the two cancel as below.
    have h_pp' : LHS_m_pair i j =
        -((∫ y in Ω,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              D.weak_partial i y * ψ_j y
            ∂(volume : Measure EuclN)) + PR_pair i j) := by
      rw [h_lhs_schwarz]
      -- `h_pp` is `… = -((∫ (fderiv a_ij)(e_l) · v · ψ_j) + (∫ a_ij · (∂_l v) · ψ_j))`;
      -- the first coefficient is definitionally `weightedInvGramDerivOnEuclid`, and
      -- the second integral is definitionally `PR_pair i j`.
      exact h_pp
    -- `∫ (weightedInvGramDerivOnEuclid g α i j l) · (wp i) · ψ_j` with
    -- `ψ_j = ∂_j ψ` is the LHS of `h_inner`.
    have h_inner' :
        (∫ y in Ω,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              D.weak_partial i y * ψ_j y
            ∂(volume : Measure EuclN)) =
        -(A_pair i j + B_pair i j) := h_inner
    rw [h_pp', h_inner']
    ring
  -- Continuity of `∂_l weightedInvGramOnEuclid` agrees with
  -- `weightedInvGramDerivOnEuclid` (so `h_da_cont` covers the A-term coefficient).
  -- Integrability of the per-pair atoms.
  have h_int_LHS : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple hΩ_open (h_a_cont i j) (h_wp_loc i)
      (hψ_l_partial_cont j) (hψ_l_partial_cs j) (hψ_l_partial_supp j)
  have h_int_A : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) * D.weak_partial i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple hΩ_open (h_da_fderiv_cont i j) (h_wp_loc i)
      hψ_cont hψ_cs hψ_supp
  have h_int_B : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j (D.weak_partial i) Ω y *
        ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple hΩ_open (h_da_cont i j) (h_wp_wp_loc i j)
      hψ_cont hψ_cs hψ_supp
  have h_int_PR : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i) Ω y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple hΩ_open (h_a_cont i j) (h_wp_wp_loc i l)
      (hψ_partial_cont j) (hψ_partial_cs j) (hψ_partial_supp j)
  -- Step 3: sum-swap the principal LHS, `∑∫ = ∫∑`.
  set LHS_principal0 : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) with hLHS_principal0_def
  set LHS_mass0 : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y * D.u_chart y * ψ_l y
      ∂(volume : Measure EuclN) with hLHS_mass0_def
  set RHS0 : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y * D.f_chart y * ψ_l y
      ∂(volume : Measure EuclN) with hRHS0_def
  have h_level0' : LHS_principal0 + LHS_mass0 = RHS0 := h_level0
  have h_swap_principal0 : LHS_principal0 = ∑ i, ∑ j, LHS_m_pair i j := by
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) = _
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_LHS i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_LHS i j)]
  -- `∑∑ LHS_m_pair = ∑∑ A + ∑∑ B - ∑∑ PR`.
  have h_sum_principal :
      ∑ i, ∑ j, LHS_m_pair i j =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) -
        (∑ i, ∑ j, PR_pair i j) := by
    calc ∑ i, ∑ j, LHS_m_pair i j
        = ∑ i, ∑ j, (A_pair i j + B_pair i j - PR_pair i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_principal_pair i j
      _ = ∑ i, ∑ j, (A_pair i j + (B_pair i j + (-(PR_pair i j)))) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i, (∑ j, A_pair i j) +
            ∑ i, (∑ j, (B_pair i j + (-(PR_pair i j)))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, A_pair i j) +
          ((∑ i, ∑ j, B_pair i j) + ∑ i, ∑ j, -(PR_pair i j)) := by
          congr 1
          rw [show (fun i => ∑ j, (B_pair i j + (-(PR_pair i j)))) =
              (fun i => (∑ j, B_pair i j) + (∑ j, -(PR_pair i j))) by
            funext i; exact Finset.sum_add_distrib]
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) -
          (∑ i, ∑ j, PR_pair i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  -- Step 4: IBP of the mass term `∫ density · u_chart · ∂_l ψ`.
  set N_C : ℝ :=
    ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
      D.u_chart y * ψ y ∂(volume : Measure EuclN) with hN_C_def
  set N_mass_C2 : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.u_chart Ω y * ψ y
      ∂(volume : Measure EuclN) with hN_mass_C2_def
  have h_mass_ibp : LHS_mass0 = -(N_C + N_mass_C2) := by
    have hb := generic_per_pair_ibp (I := I) (M := M) α h_u_memW1p
      (densityOnEuclid_contDiffOn (I := I) g α) hψ_smooth hψ_cs hψ_supp l
    change (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.u_chart y * ψ_l y
        ∂(volume : Measure EuclN)) = _
    rw [hb]
    rfl
  -- Step 5: IBP of the RHS term `∫ density · f_chart · ∂_l ψ`.
  set N_D : ℝ :=
    ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
      D.f_chart y * ψ y ∂(volume : Measure EuclN) with hN_D_def
  set N_E : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.f_chart Ω y * ψ y
      ∂(volume : Measure EuclN) with hN_E_def
  have h_rhs_ibp : RHS0 = -(N_D + N_E) := by
    have hb := generic_per_pair_ibp (I := I) (M := M) α h_f_memW1p
      (densityOnEuclid_contDiffOn (I := I) g α) hψ_smooth hψ_cs hψ_supp l
    change (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.f_chart y * ψ_l y
        ∂(volume : Measure EuclN)) = _
    rw [hb]
    rfl
  -- Step 6: collect the algebraic identity.
  --   (∑∑ PR) + N_mass_C2 = (∑∑ A) + (∑∑ B) - N_C + N_D + N_E.
  have h_combine : (∑ i, ∑ j, PR_pair i j) + N_mass_C2 =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - N_C + N_D + N_E := by
    have h := h_level0'
    rw [h_swap_principal0, h_sum_principal, h_mass_ibp, h_rhs_ibp] at h
    linarith
  -- Step 7: the goal LHS principal is `∑∑ PR_pair`.
  set goal_LHS_principal : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i) Ω y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) with hgoal_LHS_principal_def
  have h_goal_principal_eq : goal_LHS_principal = ∑ i, ∑ j, PR_pair i j := by
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i) Ω y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) = _
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_PR i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_PR i j)]
  -- Step 8: the goal RHS `∫ diffVariationalSource · ψ` decomposes as
  --   (∑∑ A) + (∑∑ B) - N_C + N_D + N_E.
  set goal_RHS : ℝ :=
    ∫ y in Ω,
      diffVariationalSource (I := I) (M := M) g α D l y * ψ y
      ∂(volume : Measure EuclN) with hgoal_RHS_def
  have h_goal_RHS_decomp : goal_RHS =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - N_C + N_D + N_E := by
    -- Atoms.
    set f_A : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) * D.weak_partial i y * ψ y with hf_A_def
    set f_B : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j (D.weak_partial i) Ω y *
        ψ y with hf_B_def
    set f_C : EuclN → ℝ := fun y =>
      -(densityDerivOnEuclid (I := I) g α l y * D.u_chart y * ψ y) with hf_C_def
    set f_D : EuclN → ℝ := fun y =>
      densityDerivOnEuclid (I := I) g α l y * D.f_chart y * ψ y with hf_D_def
    set f_E : EuclN → ℝ := fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.f_chart Ω y *
        ψ y with hf_E_def
    -- The differentiated source integrand decomposes pointwise.
    have h_integrand_eq : ∀ y : EuclN,
        diffVariationalSource (I := I) (M := M) g α D l y * ψ y =
        f_A y + f_B y + f_C y + f_D y + f_E y := by
      intro y
      unfold diffVariationalSource
      simp only [add_mul, sub_mul, Finset.sum_mul, hf_A_def, hf_B_def, hf_C_def,
        hf_D_def, hf_E_def]
      ring
    rw [show goal_RHS = ∫ y in Ω,
        diffVariationalSource (I := I) (M := M) g α D l y * ψ y
        ∂(volume : Measure EuclN) from rfl,
      setIntegral_congr_fun hΩ_meas (fun y _ => h_integrand_eq y)]
    -- Integrability of the atoms.
    have hint_A : Integrable f_A ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_A i j))
    have hint_B : Integrable f_B ((volume : Measure EuclN).restrict Ω) :=
      integrable_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => h_int_B i j))
    have hint_C : Integrable f_C ((volume : Measure EuclN).restrict Ω) :=
      (integrable_triple hΩ_open h_dens_deriv_cont h_u_loc
        hψ_cont hψ_cs hψ_supp).neg
    have hint_D : Integrable f_D ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple hΩ_open h_dens_deriv_cont h_f_loc
        hψ_cont hψ_cs hψ_supp
    have hint_E : Integrable f_E ((volume : Measure EuclN).restrict Ω) :=
      integrable_triple hΩ_open h_dens_cont h_f_wp_loc
        hψ_cont hψ_cs hψ_supp
    have h_sum_AB : Integrable (fun y => f_A y + f_B y)
        ((volume : Measure EuclN).restrict Ω) := hint_A.add hint_B
    have h_sum_ABC : Integrable (fun y => f_A y + f_B y + f_C y)
        ((volume : Measure EuclN).restrict Ω) := h_sum_AB.add hint_C
    have h_sum_ABCD : Integrable (fun y => f_A y + f_B y + f_C y + f_D y)
        ((volume : Measure EuclN).restrict Ω) := h_sum_ABC.add hint_D
    rw [MeasureTheory.integral_add h_sum_ABCD hint_E]
    rw [MeasureTheory.integral_add h_sum_ABC hint_D]
    rw [MeasureTheory.integral_add h_sum_AB hint_C]
    rw [MeasureTheory.integral_add hint_A hint_B]
    -- Each of the five integrals.
    have h_int_f_A : (∫ y in Ω, f_A y ∂(volume : Measure EuclN)) =
        ∑ i, ∑ j, A_pair i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) * D.weak_partial i y * ψ y
          ∂(volume : Measure EuclN)) = _
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_A i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_A i j)]
    have h_int_f_B : (∫ y in Ω, f_B y ∂(volume : Measure EuclN)) =
        ∑ i, ∑ j, B_pair i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
                (D.weak_partial i) Ω y * ψ y
          ∂(volume : Measure EuclN)) = _
      rw [integral_finset_sum _ (fun i _ =>
        (integrable_finset_sum _ (fun j _ => h_int_B i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finset_sum _ (fun j _ => h_int_B i j)]
    have h_int_f_C : (∫ y in Ω, f_C y ∂(volume : Measure EuclN)) = -N_C := by
      change (∫ y in Ω,
          -(densityDerivOnEuclid (I := I) g α l y * D.u_chart y * ψ y)
          ∂(volume : Measure EuclN)) = _
      rw [MeasureTheory.integral_neg]
    have h_int_f_D : (∫ y in Ω, f_D y ∂(volume : Measure EuclN)) = N_D := rfl
    have h_int_f_E : (∫ y in Ω, f_E y ∂(volume : Measure EuclN)) = N_E := rfl
    rw [h_int_f_A, h_int_f_B, h_int_f_C, h_int_f_D, h_int_f_E]
    ring
  -- Step 9: assemble the goal.
  change goal_LHS_principal + N_mass_C2 = goal_RHS
  rw [h_goal_principal_eq, h_goal_RHS_decomp]
  linarith [h_combine]

/-! ## The tensor wrapper

The same Leibniz-commutator integration-by-parts step, stated for the tensor
chart-component data structure `TensorChartBilinearH1ComplData`. -/

/-- The differentiated right-hand side for a tensor chart-component datum, i.e.
`diffVariationalSource` applied to the underlying scalar chart data. This is the
value a downstream producer plugs into `f_chart` of the next-level tensor
chart-bilinear datum. -/
def tensorDiffVariationalSource
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  diffVariationalSource (I := I) (M := M) g α D.toChartData l

/-- **Generic Leibniz-commutator integration-by-parts step — tensor wrapper.**

For a tensor chart-component datum `D : TensorChartBilinearH1ComplData g r s α P₀`
on a closed Riemannian manifold `(M, g)` and a chart direction `l`, suppose the
chart component `D.u_chart`, every weak partial `D.weak_partial i`, and the
right-hand side `D.f_chart` lie in `W^{1,2}` of the chart target
`Ω = chartTargetEuclid α`.

Then the chosen `l`-th weak partial `chosenWeakPartial' 2 l D.u_chart Ω`
satisfies the *differentiated* divergence-form variational identity with the
**same** principal symbol `weightedInvGramOnEuclid g α` and the differentiated
right-hand side `tensorDiffVariationalSource D l`:

```
∫_Ω ∑_{i, j} weightedInvGramOnEuclid · (∂_l-weak-partial of weak_partial i) · ∂_jψ
  + ∫_Ω densityOnEuclid · (chosenWeakPartial' 2 l u_chart Ω) · ψ
  = ∫_Ω (tensorDiffVariationalSource D l) · ψ
```

for every smooth compactly supported test function `ψ` with `tsupport ψ ⊆ Ω`.

This is the tensor analogue of `chartBilinear_diff_variational_identity`: the
tensor structure being a thin wrapper around the scalar one, the conclusion is
a definitional re-export of the scalar step applied to `D.toChartData`. The
differentiated datum it produces is again of `(Tensor)ChartBilinearH1ComplData`
shape, so iterating this step is the elliptic-bootstrap order increment. -/
theorem tensorChartComponent_diff_variational_identity
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    (l : Fin (Module.finrank ℝ E))
    (h_u_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_wp_memW1p : ∀ i : Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_f_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 l (D.weak_partial i)
              (chartTargetEuclid (I := I) (M := M) α) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l D.u_chart
          (chartTargetEuclid (I := I) (M := M) α) y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      tensorDiffVariationalSource (I := I) (M := M) D l y * ψ y
      ∂(volume : Measure EuclN) :=
  chartBilinear_diff_variational_identity (I := I) (M := M) D.toChartData l
    h_u_memW1p h_wp_memW1p h_f_memW1p hψ_smooth hψ_cs hψ_supp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
