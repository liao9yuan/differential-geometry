import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# `K`-graded explicit-norm bound for the cross-right gradient-divergence limit

The cross-right gradient-term divergence has, as its `n → ∞` `L²`-limit, the
explicit finite-sum object `crossRightGradCoeffDivLimit g r s h_atlas i α P₀`.
By definition it is a sum of two three-fold finite sums, indexed by a chart
direction `l` and a pair of component multi-indices `(P, Q)`:

* a **component-atom** group: the kernel-indicator-cut chart-Euclidean partial of
  the test-independent `C^∞` factor `crossRightDivFactor`, times the cutoff
  chart-component limit object `crossRightLimitComponent g r s h_atlas i α P`;
* a **chart-partial-atom** group: the kernel-indicator-cut `C^∞` factor
  `crossRightDivFactor`, times the cutoff chart-partial limit object
  `cutoffPartialLpLimit g r s h_atlas i α P l`.

The order-`0` companion `eLpNorm_crossRightGradCoeffDivLimit_le` records the
quantitative weighted-`eLpNorm` bound — the `wkpNorm`-bound at Sobolev order `0`
— for the limit, in terms of the weighted `eLpNorm`s of the two atom families.
This file records its order-`K` generalisation: there is a nonnegative constant
`C` with

```
wkpNorm K 2 (crossRightGradCoeffDivLimit g r s h_atlas i α P₀)
    (chartTargetEuclid α)
  ≤ ENNReal.ofReal C *
      ((∑ P, wkpNorm K 2 (crossRightLimitComponent g r s h_atlas i α P)
              (chartTargetEuclid α))
        + (∑ P, ∑ l, wkpNorm K 2 (cutoffPartialLpLimit g r s h_atlas i α P l)
              (chartTargetEuclid α))),
```

the faithful order-`K` `wkpNorm` analogue of the order-`0` `eLpNorm` atom sum:
the same two atom families `crossRightLimitComponent` (indexed by the component
multi-index `P`) and `cutoffPartialLpLimit` (indexed by `P` and the chart
direction `l`), kept verbatim as aggregate terms.

## Strategy

`crossRightGradCoeffDivLimit` is the sum of two three-fold finite sums; iterated
Minkowski for `wkpNorm` (`wkpNorm_add_le`, `wkpNorm_sum_le`) bounds its order-`K`
norm by the sum of the two group norms, then by the sum of the per-summand norms
within each group. Each three-fold-sum summand is a product
`Set.indicator (chartPouKernel α) c · w` of a kernel-indicator-cut coefficient
with a `W^{K,2}` atom. The coefficient `c` — `crossRightDivFactor` or its
chart-Euclidean partial — is `C^∞` on the open chart target *and vanishes off
the compact partition-of-unity kernel* `chartPouKernel α`. Hence the kernel
indicator acts as the identity (`Set.indicator (chartPouKernel α) c = c`
pointwise), and `c` extends to a globally `C^∞` compactly-supported coefficient.

The quantitative "off-kernel-vanishing smooth coefficient × `W^{K,2}` atom"
closure `wkpNorm_offKernelSmoothCoef_mul_le` — the order-`K` `wkpNorm` twin of
the qualitative `memWkp_offKernelSmoothCoef_mul` — then gives, per summand,

```
wkpNorm K 2 (fun y => c y * w y) Ω ≤ ENNReal.ofReal C * wkpNorm K 2 w Ω,
```

via the global-smoothness Leibniz bound `wkpNorm_smul_smooth_bounded_le`. The
atom `wkpNorm` is bounded by the full atom-family sum; the coefficient sup
constants and the triple-index cardinality fold into a single nonnegative `C`.

## Main result

* `wkpNorm_crossRightGradCoeffDivLimit_le` — the `K`-graded explicit-norm
  `wkpNorm` bound for the cross-right gradient-divergence limit, in terms of the
  order-`K` `wkpNorm`s of its two atom families.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The quantitative off-kernel-vanishing smooth-coefficient `wkpNorm` bound

The workhorse — the order-`K` `wkpNorm` twin of the qualitative
`memWkp_offKernelSmoothCoef_mul`. When the coefficient is itself `C^∞` on the
open Euclidean chart target *and* vanishes pointwise off a compact kernel inside
the chart target, it extends to a globally `C^∞` compactly-supported function:
no auxiliary cutoff is needed. Its iterated derivatives up to order `K` are then
uniformly bounded, so the global-smoothness Leibniz bound
`wkpNorm_smul_smooth_bounded_le` applies and bounds the order-`K` Sobolev norm
of the product `coef · factor` by an explicit constant times the order-`K` norm
of the factor — with no support hypothesis on the factor. -/

section OffKernelCoefBound

set_option linter.unusedSectionVars false in
/-- **Quantitative off-kernel-vanishing smooth-coefficient `wkpNorm` bound.** For
a coefficient `coef : EuclN → ℝ` that is `C^∞` on the open Euclidean chart
target and vanishes pointwise off a compact kernel `Kkern` inside the chart
target, and a factor in `MemWkp K 2` on the chart target, the pointwise product
`coef · factor` lies in `MemWkp K 2` on the chart target and there is a
nonnegative constant `C` with

```
wkpNorm K 2 (fun y => coef y * factor y) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * wkpNorm K 2 factor (chartTargetEuclid α).
```

The off-kernel vanishing makes `coef` globally `C^∞` (smooth on its closed
support inside the chart target, identically zero on the open complement) and
compactly supported; a uniform bound on its iterated derivatives up to order `K`
feeds the global-smoothness Leibniz bound `wkpNorm_smul_smooth_bounded_le`. -/
private lemma wkpNorm_offKernelSmoothCoef_mul_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0)
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The closed support of `coef` sits inside the compact kernel, hence in `Ω`.
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  -- `coef` is globally `C^∞`: smooth on `tsupport coef ⊆ Ω`, zero off it.
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  -- A uniform bound on the iterated derivatives of `coef` up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  -- `coef · factor ∈ MemWkp K 2` via `MemWkp.smul_smooth_bounded`.
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hcoef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  refine ⟨h_memWkp, ?_⟩
  -- The quantitative global-smoothness Leibniz bound for the coefficient.
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hcoef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  exact ⟨Kc, le_of_lt hKc_pos, hKc_bd hfactor_memWkp⟩

end OffKernelCoefBound

/-! ## Finite-sum closure for `MemWkp K 2`

The cross-right gradient-divergence limit's two groups are finite sums indexed
by the triple-index product type; the helper below propagates `MemWkp K 2`
through a finite sum indexed by an arbitrary `Finset`. -/

section MemWkpFinsetSum

set_option linter.unusedSectionVars false in
/-- **`MemWkp` is closed under finite sums.** A finite-`Finset` sum of
`MemWkp k 2` functions on an open set is also `MemWkp k 2`. -/
private lemma memWkp_finset_sum_iota
    {k : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {ι : Type*} (S : Finset ι) (f : ι → EuclN → ℝ)
    (hf : ∀ j ∈ S, MemWkp (d := Module.finrank ℝ E) k 2 (f j) Ω) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => ∑ j ∈ S, f j y) Ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
  | insert a t ha iht =>
      have h_split : (fun y => ∑ j ∈ insert a t, f j y) =
          (fun y => f a y + ∑ j ∈ t, f j y) := by
        funext y; rw [Finset.sum_insert ha]
      rw [h_split]
      refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ
        (hf a (Finset.mem_insert_self a t)) ?_
      exact iht (fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MemWkpFinsetSum

/-! ## A uniform bound across a finite family of summand coefficients

For each chart direction `l` and component-pair `(P, Q)`, the per-summand bound
`wkpNorm_offKernelSmoothCoef_mul_le` yields a constant controlling that summand.
Since the indexing triples form a finite type, the sum of all those constants is
a single nonnegative constant bounding *every* summand simultaneously. -/

section UniformConstant

set_option linter.unusedSectionVars false in
/-- Given, for every element of a finite type, a nonnegative constant and an
order-`K` `wkpNorm` bound governed by it, the sum of all those constants is a
single nonnegative constant for which the same bound holds for every element. -/
private lemma exists_uniform_wkpNorm_bound
    {ι : Type*} [Finite ι] {K : ℕ}
    {Ω : Set EuclN} {f : ι → EuclN → ℝ} {a : ι → ℝ≥0∞}
    (h : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2 (f j) Ω ≤ ENNReal.ofReal C * a j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (f j) Ω ≤ ENNReal.ofReal C * a j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose Cf hCf_nn hCf using h
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), fun j => ?_⟩
  refine (hCf j).trans (mul_le_mul_left ?_ (a j))
  exact ENNReal.ofReal_le_ofReal
    (Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j))

end UniformConstant

/-! ## The `K`-graded explicit-norm bound for the cross-right gradient-divergence
limit -/

section MainBound

/-- **`K`-graded explicit-norm `wkpNorm` bound for the cross-right
gradient-divergence limit.** For a closed Riemannian manifold `(M, g)`, ranks
`(r, s)`, an eigenbasis index `i`, a chart center `α : M`, a base component
multi-index `P₀`, and an iteration order `K`, if every partition-of-unity
Euclidean chart component of the `L²`-coercion of the eigenvector resolvent
`eigenvectorResolvent g r s h_atlas i` is iterated Sobolev regular of order
`K + 1` (`W^{K+1,2}`), then there is a nonnegative constant `C` such that the
order-`K` iterated Euclidean Sobolev norm of the cross-right gradient-divergence
limit `crossRightGradCoeffDivLimit g r s h_atlas i α P₀` is bounded by
`ENNReal.ofReal C` times the sum of the order-`K` `wkpNorm`s of the two atom
families: the cutoff chart-component limit objects
`crossRightLimitComponent g r s h_atlas i α P` (indexed by the component
multi-index `P`), and the cutoff chart-partial limit objects
`cutoffPartialLpLimit g r s h_atlas i α P l` (indexed by `P` and the chart
direction `l`).

This is the order-`K` `wkpNorm` analogue of the order-`0` weighted-`eLpNorm`
bound `eLpNorm_crossRightGradCoeffDivLimit_le`; the right-hand side keeps the
same two atom families verbatim as aggregate terms.

`crossRightGradCoeffDivLimit` is, by definition, a sum of two three-fold finite
sums over `(l, P, Q)`. Each summand is a product
`Set.indicator (chartPouKernel α) c · w` of a kernel-indicator-cut `C^∞`
coefficient `c` (the test-independent factor `crossRightDivFactor`, or its
chart-Euclidean partial — each vanishing off the compact partition-of-unity
kernel) with a `W^{K,2}` atom `w` (`crossRightLimitComponent` for the
component-atom group, `cutoffPartialLpLimit` for the chart-partial-atom group).
The kernel indicator is the identity, and the per-summand bound
`wkpNorm_offKernelSmoothCoef_mul_le` controls each summand's order-`K` norm by a
constant times the atom's. The atom in the component-atom group depends only on
`P`, the atom in the chart-partial-atom group only on `(P, l)`; bounding each
atom's `wkpNorm` by the full atom-family sum, summing the resulting constant
over the (finitely many) triples — folding the triple-index cardinality and the
coefficient sup constants into the single `C` — and applying the triangle
inequality across the two groups gives the estimate. -/
theorem wkpNorm_crossRightGradCoeffDivLimit_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          ((∑ P : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) K 2
                ((crossRightLimitComponent (I := I) (M := M)
                    g r s h_atlas i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  wkpNorm (d := Module.finrank ℝ E) K 2
                    ((cutoffPartialLpLimit (I := I) (M := M)
                        g r s h_atlas i α P l :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- Abbreviations for the two atom families and the two `wkpNorm`-sum targets.
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s h_atlas i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s h_atlas i α P l :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω with hSumpart_def
  -- The two atom families are `W^{K,2}` on the chart target, from `h_pou`.
  have hAcomp_memWkp : ∀ P : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (Acomp P) Ω := by
    intro P
    rw [hAcomp_def, hΩ_def]
    exact crossRightLimitComponent_memWkp (I := I) (M := M)
      g r s h_atlas i α P K h_pou
  have hApart_memWkp : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Apart P l) Ω := by
    intro P l
    rw [hApart_def, hΩ_def]
    exact cutoffPartialLpLimit_memWkp (I := I) (M := M)
      g r s h_atlas i α P l K h_pou
  -- The triple-index type for the two three-fold sums.
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  -- The component-atom-group summand, as a function indexed by `(l, P, Q)`.
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  -- The chart-partial-atom-group summand, as a function indexed by `(l, P, Q)`.
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  -- Each component-atom summand is the identity-cut `C^∞` coefficient times the
  -- `W^{K,2}` atom: the indicator is the identity since the chart-Euclidean
  -- partial of `crossRightDivFactor` vanishes off the kernel.
  have hsummandComp_eq : ∀ j : ι, summandComp j =
      (fun y => euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M)
            g r s α P₀ j.1 j.2.1 j.2.2) y * Acomp j.2.1 y) := by
    intro j
    funext y
    simp only [hsummandComp_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hsummandPart_eq : ∀ j : ι, summandPart j =
      (fun y => crossRightDivFactor (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2 y * Apart j.2.1 j.1 y) := by
    intro j
    funext y
    simp only [hsummandPart_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  -- The per-summand `MemWkp` and `wkpNorm` data for the component-atom group.
  have hsummandComp_data : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
            ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω := by
    intro j
    rw [hsummandComp_eq j, hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (hAcomp_memWkp j.2.1)
  -- The per-summand `MemWkp` and `wkpNorm` data for the chart-partial-atom group.
  have hsummandPart_data : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
            ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω := by
    intro j
    rw [hsummandPart_eq j, hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (hApart_memWkp j.2.1 j.1)
  have hsummandComp_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω :=
    fun j => (hsummandComp_data j).1
  have hsummandPart_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω :=
    fun j => (hsummandPart_data j).1
  -- A uniform constant `Ccomp` controlling every component-atom-group summand.
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ι,
          wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
            ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω :=
    exists_uniform_wkpNorm_bound (fun j => (hsummandComp_data j).2)
  -- A uniform constant `Cpart` controlling every chart-partial-atom-group
  -- summand.
  obtain ⟨Cpart, hCpart_nn, hCpart⟩ :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j : ι,
          wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
            ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω :=
    exists_uniform_wkpNorm_bound (fun j => (hsummandPart_data j).2)
  -- `crossRightGradCoeffDivLimit` is the sum of the two three-fold sums of
  -- functions; rewrite the pointwise nested sums as single `Finset.sum`s of
  -- functions over the triple-index `ι`.
  have h_funcA : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  -- The two three-fold-sum function-groups, as single `ι`-sums of functions.
  have hsumComp_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandComp j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandComp
      (fun j _ => hsummandComp_memWkp j)
  have hsumPart_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandPart j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandPart
      (fun j _ => hsummandPart_memWkp j)
  -- The triangle inequality: across the two three-fold sums, then within each.
  have h_triangle :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀) Ω
        ≤ (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ =
        (fun y => (∑ j : ι, summandComp j y) + (∑ j : ι, summandPart j y)) := by
      funext y
      unfold crossRightGradCoeffDivLimit
      rw [h_funcA y, h_funcB y]
    rw [h_split]
    refine le_trans
      (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hsumComp_memWkp hsumPart_memWkp) (add_le_add ?_ ?_)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandComp
        (fun j _ => hsummandComp_memWkp j)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandPart
        (fun j _ => hsummandPart_memWkp j)
  -- The component-atom-group sum: each summand's atom `wkpNorm` is bounded by the
  -- full component-atom sum `Sumcomp`, so every summand is `≤ ofReal Ccomp *
  -- Sumcomp`; the triple-sum of that constant is `card ι • (ofReal Ccomp *
  -- Sumcomp)`.
  have h_groupA :
      (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
          ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum
        (f := fun P => wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω)
        (fun P _ => zero_le _) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  -- The chart-partial-atom-group sum: each summand's atom `wkpNorm` is bounded by
  -- the full chart-partial-atom sum `Sumpart`.
  have h_groupB :
      (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
          ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum
          (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω)
          (fun P _ => zero_le _) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum
        (f := fun l => wkpNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 l) Ω)
        (fun l _ => zero_le _) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  -- Assemble: the headline constant is the larger of the two group constants.
  refine ⟨max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart),
    le_max_of_le_left (by positivity), ?_⟩
  -- The two group constants are dominated by their max.
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀) Ω
        ≤ (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) :=
        h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

end MainBound

/-! ## The factor-uniform off-kernel-vanishing smooth-coefficient `wkpNorm` bound

The `factor`-hoisted twin of `wkpNorm_offKernelSmoothCoef_mul_le`: a *single*
nonnegative constant — built purely from the coefficient's iterated-derivative
bounds, with no dependence on the factor — controls the order-`K` `wkpNorm` of
the product `coef · factor` for *every* `W^{K,2}` factor simultaneously. The
constant is the constant supplied by the `factor`-polymorphic global-smoothness
Leibniz bound `wkpNorm_smul_smooth_bounded_le`, whose `∀ {u}` quantifier already
exposes the factor-uniformity; it is hoisted before the `∀ factor`. -/

section OffKernelCoefBoundUniform

set_option linter.unusedSectionVars false in
/-- **Factor-uniform off-kernel-vanishing smooth-coefficient `wkpNorm` bound.**
The `factor`-uniform companion of `wkpNorm_offKernelSmoothCoef_mul_le`: for a
coefficient `coef : EuclN → ℝ` that is `C^∞` on the open Euclidean chart target
and vanishes pointwise off a compact kernel `Kkern` inside the chart target,
there is a *single* nonnegative constant `C` such that for *every* factor in
`MemWkp K 2` on the chart target,

```
wkpNorm K 2 (fun y => coef y * factor y) (chartTargetEuclid α)
  ≤ ENNReal.ofReal C * wkpNorm K 2 factor (chartTargetEuclid α).
```

The off-kernel vanishing makes `coef` globally `C^∞` and compactly supported; a
uniform bound on its iterated derivatives up to order `K` feeds the
factor-polymorphic global-smoothness Leibniz bound
`wkpNorm_smul_smooth_bounded_le`, whose constant is independent of the factor.
The `∀ factor` therefore moves inside the `∃ C`. -/
private lemma wkpNorm_offKernelSmoothCoef_mul_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ,
        MemWkp (d := Module.finrank ℝ E) K 2 factor
            (chartTargetEuclid (I := I) (M := M) α) →
          wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => coef y * factor y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              wkpNorm (d := Module.finrank ℝ E) K 2 factor
                (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The closed support of `coef` sits inside the compact kernel, hence in `Ω`.
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  -- `coef` is globally `C^∞`: smooth on `tsupport coef ⊆ Ω`, zero off it.
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  -- A uniform bound on the iterated derivatives of `coef` up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  -- The factor-polymorphic global-smoothness Leibniz bound for the coefficient:
  -- its constant `Kc` is independent of the factor, so it is hoisted before the
  -- `∀ factor`.
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hcoef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  exact ⟨Kc, le_of_lt hKc_pos, fun factor hfactor => hKc_bd hfactor⟩

end OffKernelCoefBoundUniform

/-! ## The eigenbasis-uniform `K`-graded explicit-norm bound for the cross-right
gradient-divergence limit -/

section MainBoundUniform

/-- **Eigenbasis-uniform `K`-graded explicit-norm `wkpNorm` bound for the
cross-right gradient-divergence limit.** The eigenbasis-uniform companion of
`wkpNorm_crossRightGradCoeffDivLimit_le`: a *single* nonnegative constant `C`,
independent of the eigenbasis index `i`, serves every `i` simultaneously — the
`∀ i` quantifier moved inside the `∃ C`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a base component multi-index `P₀`, and an iteration order `K`, given
the order-`K + 1` `MemWkp` regularity hypothesis `h_pou` on the
resolvent-inclusion partition-of-unity chart components — phrased uniformly over
`i` — there is a nonnegative constant `C` such that, for every `i`, the order-`K`
iterated Euclidean Sobolev norm of the cross-right gradient-divergence limit
`crossRightGradCoeffDivLimit g r s h_atlas i α P₀` is bounded by
`ENNReal.ofReal C` times the sum of the order-`K` `wkpNorm`s of its two atom
families.

No exposed eigenvalue factor appears: the witness constant of
`wkpNorm_crossRightGradCoeffDivLimit_le` is the maximum of two triple-index
cardinality multiples of constants supplied by the off-kernel smooth-coefficient
bound `wkpNorm_offKernelSmoothCoef_mul_le`, whose constant is the
iterated-derivative data of the test-independent `C^∞` factor
`crossRightDivFactor` (and its chart-Euclidean partial) — chart-geometric data,
independent of the abstract resolvent element and hence of `i`. That single
constant is hoisted before the `∀ i` via the factor-uniform companion
`wkpNorm_offKernelSmoothCoef_mul_le_uniform`. -/
theorem wkpNorm_crossRightGradCoeffDivLimit_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        wkpNorm (d := Module.finrank ℝ E) K 2
            (crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                wkpNorm (d := Module.finrank ℝ E) K 2
                  ((crossRightLimitComponent (I := I) (M := M)
                      g r s h_atlas i α P :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    wkpNorm (d := Module.finrank ℝ E) K 2
                      ((cutoffPartialLpLimit (I := I) (M := M)
                          g r s h_atlas i α P l :
                          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                          EuclN → ℝ)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- The triple-index type for the two three-fold sums.
  set ι : Type _ :=
    Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s with hι_def
  -- Per triple `j`, a *factor-uniform* constant for the component-atom-group
  -- coefficient (the chart-Euclidean partial of `crossRightDivFactor`) — built
  -- purely from that `C^∞` factor, independent of the resolvent element and
  -- hence of `i`.
  have hCcomp_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ, MemWkp (d := Module.finrank ℝ E) K 2 factor Ω →
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => euclidPartial (E := E) j.1
                (crossRightDivFactor (I := I) (M := M)
                  g r s α P₀ j.1 j.2.1 j.2.2) y * factor y) Ω
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor Ω := by
    intro j
    rw [hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le_uniform (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
  -- Per triple `j`, a factor-uniform constant for the chart-partial-atom-group
  -- coefficient (`crossRightDivFactor` itself) — likewise `i`-independent.
  have hCpart_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ, MemWkp (d := Module.finrank ℝ E) K 2 factor Ω →
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => crossRightDivFactor (I := I) (M := M)
                g r s α P₀ j.1 j.2.1 j.2.2 y * factor y) Ω
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor Ω := by
    intro j
    rw [hΩ_def]
    exact wkpNorm_offKernelSmoothCoef_mul_le_uniform (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
  -- Fold the per-triple constants into a single triple-uniform constant for
  -- each group: the sum over the (finitely many) triples.
  choose Ccompf hCcompf_nn hCcompf using hCcomp_data
  choose Cpartf hCpartf_nn hCpartf using hCpart_data
  set Ccomp : ℝ := ∑ j : ι, Ccompf j with hCcomp_def
  set Cpart : ℝ := ∑ j : ι, Cpartf j with hCpart_def
  have hCcomp_nn : 0 ≤ Ccomp :=
    Finset.sum_nonneg (fun j _ => hCcompf_nn j)
  have hCpart_nn : 0 ≤ Cpart :=
    Finset.sum_nonneg (fun j _ => hCpartf_nn j)
  -- Each per-triple constant is dominated by the group sum.
  have hCcompf_le : ∀ j : ι, Ccompf j ≤ Ccomp := fun j =>
    Finset.single_le_sum (fun k _ => hCcompf_nn k) (Finset.mem_univ j)
  have hCpartf_le : ∀ j : ι, Cpartf j ≤ Cpart := fun j =>
    Finset.single_le_sum (fun k _ => hCpartf_nn k) (Finset.mem_univ j)
  -- The headline constant: the larger of the two triple-index cardinality
  -- multiples — hoisted before the `∀ i`.
  refine ⟨max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart),
    le_max_of_le_left (by positivity), fun i => ?_⟩
  -- The remainder reproduces the per-`i` proof body for the fixed index `i`,
  -- with the factor-uniform per-triple constants in place of the per-summand
  -- ones.
  -- Abbreviations for the two atom families and the two `wkpNorm`-sum targets.
  set Acomp : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => ((crossRightLimitComponent (I := I) (M := M)
      g r s h_atlas i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hAcomp_def
  set Apart : TensorCompIdx (E := E) r s → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun P l => ((cutoffPartialLpLimit (I := I) (M := M)
      g r s h_atlas i α P l :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) with hApart_def
  set Sumcomp : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω with hSumcomp_def
  set Sumpart : ℝ≥0∞ :=
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ l : Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω with hSumpart_def
  -- The two atom families are `W^{K,2}` on the chart target, from `h_pou i`.
  have hAcomp_memWkp : ∀ P : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (Acomp P) Ω := by
    intro P
    rw [hAcomp_def, hΩ_def]
    exact crossRightLimitComponent_memWkp (I := I) (M := M)
      g r s h_atlas i α P K (h_pou i)
  have hApart_memWkp : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Apart P l) Ω := by
    intro P l
    rw [hApart_def, hΩ_def]
    exact cutoffPartialLpLimit_memWkp (I := I) (M := M)
      g r s h_atlas i α P l K (h_pou i)
  -- The component-atom-group summand, as a function indexed by `(l, P, Q)`.
  set summandComp : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2)) y *
      Acomp j.2.1 y with hsummandComp_def
  -- The chart-partial-atom-group summand, as a function indexed by `(l, P, Q)`.
  set summandPart : ι → EuclN → ℝ :=
    fun j y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        (crossRightDivFactor (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2) y *
      Apart j.2.1 j.1 y with hsummandPart_def
  -- Each component-atom summand is the identity-cut `C^∞` coefficient times the
  -- `W^{K,2}` atom: the indicator is the identity since the chart-Euclidean
  -- partial of `crossRightDivFactor` vanishes off the kernel.
  have hsummandComp_eq : ∀ j : ι, summandComp j =
      (fun y => euclidPartial (E := E) j.1
          (crossRightDivFactor (I := I) (M := M)
            g r s α P₀ j.1 j.2.1 j.2.2) y * Acomp j.2.1 y) := by
    intro j
    funext y
    simp only [hsummandComp_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  have hsummandPart_eq : ∀ j : ι, summandPart j =
      (fun y => crossRightDivFactor (I := I) (M := M)
          g r s α P₀ j.1 j.2.1 j.2.2 y * Apart j.2.1 j.1 y) := by
    intro j
    funext y
    simp only [hsummandPart_def]
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK,
        crossRightDivFactor_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hyK]
  -- The per-summand `wkpNorm` bound for the component-atom group, from the
  -- factor-uniform constant `Ccompf j` applied to the atom `Acomp j.2.1`.
  have hCcomp : ∀ j : ι,
      wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
        ENNReal.ofReal Ccomp *
          wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp j.2.1) Ω := by
    intro j
    rw [hsummandComp_eq j]
    refine (hCcompf j (Acomp j.2.1) (hAcomp_memWkp j.2.1)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCcompf_le j)) _
  -- The per-summand `wkpNorm` bound for the chart-partial-atom group.
  have hCpart : ∀ j : ι,
      wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
        ENNReal.ofReal Cpart *
          wkpNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 j.1) Ω := by
    intro j
    rw [hsummandPart_eq j]
    refine (hCpartf j (Apart j.2.1 j.1) (hApart_memWkp j.2.1 j.1)).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCpartf_le j)) _
  -- The per-summand `MemWkp` data for both groups, via `MemWkp.smul_smooth`'s
  -- closure through the `wkpNorm_offKernelSmoothCoef_mul_le` workhorse.
  have hsummandComp_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandComp j) Ω := by
    intro j
    rw [hsummandComp_eq j, hΩ_def]
    exact (wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (by rw [← hΩ_def]; exact hAcomp_memWkp j.2.1)).1
  have hsummandPart_memWkp : ∀ j : ι,
      MemWkp (d := Module.finrank ℝ E) K 2 (summandPart j) Ω := by
    intro j
    rw [hsummandPart_eq j, hΩ_def]
    exact (wkpNorm_offKernelSmoothCoef_mul_le (I := I) (M := M) α K
      hKα_compact hKα_in
      (crossRightDivFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ j.1 j.2.1 j.2.2)
      (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s α P₀ j.1 j.2.1 j.2.2 hy)
      (by rw [← hΩ_def]; exact hApart_memWkp j.2.1 j.1)).1
  -- `crossRightGradCoeffDivLimit` is the sum of two three-fold sums of
  -- functions; rewrite the pointwise nested sums as single `Finset.sum`s of
  -- functions over the triple-index `ι`.
  have h_funcA : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (euclidPartial (E := E) l
                    (crossRightDivFactor (I := I) (M := M)
                      g r s α P₀ l P Q)) y *
                (crossRightLimitComponent (I := I) (M := M)
                  g r s h_atlas i α P :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandComp j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  have h_funcB : ∀ y : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
          ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q) y *
                (cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                  EuclN → ℝ) y)
        = ∑ j : ι, summandPart j y := by
    intro y
    rw [show (Finset.univ : Finset ι) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
            TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s)) =
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
          (Finset.univ : Finset (TensorCompIdx (E := E) r s)) from
      (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
  -- The two three-fold-sum function-groups, as single `ι`-sums of functions.
  have hsumComp_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandComp j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandComp
      (fun j _ => hsummandComp_memWkp j)
  have hsumPart_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, summandPart j y) Ω :=
    memWkp_finset_sum_iota hΩ_open
      (Finset.univ : Finset ι) summandPart
      (fun j _ => hsummandPart_memWkp j)
  -- The triangle inequality: across the two three-fold sums, then within each.
  have h_triangle :
      wkpNorm (d := Module.finrank ℝ E) K 2
          (crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀) Ω
        ≤ (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) := by
    have h_split : crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s h_atlas i α P₀ =
        (fun y => (∑ j : ι, summandComp j y) + (∑ j : ι, summandPart j y)) := by
      funext y
      unfold crossRightGradCoeffDivLimit
      rw [h_funcA y, h_funcB y]
    rw [h_split]
    refine le_trans
      (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hsumComp_memWkp hsumPart_memWkp) (add_le_add ?_ ?_)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandComp
        (fun j _ => hsummandComp_memWkp j)
    · exact wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset ι) summandPart
        (fun j _ => hsummandPart_memWkp j)
  -- The component-atom-group sum: each summand's atom `wkpNorm` is bounded by
  -- the full component-atom sum `Sumcomp`, so every summand is `≤ ofReal Ccomp *
  -- Sumcomp`; the triple-sum of that constant is `card ι • (ofReal Ccomp *
  -- Sumcomp)`.
  have h_groupA :
      (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp := by
    have h_each : ∀ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω ≤
          ENNReal.ofReal Ccomp * Sumcomp := by
      intro j
      refine (hCcomp j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Ccomp))
      rw [hSumcomp_def]
      exact Finset.single_le_sum
        (f := fun P => wkpNorm (d := Module.finrank ℝ E) K 2 (Acomp P) Ω)
        (fun P _ => zero_le _) (Finset.mem_univ j.2.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  -- The chart-partial-atom-group sum: each summand's atom `wkpNorm` is bounded
  -- by the full chart-partial-atom sum `Sumpart`.
  have h_groupB :
      (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart := by
    have h_each : ∀ j : ι,
        wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω ≤
          ENNReal.ofReal Cpart * Sumpart := by
      intro j
      refine (hCpart j).trans (mul_le_mul_right ?_ (ENNReal.ofReal Cpart))
      rw [hSumpart_def]
      refine le_trans ?_
        (Finset.single_le_sum
          (f := fun P => ∑ l : Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) K 2 (Apart P l) Ω)
          (fun P _ => zero_le _) (Finset.mem_univ j.2.1))
      exact Finset.single_le_sum
        (f := fun l => wkpNorm (d := Module.finrank ℝ E) K 2 (Apart j.2.1 l) Ω)
        (fun l _ => zero_le _) (Finset.mem_univ j.1)
    refine le_trans (Finset.sum_le_sum (fun j _ => h_each j)) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  -- The two group constants are dominated by their max.
  have hCcomp_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hCpart_le :
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) ≤
        ENNReal.ofReal
          (max ((Fintype.card ι : ℝ) * Ccomp) ((Fintype.card ι : ℝ) * Cpart)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀) Ω
        ≤ (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandComp j) Ω)
          + (∑ j : ι, wkpNorm (d := Module.finrank ℝ E) K 2 (summandPart j) Ω) :=
        h_triangle
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Ccomp) * Sumcomp
          + ENNReal.ofReal ((Fintype.card ι : ℝ) * Cpart) * Sumpart :=
        add_le_add h_groupA h_groupB
    _ ≤ ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * Sumcomp
          + ENNReal.ofReal
              (max ((Fintype.card ι : ℝ) * Ccomp)
                ((Fintype.card ι : ℝ) * Cpart)) * Sumpart :=
        add_le_add (mul_le_mul_left hCcomp_le _)
          (mul_le_mul_left hCpart_le _)
    _ = ENNReal.ofReal
            (max ((Fintype.card ι : ℝ) * Ccomp)
              ((Fintype.card ι : ℝ) * Cpart)) * (Sumcomp + Sumpart) :=
        (mul_add _ _ _).symm

end MainBoundUniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
