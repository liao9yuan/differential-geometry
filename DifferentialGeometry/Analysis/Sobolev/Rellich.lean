import DifferentialGeometry.Analysis.Sobolev.EuclideanRellich
import DifferentialGeometry.Analysis.Sobolev.Chart
import DifferentialGeometry.Analysis.Sobolev.ChartAtlas
import DifferentialGeometry.Integral.Measure.Glue
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.External.DeGiorgi.LpFunctionToolkit
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Rellich-Kondrachov compact embedding on a closed Riemannian manifold

Infrastructure for the Rellich-Kondrachov compact embedding
`H^{k+1}(M) ↪ L^p(M, μ_g)` on a closed (compact, boundaryless) smooth
Riemannian manifold `(M, g)`.

This file develops:

* The key reduction
  `riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn`: for any
  measurable `F : M → ℝ≥0∞` supported in the chart-α source, the
  `μ_g`-integral of `F` equals its `chartLocalMeasure g α`-integral. This
  follows from the partition-of-unity decomposition of `μ_g` together with
  the chart-overlap equality of chart-local measures.
* The pull-back operation `pullbackToM` taking a function on the chart-target
  Euclidean space to a function on `M`, supported in the chart source.
* Compatibility of `pullbackToM` with `chartPushed`: if `ρ` is a smooth
  partition of unity subordinate to the chart family, then
  `pullbackToM I α (chartPushed ρ α u) = ρ_α · u`.
* Linearity of `pullbackToM` in its function argument.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Lemma: POU sum equals 1 on the global support finset

On compact `M`, the chart-atlas POU `(ρ_α)` has only finitely many indices
`α` with non-empty support, gathered in the `Finset` `chartAtlasPOU_finset`.
Summing the POU values over this finset yields `1` at every point `x ∈ M`. -/

lemma chartAtlasPOU_finset_sum_eq_one
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (x : M) :
    ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x = 1 := by
  classical
  -- The finsupport at `x` is a subset of the global support set.
  have hsubset :
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).finsupport x ⊆
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) := by
    intro α hα
    rw [DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset_mem]
    -- α ∈ finsupport x means ρ_α x ≠ 0, so x ∈ Function.support ρ_α, so the support is non-empty.
    rw [SmoothPartitionOfUnity.mem_finsupport] at hα
    exact ⟨x, hα⟩
  -- Apply ρ.sum_finsupport' which gives sum over finsupport = 1.
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).sum_finsupport' x
    (Set.mem_univ x) hsubset

/-! ## Lemma: integral of a chart-α-supported function via μ_g equals via chartLocalMeasure g α

This is the key reduction: for any nonneg measurable function `F : M → ℝ≥0∞`
supported in the chart-α source (i.e., zero outside `(chartAt H α).source`),
its `μ_g`-integral equals its `chartLocalMeasure g α`-integral.

Mathematically, this works because `μ_g = Σ_β ρ_β · chartLocalMeasure g β`,
and on the support of `F` (which is in `chart α source`), each
`chartLocalMeasure g β` agrees with `chartLocalMeasure g α`
(`chartLocalMeasure_restrict_overlap_eq`), and the POU values sum to one. -/

theorem riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hF_supp : ∀ x, x ∉ (chartAt H α).source → F x = 0) :
    ∫⁻ x, F x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) =
      ∫⁻ x, F x ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α) := by
  classical
  -- Step 1: expand μ_g via riemannianMeasure_lintegral_eq.
  rw [DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq
    (I := I) g (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) hF]
  -- We have: ∫⁻ F dμ_g = Σ' β, ∫⁻ ρ_β · F d(chartLocalMeasure g β)
  -- We want: this = ∫⁻ F d(chartLocalMeasure g α).
  -- Step 2: For β not in chartAtlasPOU_finset, ρ_β = 0 → integrand is 0.
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have htsum_eq_finsum :
      ∑' β : M, ∫⁻ x, ENNReal.ofReal
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x)
              * F x
            ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g β) =
        ∑ β ∈ S, ∫⁻ x, ENNReal.ofReal
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x)
              * F x
            ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g β) := by
    rw [tsum_eq_sum]
    intro β hβ
    -- β ∉ S means ρ_β = 0 everywhere, so integrand is 0.
    have hρ_zero : ∀ x : M,
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x = 0 := fun x =>
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hβ x
    have hint_zero : ∀ x : M, ENNReal.ofReal
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x = 0 := by
      intro x
      rw [hρ_zero x]
      simp
    have hintegrand : (fun x : M => ENNReal.ofReal
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x) =
        (fun _ : M => (0 : ℝ≥0∞)) := by
      funext x
      exact hint_zero x
    rw [hintegrand]
    simp
  rw [htsum_eq_finsum]
  -- Step 3: For each β ∈ S, transfer the integral on `chartLocalMeasure g β` to
  -- `chartLocalMeasure g α` using the support-in-chart-α-source hypothesis on F.
  have h_each_eq : ∀ β ∈ S,
      ∫⁻ x, ENNReal.ofReal
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x
          ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g β) =
        ∫⁻ x, ENNReal.ofReal
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x
          ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α) := by
    intro β hβS
    apply DifferentialGeometry.Integral.Measure.chartLocalMeasure_lintegral_eq_of_support_in_overlap
      (I := I) g β α
    · exact ((DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β)).mul hF
    · intro x hx_not_overlap
      -- x ∉ (chart β source) ∩ (chart α source)
      simp only [Set.mem_inter_iff, not_and] at hx_not_overlap
      by_cases hxβ : x ∈ (chartAt H β).source
      · -- x ∈ chart β source but x ∉ chart α source
        have hxα : x ∉ (chartAt H α).source := hx_not_overlap hxβ
        rw [hF_supp x hxα]
        simp
      · -- x ∉ chart β source means x ∉ tsupport ρ_β, so ρ_β x = 0.
        have hρβ_zero :
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x = 0 := by
          have hsub :=
            DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M) β
          have hxnotsupp : x ∉ tsupport
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) := by
            intro hcontra
            exact hxβ (hsub hcontra)
          exact image_eq_zero_of_notMem_tsupport hxnotsupp
        rw [hρβ_zero]
        simp
  -- Step 4: rewrite each integral using h_each_eq, then sum.
  rw [Finset.sum_congr rfl h_each_eq]
  -- Now: Σ β ∈ S, ∫⁻ ofReal(ρ_β) · F d(chartLocalMeasure g α) = ∫⁻ F d(chartLocalMeasure g α).
  -- Pull out the sum: Σ_β ofReal(ρ_β) · F = ofReal(Σ_β ρ_β) · F = ofReal(1) · F = F.
  -- We need to be careful about the ENNReal sum.
  have hF_eq : ∀ x : M,
      ENNReal.ofReal
          (∑ β ∈ S, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x =
        ∑ β ∈ S, ENNReal.ofReal
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) * F x := by
    intro x
    -- ENNReal.ofReal is a Finset-sum-additive when the summands are nonneg.
    have hnonneg : ∀ β ∈ S,
        0 ≤ (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x := fun β _ =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg β x
    have hsum_eq : ENNReal.ofReal
          (∑ β ∈ S, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) =
        ∑ β ∈ S, ENNReal.ofReal
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) := by
      induction S using Finset.cons_induction with
      | empty => simp
      | cons a s has ih =>
          rw [Finset.sum_cons, Finset.sum_cons]
          have hnonneg' :
              0 ≤ (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M a : M → ℝ) x :=
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg a x
          have hsum_nn :
              0 ≤ ∑ β ∈ s, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x :=
            Finset.sum_nonneg fun β _ =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg β x
          rw [ENNReal.ofReal_add hnonneg' hsum_nn]
          -- Recursively apply ih.
          have hih : ENNReal.ofReal
              (∑ β ∈ s, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) =
            ∑ β ∈ s, ENNReal.ofReal
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) := by
            -- We need ih applied to s. ih takes a hypothesis about s; here we have it.
            apply ih
          rw [hih]
    rw [hsum_eq, Finset.sum_mul]
  have hsum_one : ∀ x : M,
      ENNReal.ofReal
          (∑ β ∈ S, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) =
        1 := by
    intro x
    rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x]
    simp
  -- Now compute:
  -- Σ β ∈ S, ∫⁻ ofReal(ρ_β) · F d(chartLocalMeasure g α)
  -- = ∫⁻ Σ β ∈ S, ofReal(ρ_β) · F d(chartLocalMeasure g α)
  -- = ∫⁻ F · 1 d(chartLocalMeasure g α) [using hsum_one]
  -- = ∫⁻ F d(chartLocalMeasure g α).
  rw [← MeasureTheory.lintegral_finset_sum]
  · refine MeasureTheory.lintegral_congr (fun x => ?_)
    rw [← hF_eq x, hsum_one x, one_mul]
  · intro β _
    exact ((DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β)).mul hF

/-! ## Pull-back of an `EuclideanSpace`-valued function to `M`

Given a function `w : EuclideanSpace ℝ (Fin n) → ℝ` and a chart point `α : M`,
the pull-back `pullbackToM g α w : M → ℝ` is defined as `w ∘ (toEuclidean ∘ extChartAt I α)`
on `(chartAt H α).source` and zero outside that set.

This is the inverse operation of `chartPushed`: if `u : M → ℝ` is given and we
chart-push by `α`, the resulting Euclidean function pulled back equals
`(ρ_α : C^∞⟮I, M; ℝ⟯) · u` (when ρ is the POU). -/

/-- Pull-back of an `EuclideanSpace`-valued function `w` to `M` via the chart at `α`.
Set to zero outside the chart source. -/
def pullbackToM
    (I : ModelWithCorners ℝ E H) (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      w (toEuclidean (extChartAt I α x))
    else 0

/-- On the chart source, the pull-back of a function `w` evaluates as `w` composed with the chart. -/
lemma pullbackToM_apply_of_mem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    pullbackToM (M := M) I α w x =
      w (toEuclidean (extChartAt I α x)) := by
  classical
  unfold pullbackToM; simp [hx]

/-- Outside the chart source, the pull-back of a function is zero. -/
lemma pullbackToM_apply_of_notMem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 := by
  classical
  unfold pullbackToM; simp [hx]

/-- The pull-back of a function is supported in the chart source. -/
lemma pullbackToM_support_subset_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (pullbackToM (M := M) I α w) ⊆ (chartAt H α).source := by
  intro x hx
  by_contra h
  apply hx
  exact pullbackToM_apply_of_notMem (M := M) (I := I) α w h

/-- Outside the chart source, the pull-back is zero. -/
lemma pullbackToM_zero_of_notMem_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 :=
  pullbackToM_apply_of_notMem (M := M) (I := I) α w hx

/-- The pull-back is linear in `w`: linearity for addition. -/
lemma pullbackToM_add (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y + w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x +
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

/-- The pull-back is linear in `w`: linearity for subtraction. -/
lemma pullbackToM_sub (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y - w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x -
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

/-- The pull-back of the chart-pushed function for a subordinate POU recovers
the POU-weighted function. -/
lemma pullbackToM_chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    pullbackToM (M := M) I α
      (chartPushed (I := I) (M := M) ρ α u) =
        fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · -- For x in chart source, compute via pullbackToM_apply_of_mem.
    rw [pullbackToM_apply_of_mem (M := M) (I := I) α _ hx]
    -- Apply chartPushed definition: it's ρ α (chart^{-1}(toEuclidean.symm y)) · u (chart^{-1}(toEuclidean.symm y))
    unfold chartPushed
    -- Need: ρ α ((extChartAt I α).symm (toEuclidean.symm (toEuclidean (extChartAt I α x))))
    --     * u ((extChartAt I α).symm (toEuclidean.symm (toEuclidean (extChartAt I α x))))
    --   = ρ α x * u x
    have htoeucl : toEuclidean.symm (toEuclidean (extChartAt I α x)) = extChartAt I α x := by
      simp
    rw [htoeucl]
    have hsymm : (extChartAt I α).symm (extChartAt I α x) = x := by
      apply (extChartAt I α).left_inv
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    rw [hsymm]
  · -- For x outside chart source, both sides should be zero.
    rw [pullbackToM_apply_of_notMem (M := M) (I := I) α _ hx]
    -- Need: 0 = ρ α x · u x. Since ρ is subordinate, x ∉ tsupport ρ_α (else x ∈ chart α source by hρ).
    have hxnotsupp : x ∉ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      intro hcontra
      exact hx (hρ α hcontra)
    have hρα_zero : ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hxnotsupp
    rw [hρα_zero]
    ring

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
