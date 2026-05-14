import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ComponentSobolevBoundFinal
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichOnM

/-!
# Per-chart per-component scalar Rellich diagonal extraction for tensor sections

For a closed Riemannian manifold `(M, g)` and a sequence
`S : ℕ → SmoothCcTensorH1 g r s` of smooth compactly-supported `H¹` tensor
sections, every chart point `α ∈ chartAtlasPOU_finset I M` together with every
multi-index pair `(Idx, Jdx)` produces a scalar field
`tensorChartComponentScalar g r s (S n).toCcTensor α Idx Jdx` on `M`. This file
delivers a **single** subsequence extraction `φ : ℕ → ℕ` which, simultaneously
for every triple `(α, Idx, Jdx)` in the finite triple set, yields convergence
in `L²` of the Riemannian volume measure.

The construction proceeds by:

* per fixed `(α, Idx, Jdx)`, applying the closed-manifold Rellich–Kondrachov
  subsequence extraction `rellich_kondrachov_chart_seq` to the component
  sequence, under the hypothesis that the chart-Sobolev norms of the
  components are uniformly bounded across `n`;
* iterating a finite-Finset diagonal extraction over the triple set
  `S.attach × Finset.univ` with `S = chartAtlasPOU_finset I M`.

The uniform component bound is taken as an explicit hypothesis. Per-section
finiteness of each `wkpNormChart` is already known from
`tensorChartComponentScalar_wkpNormChart_lt_top`, and a per-section bound is
delivered by `tensorChartComponent_wkpNormChart_le_per_section`, but those
forms do not assemble a sequence-uniform constant. The downstream user
supplies the uniform bound separately.

## Headline theorems

* `tensorChartComponent_rellich_extraction_of_uniform_bound` — the diagonal
  extraction under an explicit uniform-in-`n` chart-Sobolev bound on the
  scalar components.
* `tensorChartComponent_rellich_extraction` — the same conclusion, restated
  in the natural per-section signature where the user passes the uniform
  bound as a hypothesis dependent on each `(α, Idx, Jdx)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

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

/-! ## Measurability of the scalar component field -/

/-- The manifold-side scalar field is measurable: it is smooth, hence
continuous, hence Borel measurable. -/
theorem tensorChartComponentScalar_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) := by
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  exact hsmooth.continuous.measurable

/-! ## Triple type and triple Finset

The data of a triple `(α, Idx, Jdx)` is packaged into a single dependent
product type. We restrict the `α` component to lie in
`chartAtlasPOU_finset I M`, and use `Fintype.univ` for the multi-index
components. The diagonalisation proceeds by `Finset.induction_on` over the
triple Finset. -/

/-- The triple type packaging `(α ∈ chartAtlasPOU_finset, Idx, Jdx)`. -/
private abbrev Triple (r s : ℕ) :=
  { α : M // α ∈ chartAtlasPOU_finset (I := I) (M := M) } ×
    (Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))

/-- The full triple Finset over the chart-atlas POU support set and the
multi-index Fintype. -/
private noncomputable def tripleFinset (r s : ℕ) :
    Finset (Triple (I := I) (M := M) r s) :=
  Finset.univ

/-! ## Per-triple Rellich extraction

For a fixed triple `(α, Idx, Jdx)` and a sequence of `H¹` tensor sections
`S` with the chart-Sobolev norm of the corresponding scalar component
uniformly bounded by `R`, the closed-manifold Rellich-Kondrachov subsequence
extraction `rellich_kondrachov_chart_seq` produces a strictly monotone
`σ : ℕ → ℕ` and a manifold-side `L²` limit `u_lim`. -/

/-- Single-triple Rellich extraction: given a sequence `S : ℕ → SmoothCcTensorH1`
and a triple `(α, Idx, Jdx)`, under a uniform chart-Sobolev bound on the
scalar components, extract a subsequence convergent in `L²` of the
Riemannian volume measure. -/
private lemma single_triple_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ n,
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ u_lim : M → ℝ,
        MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        Filter.Tendsto
          (fun j => eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                g r s (S (σ j)).toCcTensor α Idx Jdx b - u_lim b)
              2 (riemannianVolumeMeasure (I := I) (M := M) g))
          Filter.atTop (𝓝 0) := by
  classical
  -- Apply the closed-manifold Rellich theorem with `p = 2`.
  have hp_one : (1 : ℝ) < 2 := by norm_num
  -- Membership in `MemWkpChart g 1 2` for each component.
  have h_mem : ∀ n, MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal 2)
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) := by
    intro n
    have h2_eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
      simp
    rw [← h2_eq]
    exact tensorChartComponent_memWkpChart_one_two
      (I := I) (M := M) g r s (S n) α Idx Jdx
  -- Measurability of each component.
  have h_meas : ∀ n, Measurable
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) := by
    intro n
    exact tensorChartComponentScalar_measurable
      (I := I) (M := M) g r s (S n).toCcTensor α Idx Jdx
  -- Convert the uniform bound from `wkpNormChart g 1 2` to
  -- `wkpNormChart g 1 (ENNReal.ofReal 2)`, since Rellich expects the latter.
  have h_bdd : ∀ n, wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal 2)
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) ≤ ENNReal.ofReal R := by
    intro n
    have h2_eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
    rw [← h2_eq]
    exact hu_bdd n
  -- Invoke the closed-manifold Rellich subsequence theorem.
  obtain ⟨σ, hσ_mono, u_lim, hu_lim_memLp, h_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.rellich_kondrachov_chart_seq
      (I := I) (M := M) (E := E) (H := H) g hp_one
      h_meas h_mem h_bdd
  refine ⟨σ, hσ_mono, u_lim, ?_, ?_⟩
  · -- Rewrite the `MemLp` conclusion using `riemannianVolumeMeasure_def` and
    -- `ENNReal.ofReal 2 = (2 : ℝ≥0∞)`.
    have h2_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    have h_vol :
        riemannianVolumeMeasure (I := I) (M := M) g =
          riemannianMeasure (I := I) g (chartAtlasPOU I M) :=
      riemannianVolumeMeasure_def (I := I) (M := M) g
    rw [h_vol, ← h2_eq]
    exact hu_lim_memLp
  · -- Rewrite the `Tendsto` conclusion similarly.
    have h2_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    have h_vol :
        riemannianVolumeMeasure (I := I) (M := M) g =
          riemannianMeasure (I := I) g (chartAtlasPOU I M) :=
      riemannianVolumeMeasure_def (I := I) (M := M) g
    rw [h_vol, ← h2_eq]
    exact h_tendsto

/-! ## Stability under further subsequencing

If a sequence of `L²` differences tends to `0`, then so does any
subsequence-of-the-subsequence. We package this elementary stability
result in the form needed for the Finset induction step. -/

/-- Composing the L² convergence with a strictly monotone reindexing
preserves the convergence. -/
private lemma tendsto_eLpNorm_diff_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {S : ℕ → SmoothCcTensorH1 g r s}
    {φ : ℕ → ℕ} {u_lim : M → ℝ}
    (h_tendsto :
      Filter.Tendsto
        (fun j => eLpNorm
            (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
            2 (riemannianVolumeMeasure (I := I) (M := M) g))
        Filter.atTop (𝓝 0))
    {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ) :
    Filter.Tendsto
      (fun j => eLpNorm
          (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S ((φ ∘ ψ) j)).toCcTensor α Idx Jdx b - u_lim b)
          2 (riemannianVolumeMeasure (I := I) (M := M) g))
      Filter.atTop (𝓝 0) := by
  have h_at_top : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop_of_monotone hψ_mono.monotone
      (fun n => ⟨n, hψ_mono.id_le n⟩)
  exact h_tendsto.comp h_at_top

/-! ## Finite diagonal extraction over the triple Finset

By induction on the triple Finset: for each triple, apply the
single-triple extraction to the current subsequence; iterate. The output
subsequence works for every previously processed triple thanks to
`tendsto_eLpNorm_diff_comp`. -/

/-- **Finite diagonal extraction over a triple Finset.** Given a sequence
`S : ℕ → SmoothCcTensorH1 g r s` of `H¹` tensor sections and a uniform
chart-Sobolev bound on each scalar component indexed by a triple in `T`,
extract a single strictly monotone `φ : ℕ → ℕ` such that every triple in
`T` simultaneously enjoys `L²` convergence of its component subsequence. -/
private lemma diagonal_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R)
    (T : Finset (Triple (I := I) (M := M) r s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ t ∈ T, ∃ u_lim : M → ℝ,
        MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        Filter.Tendsto
          (fun j => eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ j)).toCcTensor t.1.1 t.2.1 t.2.2 b - u_lim b)
              2 (riemannianVolumeMeasure (I := I) (M := M) g))
          Filter.atTop (𝓝 0) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun t ht => ?_⟩
      exact absurd ht (Finset.notMem_empty t)
  | insert t T' ht_notin ih =>
      rcases ih with ⟨φ_T', hφ_T'_mono, hP_T'⟩
      -- Apply the single-triple extraction to the subsequence indexed by `φ_T'`.
      have hu_bdd_comp : ∀ n,
          wkpNormChart (I := I) (M := M) g 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ_T' n)).toCcTensor t.1.1 t.2.1 t.2.2) ≤
            ENNReal.ofReal R := fun n => hu_bdd t.1.1 t.2.1 t.2.2 (φ_T' n)
      obtain ⟨σ_t, hσ_t_mono, u_t, hu_t_memLp, h_tendsto_t⟩ :=
        single_triple_extraction (I := I) (M := M) g r s t.1.1 t.2.1 t.2.2
          (S := fun n => S (φ_T' n))
          (R := R) hu_bdd_comp
      refine ⟨φ_T' ∘ σ_t, hφ_T'_mono.comp hσ_t_mono, ?_⟩
      intro t' ht'
      rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
      · -- The new triple: just use `u_t` and the freshly-extracted convergence.
        refine ⟨u_t, hu_t_memLp, ?_⟩
        exact h_tendsto_t
      · -- An earlier triple: use the stability lemma to compose with `σ_t`.
        rcases hP_T' t' ht'_T' with ⟨u_t', hu_t'_memLp, h_tendsto_t'⟩
        refine ⟨u_t', hu_t'_memLp, ?_⟩
        -- The composed subsequence `φ_T' ∘ σ_t` reindexes the prior
        -- convergence at `φ_T'` by `σ_t`.
        exact tendsto_eLpNorm_diff_comp (I := I) (M := M) g r s t'.1.1 t'.2.1 t'.2.2
          h_tendsto_t' hσ_t_mono

/-! ## Headline diagonal extraction theorem

For a sequence of smooth compactly-supported `H¹` tensor sections with a
uniform chart-Sobolev bound on every scalar chart-frame component indexed
by `(α, Idx, Jdx)` in the finite triple set, there is a single
strictly-monotone subsequence such that every triple in the finite set
simultaneously enjoys `L²` convergence of its scalar component. -/

/-- **Headline theorem.** Per-`α` per-component scalar Rellich diagonal
extraction at the tensor level. For each
`α ∈ chartAtlasPOU_finset I M` and each multi-index pair `(Idx, Jdx)`, the
extracted subsequence's scalar component converges in `L²` of the
Riemannian volume measure to a manifold-side `L²` limit.

The hypothesis `hu_bdd` is a uniform-in-`n` chart-Sobolev bound on the
scalar components; per-section finiteness is delivered by
`tensorChartComponentScalar_wkpNormChart_lt_top`, but a sequence-uniform
bound requires the explicit hypothesis. -/
theorem tensorChartComponent_rellich_extraction_of_uniform_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) := by
  classical
  -- Apply the diagonal extraction over the full triple Finset.
  obtain ⟨φ, hφ_mono, hP⟩ :=
    diagonal_extraction (I := I) (M := M) g r s (S := S) (R := R) hu_bdd
      (tripleFinset (I := I) (M := M) r s)
  refine ⟨φ, hφ_mono, ?_⟩
  intro α hα Idx Jdx
  -- The triple `(⟨α, hα⟩, Idx, Jdx)` belongs to `tripleFinset`.
  have hmem : (⟨⟨α, hα⟩, Idx, Jdx⟩ : Triple (I := I) (M := M) r s) ∈
      tripleFinset (I := I) (M := M) r s :=
    Finset.mem_univ _
  rcases hP ⟨⟨α, hα⟩, Idx, Jdx⟩ hmem with ⟨u_lim, hu_lim_memLp, h_tendsto⟩
  exact ⟨u_lim, hu_lim_memLp, h_tendsto⟩

/-! ## Per-section signature wrapper

The natural per-section signature: the user passes a uniform bound
through a hypothesis dependent on each `(α, Idx, Jdx)` triple. The
content is identical to
`tensorChartComponent_rellich_extraction_of_uniform_bound` but with the
hypothesis presented in a more uniform style. -/

/-- **Per-section signature.** Given a sequence
`S : ℕ → SmoothCcTensorH1 g r s` with a uniform-in-`n` chart-Sobolev
bound on every scalar chart-frame component, extract a single
subsequence on which every scalar component converges in `L²`. -/
theorem tensorChartComponent_rellich_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) :=
  tensorChartComponent_rellich_extraction_of_uniform_bound
    (I := I) (M := M) g r s (S := S) (R := R) hu_bdd

/-! ## Restricted form: over `chartAtlasPOU_finset` only

A common application convention: only the components indexed by
`α ∈ chartAtlasPOU_finset` matter, since for any other `α` the
partition-of-unity weight is zero and the scalar component is the zero
function on `M`. We restate the headline using the natural restricted
hypothesis (the uniform bound is only required for triples in the finite
support set). -/

/-- **Restricted form.** The uniform chart-Sobolev bound is only required
on triples `(α, Idx, Jdx)` with `α ∈ chartAtlasPOU_finset`. The
conclusion is the same diagonal extraction across the finite triple
Finset. -/
theorem tensorChartComponent_rellich_extraction_restricted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) := by
  classical
  -- We replay the Finset induction inline, restricted to triples whose
  -- α-component lies in `chartAtlasPOU_finset` (already enforced by the
  -- `Triple` type's first component).
  suffices hgoal :
      ∀ T : Finset (Triple (I := I) (M := M) r s),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ t ∈ T, ∃ u_lim : M → ℝ,
            MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            Filter.Tendsto
              (fun j => eLpNorm
                  (fun b => tensorChartComponentScalar (I := I) (M := M)
                    g r s (S (φ j)).toCcTensor t.1.1 t.2.1 t.2.2 b - u_lim b)
                  2 (riemannianVolumeMeasure (I := I) (M := M) g))
              Filter.atTop (𝓝 0) by
    obtain ⟨φ, hφ_mono, hP_T⟩ := hgoal (tripleFinset (I := I) (M := M) r s)
    refine ⟨φ, hφ_mono, ?_⟩
    intro α hα Idx Jdx
    have hmem : (⟨⟨α, hα⟩, Idx, Jdx⟩ : Triple (I := I) (M := M) r s) ∈
        tripleFinset (I := I) (M := M) r s :=
      Finset.mem_univ _
    rcases hP_T ⟨⟨α, hα⟩, Idx, Jdx⟩ hmem with ⟨u_lim, hu_lim_memLp, h_tendsto⟩
    exact ⟨u_lim, hu_lim_memLp, h_tendsto⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun t ht => ?_⟩
      exact absurd ht (Finset.notMem_empty t)
  | insert t T' ht_notin ih =>
      rcases ih with ⟨φ_T', hφ_T'_mono, hP_T'⟩
      have hu_bdd_comp : ∀ n,
          wkpNormChart (I := I) (M := M) g 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ_T' n)).toCcTensor t.1.1 t.2.1 t.2.2) ≤
            ENNReal.ofReal R := fun n =>
        hu_bdd t.1.1 t.1.2 t.2.1 t.2.2 (φ_T' n)
      obtain ⟨σ_t, hσ_t_mono, u_t, hu_t_memLp, h_tendsto_t⟩ :=
        single_triple_extraction (I := I) (M := M) g r s t.1.1 t.2.1 t.2.2
          (S := fun n => S (φ_T' n))
          (R := R) hu_bdd_comp
      refine ⟨φ_T' ∘ σ_t, hφ_T'_mono.comp hσ_t_mono, ?_⟩
      intro t' ht'
      rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
      · exact ⟨u_t, hu_t_memLp, h_tendsto_t⟩
      · rcases hP_T' t' ht'_T' with ⟨u_t', hu_t'_memLp, h_tendsto_t'⟩
        refine ⟨u_t', hu_t'_memLp, ?_⟩
        exact tendsto_eLpNorm_diff_comp (I := I) (M := M) g r s t'.1.1 t'.2.1 t'.2.2
          h_tendsto_t' hσ_t_mono

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_of_uniform_bound

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_restricted

end Sanity
