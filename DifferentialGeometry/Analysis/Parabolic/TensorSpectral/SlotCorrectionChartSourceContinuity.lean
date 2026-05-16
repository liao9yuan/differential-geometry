import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.LeviCivitaParallelChartSourceContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionUniformBound
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative

/-!
# Chart-source smoothness of the chart-Levi-Civita parallel CLM for the chart basis

For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, and a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, this file delivers the
specialisation of B.1
(`chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource`) to the input
vector field `X = chartBasisVecFiber α j`.

## Headline

`chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource`
— the trivialised image of `chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)`
is `C^∞`-smooth on `(chartAt H α).source` as an `E →L[ℝ] E`-valued function.

The proof replays B.1's chain (chart-source smoothness of the chart-frame
representation of the input vector field, smoothness of chart Christoffels
on the chart target, and constant model basis blocks) for the specific
chart-basis input.

This lemma is the input atom for the chart-source continuity of the
slot-correction Christoffel atom — the value `Φ_b := chartLeviCivitaParallelCLM
g α b (chartBasisVecFiber α j)` enters the slot-correction CLM
`tensorSlotSubstCLM r b (tangentSlotCLM r k Φ_b)` substitutively.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- A finite-dimensional inner-product space is complete. We package this as
a local instance so that the `chartLeviCivitaParallelCLM` infrastructure
(which requires `[CompleteSpace E]`) is usable here. -/
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Chart-source smoothness of the chart-basis representation -/

/-- Chart-source smoothness of `b ↦ chartE_section_repr α (chartBasisVecFiber α j) b`.

This function is *constant* on the chart base set, equal to the model basis
vector `(chartModelBasis E) j`. The chart base set equals the chart source
under `[I.Boundaryless]`. -/
private lemma chartE_section_repr_chartBasisVec_eq_const_on_chart_source
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ∀ b ∈ (chartAt H α).source,
      chartE_section_repr (I := I) α (chartBasisVecFiber (I := I) α j) b =
        (chartModelBasis E) j := by
  intro b hb
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  -- `chartE_section_repr α X b = trivToE α b (X b)`.
  have h1 :
      chartE_section_repr (I := I) α (chartBasisVecFiber (I := I) α j) b =
        trivToE (I := I) α b (chartBasisVecFiber (I := I) α j b) := rfl
  rw [h1]
  -- `trivToE α b (chartBasisVecFiber α j b) = (chartModelBasis E) j` on baseSet.
  have h2 := trivializationAt_chartBasisVec_snd (I := I) α j (x := b) hb_base
  change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
      (chartBasisVecFiber (I := I) α j b) = (chartModelBasis E) j
  -- `continuousLinearMapAt R b = linearMapAt R b` (the underlying linear map).
  rw [Bundle.Trivialization.continuousLinearMapAt_apply
    (R := ℝ) (trivializationAt E (TangentSpace I) α) b]
  rw [(trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
    (R := ℝ) hb_base]
  exact h2

/-- Chart-source smoothness of the scalar `(chartModelBasis E).repr applied at
slot `j'` to the chart-frame representation of `chartBasisVecFiber α j`.

On chart source this scalar equals `δ_{j', j}` (constant). Smoothness as a
function `M → ℝ` follows by congruence with a constant. -/
private lemma chartE_section_repr_chartBasisVec_basis_component_contMDiffOn_chartSource
    (α : M) (j : Fin (Module.finrank ℝ E))
    (j' : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j')
      ((chartAt H α).source) := by
  classical
  -- On chart source, the scalar equals `(if j' = j then 1 else 0)`.
  have h_const_on :
      ∀ b ∈ (chartAt H α).source,
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j' =
          (if j' = j then (1 : ℝ) else 0) := by
    intro b hb
    have h_repr_eq :
        chartE_section_repr (I := I) α
          (chartBasisVecFiber (I := I) α j) b =
          (chartModelBasis E) j :=
      chartE_section_repr_chartBasisVec_eq_const_on_chart_source
        (I := I) (M := M) α j b hb
    rw [h_repr_eq]
    have h_repr_self :
        (chartModelBasis E).repr ((chartModelBasis E) j) =
          Finsupp.single j (1 : ℝ) :=
      Module.Basis.repr_self (chartModelBasis E) j
    rw [h_repr_self]
    by_cases hj' : j' = j
    · simp [hj']
    · simp [hj']
  -- Smoothness via congruence with the constant function.
  refine ContMDiffOn.congr (contMDiffOn_const (c :=
    (if j' = j then (1 : ℝ) else 0))) ?_
  intro b hb
  exact h_const_on b hb

/-! ## Chart-source smoothness of the chart Christoffel symbols (per-component)

This is a re-export of the chain used in B.1's
`chartChristoffel_contMDiffOn_chartSource`. We restate the per-component
version locally; this file's downstream consumers reuse this form. -/

private lemma chartChristoffel_contMDiffOn_chartSource'
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j' k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartChristoffel (I := I) g α i j' k (extChartAt I α b))
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) b :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hb_src
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target α
  have h_int_eq : interior ((extChartAt I α).target : Set E) =
      (extChartAt I α).target := h_target_open.interior_eq
  have hb_ext_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_src
  have hxφ_tgt : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_ext_src
  have hxφ_int : extChartAt I α b ∈
      interior ((extChartAt I α).target : Set E) := by
    rw [h_int_eq]; exact hxφ_tgt
  have hΓ_on : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j' k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j' k
  have hΓ_chart : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j' k)
      (extChartAt I α b) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hxφ_int)
  exact (hΓ_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

/-! ## Chart-source smoothness of the chart-basis christoffel-correction CLM -/

/-- The chart-side Christoffel-correction CLM for the chart-basis vector
field `chartBasisVecFiber α j` is chart-source smooth as a CLM-valued
function of `b`. The proof reuses the triple-finite-sum decomposition from
B.1, specialised to the case where the input vector field is a chart basis
(yielding a *constant* component scalar on chart source). -/
private lemma christoffelCorrectionCLM_chartBasisVec_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α
        (chartBasisVecFiber (I := I) α j))
      ((chartAt H α).source) := by
  classical
  unfold christoffelCorrectionCLM
  -- Triple finite-sum: each summand is chart-source smooth.
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun i _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun j' _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun k _ => ?_)
  have hrepr_smooth :=
    chartE_section_repr_chartBasisVec_basis_component_contMDiffOn_chartSource
      (I := I) (M := M) α j j'
  have hΓ_smooth :=
    chartChristoffel_contMDiffOn_chartSource' (I := I) (M := M) g α i j' k
  have hscalar : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (chartBasisVecFiber (I := I) α j) b)) j' *
        chartChristoffel (I := I) g α i j' k (extChartAt I α b))
      ((chartAt H α).source) :=
    hrepr_smooth.mul hΓ_smooth
  have hblock_const : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun (_ : M) => christoffelBlockCLM (E := E) i k)
      ((chartAt H α).source) :=
    contMDiffOn_const
  exact hscalar.smul hblock_const

/-! ## Public theorem: chart-source `ContMDiffOn` of the trivialised parallel CLM
for the chart-basis vector field -/

/-- **Chart-source smoothness of the hom-trivialised chart Levi-Civita
parallel CLM for the chart-basis vector field.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, and a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, the function

```
b ↦ (trivializationAt (E →L[ℝ] E)
      (fun b' => TangentSpace I b' →L[ℝ] TangentSpace I b') α
      ⟨b, chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)⟩).2
```

is `ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞` on `(chartAt H α).source`.

This specialises B.1
(`chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource`) to the
chart-basis input vector field, which is the form needed downstream by the
chart-frame Christoffel slot-correction. -/
theorem chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2)
      ((chartAt H α).source) := by
  classical
  -- Use the chart-source smoothness of `christoffelCorrectionCLM` plus the
  -- bridge identity from B.1's proof.
  have h_χ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α
        (chartBasisVecFiber (I := I) α j))
      ((chartAt H α).source) :=
    christoffelCorrectionCLM_chartBasisVec_contMDiffOn_chartSource
      (I := I) (M := M) g α j
  refine h_χ.congr ?_
  intro b hb
  -- The bridge identity: trivialised parallel CLM = `christoffelCorrectionCLM`
  -- on chart source. Apply pointwise.
  classical
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  ext w
  -- LHS: trivialised image at b, unfolded via `inCoordinates`.
  have hLHS_unfold :
      (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2 w =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)) w := rfl
  rw [hLHS_unfold]
  have hLHS_unfold' :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)) w =
        trivToE (I := I) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))
            (trivFromE (I := I) α b w)) := rfl
  rw [hLHS_unfold']
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b
    (chartBasisVecFiber (I := I) α j) (trivFromE (I := I) α b w)]
  rw [trivToE_trivFromE (I := I) α hb_base]
  have hY :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α j b) =
        chartE_section_repr (I := I) α
          (chartBasisVecFiber (I := I) α j) b := rfl
  rw [hY]
  exact christoffelCorrection_eq_christoffelCorrectionCLM
    (I := I) g α (chartBasisVecFiber (I := I) α j) hb_base w

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource

end Sanity
