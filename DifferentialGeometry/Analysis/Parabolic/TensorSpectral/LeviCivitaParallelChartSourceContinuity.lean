import DifferentialGeometry.Integral.Connection.ChartLeviCivitaParallelExtend
import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.LeviCivitaChartSmooth

/-!
# Chart-source smoothness of `chartLeviCivitaParallelCLM g α b X`

For a closed Riemannian manifold `(M, g)`, a chart-base point `α : M`, and a
smooth vector field `X : Π b : M, TangentSpace I b`, the chart Levi-Civita
parallel CLM

```
chartLeviCivitaParallelCLM g α b X
  := (trivFromE α b).comp
      (christoffelCorrection g α b (trivToE α b (X b)))
```

is a continuous linear map `TangentSpace I b →L[ℝ] TangentSpace I b`. This
file establishes that, viewed through the canonical hom-bundle
trivialization at `α` as a CLM `E →L[ℝ] E`, this assignment is `C^∞` on the
chart-`α` source.

## Decomposition

By definition,
`chartLeviCivitaParallelCLM g α b X = trivFromE α b ∘ christoffelCorrection
g α b (trivToE α b (X b))`. The hom-bundle trivialization at `α` applied at
`b` sends a CLM `Φ : TangentSpace I b →L[ℝ] TangentSpace I b` to
`trivToE α b ∘ Φ ∘ trivFromE α b : E →L[ℝ] E`. Substituting `Φ` by the
parallel CLM and using the round-trip identities
`trivToE α b ∘ trivFromE α b = id_E` (valid on the trivialisation base set,
which equals the chart source), one obtains

```
hom-trivialised image  =  christoffelCorrectionCLM g α X b   on chart source,
```

where `christoffelCorrectionCLM` is the chart-side CLM defined in
`LeviCivitaChartSmooth.lean`. Both factors of `christoffelCorrectionCLM` —
the chart-trivialised section-component `(b.repr (chartE_section_repr α X))_j`
and the Christoffel symbol `Γ^k_{ij}(extChartAt I α b)` — are smooth on the
chart source under `[I.Boundaryless]` (the chart target is open, so
`interior = target`), and the model-side basis blocks are constant. A finite
sum of smooth scalars times constant model-CLMs is smooth.

## Public theorem

* `chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource` — smoothness
  of the hom-bundle-trivialised parallel CLM as a function valued in
  `E →L[ℝ] E`, on `(chartAt H α).source`.
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

/-! ## Chart-source smoothness of `chartE_section_repr` -/

/-- On the chart-`α` source (= the trivialisation base set), the chart-
trivialised representation of a smooth vector field is `C^∞`. -/
private lemma chartE_section_repr_contMDiffOn_chartSource
    (α : M) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => chartE_section_repr (I := I) α X b)
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  -- The chart source equals the trivialization base set.
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb_src
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) b :=
    hX.contMDiffAt
  have h := (contMDiffAt_section_iff_chartE I α X (k := (⊤ : ℕ∞)) hb_base).mp hX_at
  exact h.contMDiffWithinAt

/-- Smoothness of the basis-component scalar `(b.repr (chartE_section_repr α X x))_j`
on the chart-`α` source. -/
private lemma chartE_section_repr_basis_component_contMDiffOn_chartSource
    (α : M) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α X b)) j)
      ((chartAt H α).source) := by
  classical
  have hbase :=
    chartE_section_repr_contMDiffOn_chartSource (I := I) (M := M) α (X := X) hX
  have hcoord_clm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).contMDiff
  intro b hb
  exact (hcoord_clm.contMDiffAt).comp_contMDiffWithinAt b (hbase b hb)

/-! ## Chart-source smoothness of `chartChristoffel` -/

/-- Under `[I.Boundaryless]`, the chart target is open, hence equal to its
interior. Therefore `chartChristoffel` precomposed with `extChartAt I α` is
`ContMDiffOn` on the chart-`α` source. -/
private lemma chartChristoffel_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartChristoffel (I := I) g α i j k (extChartAt I α b))
      ((chartAt H α).source) := by
  classical
  intro b hb_src
  have hφ_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) b :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) hb_src
  -- The chart target is open under `[I.Boundaryless]`, so `interior = target`.
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target α
  have h_int_eq : interior ((extChartAt I α).target : Set E) =
      (extChartAt I α).target := h_target_open.interior_eq
  -- `extChartAt I α b ∈ target` from `b ∈ chartAt.source`.
  have hb_ext_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_src
  have hxφ_tgt : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_ext_src
  have hxφ_int : extChartAt I α b ∈
      interior ((extChartAt I α).target : Set E) := by
    rw [h_int_eq]; exact hxφ_tgt
  -- Christoffel smoothness on the interior.
  have hΓ_on : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hΓ_chart : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (extChartAt I α b) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hxφ_int)
  exact (hΓ_chart.comp_contMDiffAt hφ_at).contMDiffWithinAt

/-! ## Chart-source smoothness of `christoffelCorrectionCLM` -/

/-- Smoothness of the chart-side Christoffel-correction CLM as a CLM-valued
function of `b : M` on the chart-`α` source. -/
private lemma christoffelCorrectionCLM_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α X)
      ((chartAt H α).source) := by
  classical
  unfold christoffelCorrectionCLM
  -- Triple finite-sum: each summand is smooth on chart source.
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun i _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun j _ => ?_)
  refine contMDiffOn_finset_sum (t := Finset.univ) (fun k _ => ?_)
  -- Goal: smoothness of `b ↦ scalar(b) • Cᵢₖ` where Cᵢₖ is constant.
  have hrepr_smooth :=
    chartE_section_repr_basis_component_contMDiffOn_chartSource
      (I := I) (M := M) α (X := X) hX (j := j)
  have hΓ_smooth :=
    chartChristoffel_contMDiffOn_chartSource (I := I) (M := M) g α i j k
  have hscalar : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr (chartE_section_repr (I := I) α X b)) j *
        chartChristoffel (I := I) g α i j k (extChartAt I α b))
      ((chartAt H α).source) :=
    hrepr_smooth.mul hΓ_smooth
  have hblock_const : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun (_ : M) => christoffelBlockCLM (E := E) i k)
      ((chartAt H α).source) :=
    contMDiffOn_const
  exact hscalar.smul hblock_const

/-! ## Identification: hom-trivialised image equals `christoffelCorrectionCLM` -/

/-- On the chart-`α` source, the hom-bundle trivialisation at `α` applied to
the chart Levi-Civita parallel CLM equals the chart-side Christoffel-
correction CLM (with `σ := X`). -/
private lemma chartLeviCivitaParallelCLM_trivImage_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ (chartAt H α).source) :
    (trivializationAt (E →L[ℝ] E)
        (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
        ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2 =
      christoffelCorrectionCLM (I := I) g α X b := by
  classical
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hb
  -- The `.2` of the hom-bundle trivialisation is `inCoordinates`.
  have htriv :
      (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2 =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          α b α b (chartLeviCivitaParallelCLM (I := I) g α b X) := rfl
  rw [htriv]
  -- Unfold both sides into a CLM equality on `w : E`.
  ext w
  -- LHS = `trivToE α b ((parallelCLM) (trivFromE α b w))`.
  have hLHS_unfold :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        α b α b (chartLeviCivitaParallelCLM (I := I) g α b X) w =
      trivToE (I := I) α b
        ((chartLeviCivitaParallelCLM (I := I) g α b X) (trivFromE (I := I) α b w)) :=
    rfl
  rw [hLHS_unfold]
  -- Substitute the parallel-CLM evaluation formula.
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X (trivFromE (I := I) α b w)]
  -- `trivToE α b (trivFromE α b (·)) = ·` on the base set.
  rw [trivToE_trivFromE (I := I) α hb_base]
  -- Rewrite `christoffelCorrection ... (trivFromE α b w) = christoffelCorrectionCLM g α X b w`.
  -- The `Y`-argument of `christoffelCorrection` is `trivToE α b (X b)`, which
  -- equals `chartE_section_repr α X b` by definition.
  have hY :
      trivToE (I := I) α b (X b) =
        chartE_section_repr (I := I) α X b := rfl
  rw [hY]
  exact christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α X hb_base w

/-! ## Public headline: chart-source `ContMDiffOn` of the trivialised image -/

/-- **Chart-source `C^∞` smoothness of the hom-trivialised chart Levi-Civita
parallel CLM.** For a closed Riemannian manifold `(M, g)`, a chart-base point
`α : M`, and a smooth vector field `X` (in the form of bundle-section
smoothness of `T% X`), the function

```
b ↦ (trivializationAt (E →L[ℝ] E)
      (fun b' => TangentSpace I b' →L[ℝ] TangentSpace I b') α
      ⟨b, chartLeviCivitaParallelCLM g α b X⟩).2
```

is `ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞` on `(chartAt H α).source`. -/
theorem chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b : M, TangentSpace I b)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
      ((chartAt H α).source) := by
  classical
  have h_χ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α X)
      ((chartAt H α).source) :=
    christoffelCorrectionCLM_contMDiffOn_chartSource
      (I := I) (M := M) g α (X := X) hX
  refine h_χ.congr ?_
  intro b hb
  exact (chartLeviCivitaParallelCLM_trivImage_eq_christoffelCorrectionCLM
    (I := I) (M := M) g α X hb)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaParallelCLM_trivImage_contMDiffOn_chartSource

end Sanity
