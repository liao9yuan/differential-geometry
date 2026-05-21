import DifferentialGeometry.Integral.Connection.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Integral.Measure.TensorChartPulled
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Geometry.LocalChartConsistency
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# Chart-target form of the pointwise squared op-norm bound for
`rawTensorConnLap` by the chart-pulled representation data

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, and a smooth compactly supported `(r, s)`-tensor section `T`, this
file rewrites the pointwise squared op-norm bound

```
‖rawTensorConnLap g r s T.toSection b‖^2
    ≤ K * (‖tensorRSChartE_section_repr r s α T.toSection b‖^2
           + ‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘
                (extChartAt I α).symm) (extChartAt I α b)‖^2
           + ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α
                T.toSection ∘ (extChartAt I α).symm) (extChartAt I α b)‖^2)
```

into a form parametrised by a point `y : EuclN` of the chart-target image of
the intersection of the chart-`α` partition-of-unity tsupport with the
chart-`α` Levi-Civita good set, with the LHS expressed via
`tensorTrivProjPushedNormSq` and the RHS expressed in terms of the inverse
chart applied to `toEuclidean.symm y`.

The constant `K` depends on `g`, the chart at `α`, the chart-atlas locality
hypotheses, and the ranks `r`, `s`; it is independent of `T` and `y`.

## Strategy

1. Extract `K` from the chart-pulled representation squared bound
   (`rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet`).
2. Given `y` in the `toEuclidean`-image of the `extChartAt`-image of the
   intersection `POU ∩ goodSet`, unpack a witness `b ∈ POU ∩ goodSet` with
   `y = toEuclidean (extChartAt I α b)`.
3. Rewrite the LHS via `tensorTrivProjPushedNormSq_apply_of_mem` (the point
   `y` lies inside `chartTargetEuclid α` by
   `chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid`).
4. Substitute `(extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b`
   and use the fact that `‖TensorRSSpace.toModel T‖` agrees with `‖T‖` (by
   construction of the induced norm on the fibre).
5. Conclude using the source bound at `b`, substituting the chart-target
   identifications on the RHS.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Headline -/

/-- **Chart-target form of the pointwise squared op-norm bound for
`rawTensorConnLap` by the chart-pulled representation data.**

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and ranks
`r, s : ℕ`, there is a constant `K ≥ 0` such that for every smooth compactly
supported `(r, s)`-tensor section `T` and every point `y` in the
`toEuclidean`-image of the `extChartAt I α`-image of the intersection of the
chart-`α` partition-of-unity tsupport with the chart-`α` Levi-Civita good set,

```
tensorTrivProjPushedNormSq g r s α (rawTensorConnLap g r s T.toSection) y ≤
    K * (‖tensorRSChartE_section_repr r s α T.toSection
           ((extChartAt I α).symm ((toEuclidean).symm y))‖^2
         + ‖fderiv ℝ
              (tensorRSChartE_section_repr r s α T.toSection ∘
                 (extChartAt I α).symm)
              ((toEuclidean).symm y)‖^2
         + ‖iteratedFDeriv ℝ 2
              (tensorRSChartE_section_repr r s α T.toSection ∘
                 (extChartAt I α).symm)
              ((toEuclidean).symm y)‖^2)
```

The constant `K` depends on `g`, the chart at `α`, the chart-atlas locality
hypotheses, and the ranks `r`, `s`; it is independent of `T` and `y`. -/
theorem tensorTrivProjPushedNormSq_rawTensorConnLap_le_chartTarget_data_on_pouImage
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {y : EuclN},
        y ∈ (toEuclidean : E ≃L[ℝ] EuclN) ''
              ((extChartAt I α) ''
                (tsupport (fun x : M =>
                    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
                  chartLeviCivitaGoodSet (I := I) α)) →
        tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M =>
              rawTensorConnLap (I := I) g r s
                (fun z : M => T.toSection z) b) y ≤
          K * (‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 +
              ‖fderiv ℝ
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                 ((toEuclidean (E := E)).symm y)‖ ^ 2 +
              ‖iteratedFDeriv ℝ 2
                 (tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z) ∘ (extChartAt I α).symm)
                 ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Extract the source bound.
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet
      (I := I) (M := M) h_atlas h_atlas_strong g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro T y hy
  -- Unpack `y ∈ toEuclidean '' (extChartAt α '' (POU ∩ goodSet))`.
  obtain ⟨z, hz_in, hzy⟩ := hy
  obtain ⟨b, hb_in, hbz⟩ := hz_in
  -- `hb_in : b ∈ POU ∩ goodSet`, `hbz : extChartAt I α b = z`,
  -- `hzy : toEuclidean z = y`.
  -- Rewrite the inverse chart in terms of `b`.
  have hsymm_y : (toEuclidean (E := E)).symm y = z := by
    rw [← hzy]
    exact (toEuclidean (E := E)).symm_apply_apply z
  -- `b` lies in the chart source.
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_in.2
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart_src
  have hsymm_b : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_y, ← hbz]
    exact (extChartAt I α).left_inv hb_extsrc
  -- `y` lies in `chartTargetEuclid α`: a direct construction from the
  -- witness `z = extChartAt I α b` with `b` in the chart source.
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hbz]; exact (extChartAt I α).map_source hb_extsrc
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨z, hz_target, hzy⟩
  -- Apply `tensorTrivProjPushedNormSq_apply_of_mem`.
  have h_lhs_eq :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b' : M =>
            rawTensorConnLap (I := I) g r s
              (fun z' : M => T.toSection z') b') y =
        ‖TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s
              (fun z' : M => T.toSection z')
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2 :=
    tensorTrivProjPushedNormSq_apply_of_mem
      (I := I) (M := M) g r s α
      (fun b' : M =>
        rawTensorConnLap (I := I) g r s
          (fun z' : M => T.toSection z') b') hy_target
  -- Substitute `b`.
  have h_lhs_eq_b :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b' : M =>
            rawTensorConnLap (I := I) g r s
              (fun z' : M => T.toSection z') b') y =
        ‖TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s
              (fun z' : M => T.toSection z') b)‖ ^ 2 := by
    rw [h_lhs_eq, hsymm_b]
  -- `‖toModel X‖ = ‖X‖` by the induced norm on `TensorRSSpace`.
  have h_norm_toModel :
      ‖TensorRSSpace.toModel
          (rawTensorConnLap (I := I) g r s
            (fun z' : M => T.toSection z') b)‖ =
        ‖rawTensorConnLap (I := I) g r s
            (fun z' : M => T.toSection z') b‖ := rfl
  have h_lhs_eq_b' :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b' : M =>
            rawTensorConnLap (I := I) g r s
              (fun z' : M => T.toSection z') b') y =
        ‖rawTensorConnLap (I := I) g r s
            (fun z' : M => T.toSection z') b‖ ^ 2 := by
    rw [h_lhs_eq_b, h_norm_toModel]
  -- Apply the source bound at `b`.
  have h_src := hK_bound T (b := b) hb_in
  -- Rewrite `extChartAt I α b = (toEuclidean (E := E)).symm y` on the RHS.
  have hExt_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hsymm_y, ← hbz]
  -- Replace `b` and `extChartAt I α b` in the source bound to match the target form.
  have h_rhs_match :
      ‖tensorRSChartE_section_repr (I := I) r s α
          (fun z' : M => T.toSection z') b‖ ^ 2 +
      ‖fderiv ℝ
         (tensorRSChartE_section_repr (I := I) r s α
            (fun z' : M => T.toSection z') ∘ (extChartAt I α).symm)
         (extChartAt I α b)‖ ^ 2 +
      ‖iteratedFDeriv ℝ 2
         (tensorRSChartE_section_repr (I := I) r s α
            (fun z' : M => T.toSection z') ∘ (extChartAt I α).symm)
         (extChartAt I α b)‖ ^ 2 =
      ‖tensorRSChartE_section_repr (I := I) r s α
          (fun z' : M => T.toSection z')
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 +
      ‖fderiv ℝ
         (tensorRSChartE_section_repr (I := I) r s α
            (fun z' : M => T.toSection z') ∘ (extChartAt I α).symm)
         ((toEuclidean (E := E)).symm y)‖ ^ 2 +
      ‖iteratedFDeriv ℝ 2
         (tensorRSChartE_section_repr (I := I) r s α
            (fun z' : M => T.toSection z') ∘ (extChartAt I α).symm)
         ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
    rw [hExt_b, ← hsymm_b]
  -- Combine.
  rw [h_lhs_eq_b']
  rw [h_rhs_match] at h_src
  exact h_src

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.tensorTrivProjPushedNormSq_rawTensorConnLap_le_chartTarget_data_on_pouImage
end Sanity
