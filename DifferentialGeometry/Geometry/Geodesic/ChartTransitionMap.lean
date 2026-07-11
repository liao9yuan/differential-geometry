import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartGramChristoffel
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option linter.unusedSectionVars false


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartTransitionSource (α β : M) : Set E :=
  ((extChartAt I α).symm ≫ extChartAt I β).source

omit [IsManifold I ∞ M] in
lemma chartTransitionSource_def (α β : M) :
    chartTransitionSource (I := I) α β =
      ((extChartAt I α).symm ≫ extChartAt I β).source := rfl

def chartTransitionMap (α β : M) : E → E :=
  extChartAt I β ∘ (extChartAt I α).symm

omit [IsManifold I ∞ M] in
lemma chartTransitionMap_def (α β : M) :
    chartTransitionMap (I := I) α β =
      extChartAt I β ∘ (extChartAt I α).symm := rfl

omit [IsManifold I ∞ M] in
lemma chartTransitionMap_apply (α β : M) (x : E) :
    chartTransitionMap (I := I) α β x =
      extChartAt I β ((extChartAt I α).symm x) := rfl

lemma chartTransitionMap_apply_extChartAt
    (α β : M) {x : M} (hx_α : x ∈ (chartAt H α).source) :
    chartTransitionMap (I := I) α β ((extChartAt I α) x) = extChartAt I β x := by
  unfold chartTransitionMap
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx_α
  change extChartAt I β ((extChartAt I α).symm ((extChartAt I α) x)) = extChartAt I β x
  rw [(extChartAt I α).left_inv hx_src]

theorem chartTransitionMap_contDiffOn (α β : M) :
    ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) := by
  have h := (contDiffOn_ext_coord_change (I := I) (n := ∞) β α)
  exact h

omit [IsManifold I ∞ M] in

lemma extChartAt_mem_chartTransitionSource
    (α β : M) {x : M}
    (hx_α : x ∈ (chartAt H α).source) (hx_β : x ∈ (chartAt H β).source) :
    (extChartAt I α) x ∈ chartTransitionSource (I := I) α β := by
  unfold chartTransitionSource
  have hx_α_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx_α
  have hx_β_src : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hx_β
  refine ⟨?_, ?_⟩
  · exact (extChartAt I α).map_source hx_α_src
  · have h_inv : (extChartAt I α).symm ((extChartAt I α) x) = x :=
      (extChartAt I α).left_inv hx_α_src
    change (extChartAt I α).symm ((extChartAt I α) x) ∈ (extChartAt I β).source
    rw [h_inv]
    exact hx_β_src

theorem chartTransitionSource_isOpen [I.Boundaryless] (α β : M) :
    IsOpen (chartTransitionSource (I := I) α β) := by
  unfold chartTransitionSource
  have : ((extChartAt I α).symm ≫ extChartAt I β).source =
      ((chartAt H α).extend I).symm.source ∩
        ((chartAt H α).extend I).symm ⁻¹' ((chartAt H β).extend I).source := by
    rfl
  rw [this]
  have h1 : IsOpen (((chartAt H α).extend I).symm.source) := by
    change IsOpen ((chartAt H α).extend I).target
    exact (chartAt H α).isOpen_extend_target (I := I)
  have h2_cont : ContinuousOn ((chartAt H α).extend I).symm
      ((chartAt H α).extend I).symm.source := by
    change ContinuousOn ((chartAt H α).extend I).symm ((chartAt H α).extend I).target
    exact (chartAt H α).continuousOn_extend_symm (I := I)
  have h3 : IsOpen ((chartAt H β).extend I).source :=
    (chartAt H β).isOpen_extend_source (I := I)
  exact h2_cont.isOpen_inter_preimage h1 h3

def chartTransitionAt (α β : M) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (chartTransitionMap (I := I) α β) x

omit [IsManifold I ∞ M] in
lemma chartTransitionAt_def (α β : M) (x : E) :
    chartTransitionAt (I := I) α β x =
      fderiv ℝ (chartTransitionMap (I := I) α β) x := rfl

theorem chartTransitionMap_contDiffAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    ContDiffAt ℝ ∞ (chartTransitionMap (I := I) α β) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_on : ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) :=
    chartTransitionMap_contDiffOn (I := I) α β
  exact (h_on.contDiffAt (h_open.mem_nhds hx))

theorem chartTransitionMap_differentiableAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (chartTransitionMap (I := I) α β) x :=
  (chartTransitionMap_contDiffAt (I := I) α β hx).differentiableAt (by
    decide)

theorem chartTransitionAt_smooth [I.Boundaryless] (α β : M) :
    ContDiffOn ℝ ∞
      (fun x => (chartTransitionAt (I := I) α β x : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_smooth :
      ContDiffOn ℝ ∞ (chartTransitionMap (I := I) α β)
        (chartTransitionSource (I := I) α β) :=
    chartTransitionMap_contDiffOn (I := I) α β
  have h_top : (∞ + 1) ≤ ∞ := by
    simp
  refine h_smooth.fderiv_of_isOpen h_open ?_
  exact h_top

@[simp] lemma chartTransitionAt_apply_eq_fderiv (α β : M) (x : E) (v : E) :
    chartTransitionAt (I := I) α β x v =
      fderiv ℝ (chartTransitionMap (I := I) α β) x v := rfl

lemma chartTransitionMap_self_apply
    (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) :
    chartTransitionMap (I := I) α α x = x := by
  unfold chartTransitionMap
  change extChartAt I α ((extChartAt I α).symm x) = x
  exact (extChartAt I α).right_inv hx

lemma chartTransitionMap_value_on_overlap
    (α β : M) {x : M}
    (hx_α : x ∈ (chartAt H α).source) :
    chartTransitionMap (I := I) α β ((extChartAt I α) x) = extChartAt I β x :=
  chartTransitionMap_apply_extChartAt (I := I) α β hx_α

theorem chartTransitionMap_continuousOn (α β : M) :
    ContinuousOn (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β) :=
  (chartTransitionMap_contDiffOn (I := I) α β).continuousOn

theorem chartTransitionMap_continuousAt [I.Boundaryless]
    (α β : M) {x : E}
    (hx : x ∈ chartTransitionSource (I := I) α β) :
    ContinuousAt (chartTransitionMap (I := I) α β) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  exact (chartTransitionMap_continuousOn (I := I) α β).continuousAt (h_open.mem_nhds hx)

lemma chartTransitionMap_comp_self_extChartAt
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source)
    (hp_β : p ∈ (chartAt H β).source) :
    chartTransitionMap (I := I) β α
        (chartTransitionMap (I := I) α β ((extChartAt I α) p)) =
      (extChartAt I α) p := by
  have h1 : chartTransitionMap (I := I) α β ((extChartAt I α) p) =
      extChartAt I β p :=
    chartTransitionMap_apply_extChartAt (I := I) α β hp_α
  rw [h1]
  exact chartTransitionMap_apply_extChartAt (I := I) β α hp_β

lemma chartTransitionMap_comp_self_of_mem_source
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    chartTransitionMap (I := I) β α (chartTransitionMap (I := I) α β y) = y := by
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  change extChartAt I α
      ((extChartAt I β).symm (extChartAt I β ((extChartAt I α).symm y))) = y
  rw [(extChartAt I β).left_inv hy_pre']
  exact (extChartAt I α).right_inv hy_tgt

lemma chartTransitionMap_mapsTo_source [I.Boundaryless]
    (α β : M) :
    Set.MapsTo (chartTransitionMap (I := I) α β)
      (chartTransitionSource (I := I) α β)
      (chartTransitionSource (I := I) β α) := by
  intro y hy
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  refine ⟨?_, ?_⟩
  · change extChartAt I β ((extChartAt I α).symm y) ∈ (extChartAt I β).target
    exact (extChartAt I β).map_source hy_pre'
  · change (extChartAt I β).symm
        (extChartAt I β ((extChartAt I α).symm y)) ∈ (extChartAt I α).source
    rw [(extChartAt I β).left_inv hy_pre']
    exact (extChartAt I α).map_target hy_tgt

theorem chartTransitionAt_comp_chartTransitionAt [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)).comp
        (chartTransitionAt (I := I) α β y) =
      ContinuousLinearMap.id ℝ E := by
  classical
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_nhds : chartTransitionSource (I := I) α β ∈ nhds y :=
    h_open.mem_nhds hy
  have h_eq : (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β)
      =ᶠ[nhds y] id := by
    filter_upwards [h_nhds] with z hz
    simp only [Function.comp_apply, id_eq]
    exact chartTransitionMap_comp_self_of_mem_source (I := I) α β hz
  have hdiff_f : DifferentiableAt ℝ (chartTransitionMap (I := I) α β) y :=
    chartTransitionMap_differentiableAt (I := I) α β hy
  have hy' : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  have hdiff_g : DifferentiableAt ℝ (chartTransitionMap (I := I) β α)
      (chartTransitionMap (I := I) α β y) :=
    chartTransitionMap_differentiableAt (I := I) β α hy'
  have h_fderiv_comp :
      fderiv ℝ (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β) y =
        (fderiv ℝ (chartTransitionMap (I := I) β α)
            (chartTransitionMap (I := I) α β y)).comp
          (fderiv ℝ (chartTransitionMap (I := I) α β) y) :=
    fderiv_comp y hdiff_g hdiff_f
  have h_fderiv_id : fderiv ℝ (id : E → E) y = ContinuousLinearMap.id ℝ E :=
    fderiv_id
  have h_chain : fderiv ℝ
      (chartTransitionMap (I := I) β α ∘ chartTransitionMap (I := I) α β) y =
      ContinuousLinearMap.id ℝ E := by
    rw [h_eq.fderiv_eq, h_fderiv_id]
  rw [chartTransitionAt_def, chartTransitionAt_def]
  rw [← h_fderiv_comp, h_chain]

theorem chartTransitionAt_comp_chartTransitionAt' [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    (chartTransitionAt (I := I) α β y).comp
        (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)) =
      ContinuousLinearMap.id ℝ E := by
  have hy' : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  have hback : chartTransitionMap (I := I) β α (chartTransitionMap (I := I) α β y) = y :=
    chartTransitionMap_comp_self_of_mem_source (I := I) α β hy
  have h := chartTransitionAt_comp_chartTransitionAt (I := I) β α hy'
  rw [hback] at h
  exact h

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
