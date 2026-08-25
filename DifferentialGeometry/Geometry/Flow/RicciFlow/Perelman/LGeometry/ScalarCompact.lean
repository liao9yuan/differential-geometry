import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

/-!
# Compactness of the scalar part of the regularized L-action

This file records continuity, interval integrability, and stability under
uniform convergence for the scalar-curvature term in square-root backward
time.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
/-- The scalar-curvature part of the regularized Lagrangian is continuous
along a continuous curve on a compact time interval. -/
theorem lScalar_cont
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (alpha : Real → M)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier)
    (halpha : ContinuousOn alpha (Set.uIcc a b)) :
    ContinuousOn
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      (Set.uIcc a b) := by
  have hpair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.uIcc a b) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk halpha
  have hmaps : Set.MapsTo (fun s : Real ↦ (T - s ^ 2, alpha s))
      (Set.uIcc a b) (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro s hs
    exact ⟨ht s hs, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun s : Real ↦ S.scalar (T - s ^ 2) (alpha s))
      (Set.uIcc a b) := by
    simpa only [Function.comp_def] using
      hS.scalar_continuousOn.comp hpair hmaps
  exact ((continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hscalar)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [CompactSpace M] in
/-- The scalar-curvature part of the regularized Lagrangian is interval
integrable along every continuous curve. -/
theorem lScalar_int
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (alpha : Real → M)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier)
    (halpha : ContinuousOn alpha (Set.uIcc a b)) :
    IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume a b :=
  (lScalar_cont (I := I) S hS T a b alpha ht halpha).intervalIntegrable

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
/-- The scalar-curvature part of the regularized L-action is continuous under
uniform convergence of continuous curves on a compact time interval. -/
theorem lScalar_tendsto
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.carrier)
    (alpha : Nat → Real → M) (alphaLim : Real → M)
    (halpha : ∀ n, ContinuousOn (alpha n) (Set.Icc a b))
    (hconv : TendstoUniformly
      (fun n (s : Set.Icc a b) ↦ alpha n s.1)
      (fun s : Set.Icc a b ↦ alphaLim s.1) atTop) :
    Tendsto
      (fun n ↦ ∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha n s))
      atTop
      (𝓝 (∫ s in a..b,
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alphaLim s))) := by
  let P : Real → M → Real := fun s x ↦
    2 * s ^ 2 * S.scalar (T - s ^ 2) x
  have hpair : ContinuousOn
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ (Set.univ : Set M)) :=
    (continuous_const.sub (continuous_fst.pow 2)).continuousOn.prodMk
      continuous_snd.continuousOn
  have hmaps : Set.MapsTo
      (fun q : Real × M ↦ (T - q.1 ^ 2, q.2))
      (Set.Icc a b ×ˢ (Set.univ : Set M))
      (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro q hq
    exact ⟨ht q.1 hq.1, Set.mem_univ _⟩
  have hscalar : ContinuousOn
      (fun q : Real × M ↦ S.scalar (T - q.1 ^ 2) q.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
    simpa only [Function.comp_def] using
      hS.scalar_continuousOn.comp hpair hmaps
  have hP : ContinuousOn (fun q : Real × M ↦ P q.1 q.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hK : IsCompact (Set.Icc a b ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hP
  let C₀ : Real := max C 0
  have htimeU : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    simpa only [Set.uIcc_of_le hab] using ht
  have halphaU : ∀ n, ContinuousOn (alpha n) (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using halpha
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (fun _ : Real ↦ C₀) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards with n
    exact ((lScalar_cont (I := I) S hS T a b (alpha n) htimeU
      (halphaU n)).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards with n
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      exact (hC (s, alpha n s) ⟨hsIcc, Set.mem_univ _⟩).trans
        (le_max_left C 0)
  · exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs
      have halphaAt : Tendsto (fun n ↦ alpha n s) atTop
          (𝓝 (alphaLim s)) := by
        simpa only using hconv.tendsto_at ⟨s, hsIcc⟩
      let tD : {t : Real // t ∈ D.carrier} := ⟨T - s ^ 2, ht s hsIcc⟩
      have hpairAt : Tendsto (fun n ↦ (tD, alpha n s)) atTop
          (𝓝 (tD, alphaLim s)) :=
        tendsto_const_nhds.prodMk_nhds halphaAt
      have hscalarAt : Tendsto
          (fun n ↦ S.scalar (T - s ^ 2) (alpha n s)) atTop
          (𝓝 (S.scalar (T - s ^ 2) (alphaLim s))) := by
        simpa only [tD] using
          (hS.continuous_subtype.continuousAt.tendsto.comp hpairAt)
      simpa only [P] using tendsto_const_nhds.mul hscalarAt

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
