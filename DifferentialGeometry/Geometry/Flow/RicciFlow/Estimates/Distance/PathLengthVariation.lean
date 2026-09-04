import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

set_option autoImplicit false

/-!
# Ricci-flow variation of a fixed path length

This module isolates the canonical time derivative of the length of a fixed
regular path.  It depends only on the Ricci-flow solution and arc-length layers,
so downstream distance estimates do not inherit cut-locus or Jacobi imports.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)]
  [IsManifold I 2 M]
  [SigmaCompactSpace M] in
/-- Along a Ricci flow, the time derivative of the length of a fixed regular
path is the integral of minus Ricci curvature divided by its speed. -/
theorem pathLength_timeDeriv_of_ricciFlow
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b t : Real}
    (hab : a ≤ b)
    (ht : t ∈ D.regular)
    (gamma : Real → M)
    (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma)
    (hvel : ∀ u ∈ Set.Icc a b,
      mfderiv 𝓘(Real, Real) I gamma u (1 : Real) ≠ 0) :
    HasDerivAt
      (fun s ↦
        Variation.arcLength (I := I) (S.base.metric s) gamma a b)
      (∫ u in a..b,
        -ricciTensor (I := I) (S.base.metric t) (gamma u)
            (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma u (1 : Real)) /
          Real.sqrt ((S.base.metric t).inner (gamma u)
            (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma u (1 : Real))))
      t := by
  classical
  let v : (u : Real) → TangentSpace I (gamma u) :=
    fun u ↦ mfderiv 𝓘(Real, Real) I gamma u (1 : Real)
  let G : Real → Real → Real :=
    fun s u ↦ (S.base.metric s).inner (gamma u) (v u) (v u)
  let Ric : Real → Real → Real :=
    fun s u ↦ ricciTensor (I := I) (S.base.metric s) (gamma u) (v u) (v u)
  let F : Real → Real → Real := fun s u ↦ Real.sqrt (G s u)
  let F' : Real → Real → Real :=
    fun s u ↦ ((-2 : Real) * Ric s u) / (2 * Real.sqrt (G s u))
  obtain ⟨alpha, beta, htIoo, hwin⟩ := D.exists_Icc_regular ht
  have habeta : alpha ≤ beta := (htIoo.1.trans htIoo.2).le
  let Kset : Set (Real × Real) := Set.Icc alpha beta ×ˢ Set.Icc a b
  have hvLift : Continuous (fun u : Real ↦
      TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
        (gamma u) (v u)) := by
    have h :=
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M)
        (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hGcontOn :
      ContinuousOn (fun p : Real × Real ↦ G p.1 p.2) Kset := by
    rw [continuousOn_iff_continuous_restrict]
    have htime : Continuous (fun q : ↥Kset ↦ ((q : Real × Real).1)) :=
      continuous_fst.comp continuous_subtype_val
    have hparam : Continuous (fun q : ↥Kset ↦ ((q : Real × Real).2)) :=
      continuous_snd.comp continuous_subtype_val
    have hbase : Continuous (fun q : ↥Kset ↦ gamma ((q : Real × Real).2)) :=
      hgamma.continuous.comp hparam
    have hvec : ∀ _i : Fin 2, Continuous (fun q : ↥Kset ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma ((q : Real × Real).2)) (v ((q : Real × Real).2))) :=
      fun _i ↦ hvLift.comp hparam
    have heval :=
      hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := ↥Kset)
        (τ := fun q ↦ ((q : Real × Real).1))
        (b := fun q ↦ gamma ((q : Real × Real).2))
        htime
        (fun q ↦ D.regular_subset (hwin q.2.1))
        hbase
        (v := fun _i q ↦ v ((q : Real × Real).2))
        hvec
    refine heval.congr (fun q ↦ ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    rfl
  have hRicAtContOn :
      ContinuousOn
        (fun p : Real × Real ↦
          S.ricciAt p.1 (gamma p.2) (vec2 (I := I) (v p.2) (v p.2)))
        Kset := by
    rw [continuousOn_iff_continuous_restrict]
    have htime : Continuous (fun q : ↥Kset ↦ ((q : Real × Real).1)) :=
      continuous_fst.comp continuous_subtype_val
    have hparam : Continuous (fun q : ↥Kset ↦ ((q : Real × Real).2)) :=
      continuous_snd.comp continuous_subtype_val
    have hbase : Continuous (fun q : ↥Kset ↦ gamma ((q : Real × Real).2)) :=
      hgamma.continuous.comp hparam
    have hvec : ∀ _i : Fin 2, Continuous (fun q : ↥Kset ↦
        TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y)
          (gamma ((q : Real × Real).2)) (v ((q : Real × Real).2))) :=
      fun _i ↦ hvLift.comp hparam
    have heval :=
      hS.ricciCont.eval_continuous
        (P := ↥Kset)
        (τ := fun q ↦ ((q : Real × Real).1))
        (b := fun q ↦ gamma ((q : Real × Real).2))
        htime
        (fun q ↦ D.regular_subset (hwin q.2.1))
        hbase
        (v := fun _i q ↦ v ((q : Real × Real).2))
        hvec
    refine heval.congr (fun q ↦ ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    change
      metricRicciAt (I := I) (S.base.metric ((q : Real × Real).1))
          (gamma ((q : Real × Real).2))
          (fun _i : Fin 2 ↦ v ((q : Real × Real).2)) =
        metricRicciAt (I := I) (S.base.metric ((q : Real × Real).1))
          (gamma ((q : Real × Real).2))
          (vec2 (I := I) (v ((q : Real × Real).2))
            (v ((q : Real × Real).2)))
    congr 1
    funext i
    fin_cases i <;> rfl
  have hRicContOn :
      ContinuousOn (fun p : Real × Real ↦ Ric p.1 p.2) Kset := by
    refine hRicAtContOn.congr (fun p _hp ↦ ?_)
    simpa only [Ric, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      (metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric p.1) (gamma p.2) (v p.2) (v p.2)).symm
  have hFcontOn :
      ContinuousOn (fun p : Real × Real ↦ F p.1 p.2) Kset :=
    Real.continuous_sqrt.comp_continuousOn hGcontOn
  have hF'contOn :
      ContinuousOn (fun p : Real × Real ↦ F' p.1 p.2) Kset := by
    apply ContinuousOn.div
      (continuousOn_const.mul hRicContOn)
      (continuousOn_const.mul
        (Real.continuous_sqrt.comp_continuousOn hGcontOn))
    intro p hp
    have hvne : v p.2 ≠ 0 := hvel p.2 hp.2
    have hpos : 0 < G p.1 p.2 :=
      (S.base.metric p.1).pos (gamma p.2) (v p.2) hvne
    exact ne_of_gt (mul_pos two_pos (Real.sqrt_pos.2 hpos))
  have hFslice : ∀ s ∈ Set.Icc alpha beta,
      ContinuousOn (F s) (Set.Icc a b) := by
    intro s hs
    have hcomp := hFcontOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu ↦ ⟨hs, hu⟩)
    simpa only [Prod.fst, Prod.snd] using hcomp
  have hF'slice : ∀ s ∈ Set.Icc alpha beta,
      ContinuousOn (F' s) (Set.Icc a b) := by
    intro s hs
    have hcomp := hF'contOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu ↦ ⟨hs, hu⟩)
    simpa only [Prod.fst, Prod.snd] using hcomp
  have hpoint : ∀ s ∈ Set.Ioo alpha beta, ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun q ↦ F q u) (F' s u) s := by
    intro s hs u hu
    have hsreg : s ∈ D.regular :=
      hwin ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hmetric := metricDerivAt
      (I := I) S hS ⟨s, hsreg⟩ (gamma u) (v u) (v u)
    have hbridge :
        S.ricciAt s (gamma u) (vec2 (I := I) (v u) (v u)) = Ric s u := by
      exact metricRicciAt_apply_eq_ricciTensor
        (I := I) (S.base.metric s) (gamma u) (v u) (v u)
    rw [hbridge] at hmetric
    have hGne : G s u ≠ 0 := ne_of_gt
      ((S.base.metric s).pos (gamma u) (v u) (hvel u hu))
    simpa only [F, F', G] using hmetric.sqrt hGne
  have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hF'contOn
  have hkey :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (a := a) (b := b)
      (F := F) (F' := F') (x₀ := t)
      (bound := fun _ ↦ C) (s := Set.Ioo alpha beta)
      (Ioo_mem_nhds htIoo.1 htIoo.2)
      (Filter.eventually_of_mem (Ioo_mem_nhds htIoo.1 htIoo.2)
        (fun s hs ↦ by
          rw [Set.uIoc_of_le hab]
          exact
            ((hFslice s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).mono
              Set.Ioc_subset_Icc_self).aestronglyMeasurable
              measurableSet_Ioc))
      (by
        have hcontFt : ContinuousOn (F t) (Set.Icc a b) :=
          hFslice t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
        exact hcontFt.intervalIntegrable_of_Icc hab)
      (by
        rw [Set.uIoc_of_le hab]
        exact
          ((hF'slice t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩).mono
            Set.Ioc_subset_Icc_self).aestronglyMeasurable
            measurableSet_Ioc)
      (by
        apply Filter.Eventually.of_forall
        intro u hu s hs
        rw [Set.uIoc_of_le hab] at hu
        exact hC (s, u)
          ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩,
            ⟨le_of_lt hu.1, hu.2⟩⟩)
      (_root_.intervalIntegrable_const)
      (by
        apply Filter.Eventually.of_forall
        intro u hu s hs
        rw [Set.uIoc_of_le hab] at hu
        exact hpoint s hs u ⟨le_of_lt hu.1, hu.2⟩)
  have hderiv :
      (∫ u in a..b, F' t u) =
        ∫ u in a..b, -Ric t u / Real.sqrt (G t u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hden : Real.sqrt (G t u) ≠ 0 := ne_of_gt
      (Real.sqrt_pos.2
        ((S.base.metric t).pos (gamma u) (v u) (hvel u hu)))
    dsimp only [F']
    field_simp
  rw [← hderiv]
  simpa only [Variation.arcLength, F, G, Ric, v] using hkey.2

end DifferentialGeometry.PDE.RicciFlow
