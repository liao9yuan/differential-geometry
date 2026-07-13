import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffMeas
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nonautonomous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic

/-!
# Strong reversed conjugate heat

This file assembles the genuine moving-Laplacian and scalar-potential operator
families on one short interval and applies non-autonomous maximal regularity.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The moving-Laplacian perturbation in the literal `a + 2` domain normal
form consumed by maximal regularity at `a = 0`. -/
noncomputable def conjA2MR
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (t : Real) :
    tensorHs (I := I) (M := M) (S.family.metric (T : Real))
        0 0 ((0 : Real) + 2) →L[Real]
      tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0 :=
  (lapDiffA20 (I := I) (M := M) S.family T t).comp
    (tensorHsInclusion (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      (show (2 : Real) ≤ 0 + 2 by norm_num))

/-- The scalar-potential perturbation in the literal `a + 1` domain normal
form consumed by maximal regularity at `a = 0`. -/
noncomputable def conjA1MR
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (t : Real) :
    tensorHs (I := I) (M := M) (S.family.metric (T : Real))
        0 0 ((0 : Real) + 1) →L[Real]
      tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0 :=
  (conjA1 (I := I) (M := M) S T t).comp
    (tensorHsInclusion (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      (show (1 : Real) ≤ 0 + 1 by norm_num))

/-- The genuine reversed-conjugate-heat operators satisfy the combined
non-autonomous contraction bound on one positive short interval. -/
theorem conj_inputs
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ (tau : Real) (C2 C1 : NNReal),
      0 < tau ∧ tau ≤ 1 ∧
      AEStronglyMeasurable
        (fun s : Real => conjA2MR (I := I) (M := M) S T s)
        (timeMeasure tau) ∧
      (∀ᵐ s ∂timeMeasure tau,
        ‖conjA2MR (I := I) (M := M) S T s‖ ≤ (C2 : Real)) ∧
      AEStronglyMeasurable
        (fun s : Real => conjA1MR (I := I) (M := M) S T s)
        (timeMeasure tau) ∧
      (∀ᵐ s ∂timeMeasure tau,
        ‖conjA1MR (I := I) (M := M) S T s‖ ≤ (C1 : Real)) ∧
      (C2 : Real) * (1 + tau) +
          (C1 : Real) * (2 * Real.sqrt tau) < 1 := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (S.family.metric (T : Real))
          0 0 (0 + 2) →L[Real]
        tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (S.family.metric (T : Real))
          0 0 (0 + 1) →L[Real]
        tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let C2 : NNReal := ⟨(1 / 4 : Real), by norm_num⟩
  obtain ⟨tau2, htau2, htau2one, hcont2, _hmeas2, hbound2, _hboundAE2⟩ :=
    lapDiffA20_short (I := I) (M := M) S.family hS.smoothMetric T
      (epsilon := (C2 : Real)) (by norm_num [C2])
  obtain ⟨tau1, htau1, htau1one, C1, hcont1, _hmeas1, hbound1, _hboundAE1⟩ :=
    conjA1_short (I := I) (M := M) S hS T
  let f : Real → Real := fun t =>
    (C2 : Real) * (1 + t) + (C1 : Real) * (2 * Real.sqrt t)
  have hfcont : ContinuousAt f 0 := by
    fun_prop
  have hfzero : f 0 < 1 := by
    norm_num [f, C2]
  have hfsmall : {t : Real | f t < 1} ∈ 𝓝 0 := by
    exact hfcont.eventually_lt_const hfzero
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hfsmall
  let tau : Real := min (min tau1 tau2) (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min (lt_min htau1 htau2) (half_pos hdelta)
  have htau_tau1 : tau ≤ tau1 :=
    (min_le_left (min tau1 tau2) (delta / 2)).trans (min_le_left tau1 tau2)
  have htau_tau2 : tau ≤ tau2 :=
    (min_le_left (min tau1 tau2) (delta / 2)).trans (min_le_right tau1 tau2)
  have htauone : tau ≤ 1 := htau_tau1.trans htau1one
  have hIcc1 : Set.Icc (0 : Real) tau ⊆ Set.Icc 0 tau1 := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htau_tau1⟩
  have hIcc2 : Set.Icc (0 : Real) tau ⊆ Set.Icc 0 tau2 := by
    intro s hs
    exact ⟨hs.1, hs.2.trans htau_tau2⟩
  let inc2 := tensorHsInclusion (I := I) (M := M)
    (g := S.family.metric (T : Real)) (r := 0) (s := 0)
    (show (2 : Real) ≤ 0 + 2 by norm_num)
  let inc1 := tensorHsInclusion (I := I) (M := M)
    (g := S.family.metric (T : Real)) (r := 0) (s := 0)
    (show (1 : Real) ≤ 0 + 1 by norm_num)
  have hcont2' : ContinuousOn
      (fun s : Real => conjA2MR (I := I) (M := M) S T s)
      (Set.Icc 0 tau) := by
    have h := (hcont2.mono hIcc2).clm_comp
      (continuousOn_const : ContinuousOn (fun _ : Real => inc2) (Set.Icc 0 tau))
    simpa only [conjA2MR, inc2] using h
  have hcont1' : ContinuousOn
      (fun s : Real => conjA1MR (I := I) (M := M) S T s)
      (Set.Icc 0 tau) := by
    have h := (hcont1.mono hIcc1).clm_comp
      (continuousOn_const : ContinuousOn (fun _ : Real => inc1) (Set.Icc 0 tau))
    simpa only [conjA1MR, inc1] using h
  have hmeas1' : AEStronglyMeasurable
      (fun s : Real => conjA1MR (I := I) (M := M) S T s)
      (timeMeasure tau) := by
    unfold timeMeasure
    exact hcont1'.aestronglyMeasurable measurableSet_Icc
  have hmeas2' : AEStronglyMeasurable
      (fun s : Real => conjA2MR (I := I) (M := M) S T s)
      (timeMeasure tau) := by
    unfold timeMeasure
    exact hcont2'.aestronglyMeasurable measurableSet_Icc
  have hbound1On : ∀ s ∈ Set.Icc (0 : Real) tau,
      ‖conjA1MR (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    intro s hs
    calc
      ‖conjA1MR (I := I) (M := M) S T s‖
          ≤ ‖conjA1 (I := I) (M := M) S T s‖ * ‖inc1‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖conjA1 (I := I) (M := M) S T s‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (tensorHsInclusion_opNorm_le_one (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            (show (1 : Real) ≤ 0 + 1 by norm_num))
          (norm_nonneg (conjA1 (I := I) (M := M) S T s))
      _ = ‖conjA1 (I := I) (M := M) S T s‖ := mul_one _
      _ ≤ (C1 : Real) := hbound1 s (hIcc1 hs)
  have hbound2On : ∀ s ∈ Set.Icc (0 : Real) tau,
      ‖conjA2MR (I := I) (M := M) S T s‖ ≤ (C2 : Real) := by
    intro s hs
    calc
      ‖conjA2MR (I := I) (M := M) S T s‖
          ≤ ‖lapDiffA20 (I := I) (M := M) S.family T s‖ * ‖inc2‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖lapDiffA20 (I := I) (M := M) S.family T s‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (tensorHsInclusion_opNorm_le_one (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            (show (2 : Real) ≤ 0 + 2 by norm_num))
          (norm_nonneg (lapDiffA20 (I := I) (M := M) S.family T s))
      _ = ‖lapDiffA20 (I := I) (M := M) S.family T s‖ := mul_one _
      _ ≤ (C2 : Real) := hbound2 s (hIcc2 hs)
  have hbound1' : ∀ᵐ s ∂timeMeasure tau,
      ‖conjA1MR (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hbound1On)
  have hbound2' : ∀ᵐ s ∂timeMeasure tau,
      ‖conjA2MR (I := I) (M := M) S T s‖ ≤ (C2 : Real) := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hbound2On)
  have htaudelta : tau < delta :=
    (min_le_right (min tau1 tau2) (delta / 2)).trans_lt (half_lt_self hdelta)
  have hf_tau : f tau < 1 := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg htau.le]
    exact htaudelta
  exact ⟨tau, C2, C1, htau, htauone, hmeas2', hbound2', hmeas1',
    hbound1', hf_tau⟩

/-- A genuine short-time spectral strong solution of the time-reversed
conjugate-heat equation.  All measurability and norm-bound proofs are produced
inside the existential conclusion, so this theorem adds no consumer
assumptions. -/
theorem conj_strong_exists
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 ((0 : Real) + 2)) :
    let q := S.family.metric (T : Real)
    let A2 : Real → tensorHs (I := I) (M := M) q 0 0 (0 + 2) →L[Real]
        tensorHs (I := I) (M := M) q 0 0 0 :=
      fun t => conjA2MR (I := I) (M := M) S T t
    let A1 : Real → tensorHs (I := I) (M := M) q 0 0 (0 + 1) →L[Real]
        tensorHs (I := I) (M := M) q 0 0 0 :=
      fun t => conjA1MR (I := I) (M := M) S T t
    ∃ (tau : Real) (htau : 0 < tau) (htau1 : tau ≤ 1)
      (C2 C1 : NNReal)
      (hA2 : AEStronglyMeasurable A2 (timeMeasure tau))
      (hC2 : ∀ᵐ t ∂timeMeasure tau, ‖A2 t‖ ≤ (C2 : Real))
      (hA1 : AEStronglyMeasurable A1 (timeMeasure tau))
      (hC1 : ∀ᵐ t ∂timeMeasure tau, ‖A1 t‖ ≤ (C1 : Real))
      (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := q) (r := 0) (s := 0) 0 tau)
      (force : timeL2 (tensorHs (I := I) (M := M) q 0 0 0) tau),
      u = maxRegDuhamelMap (I := I) (M := M) 0 htau htau1 u0 force ∧
      force =
        timeOp A2 hA2 C2 hC2
            (maxRegDuhamelSolField (I := I) (M := M)
              0 htau htau1 u0 force) +
          timeOp A1 hA1 C1 hC1
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              0 htau htau1 u0 force) ∧
      timeH1.trace0 _ tau u =
        tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
          (show (0 : Real) ≤ 0 + 2 by norm_num) u0 ∧
      timeH1.timeDeriv _ tau u =
        timeScaleLaplacian (I := I) (M := M) 0
            (maxRegDuhamelSolField (I := I) (M := M)
              0 htau htau1 u0 force) +
          (timeOp A2 hA2 C2 hC2
              (maxRegDuhamelSolField (I := I) (M := M)
                0 htau htau1 u0 force) +
            timeOp A1 hA1 C1 hC1
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
                0 htau htau1 u0 force)) := by
  dsimp only
  obtain ⟨tau, C2, C1, htau, htau1, hA2, hC2, hA1, hC1, hsmall⟩ :=
    conj_inputs (I := I) (M := M) S hS T
  let A2 : Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (0 + 2) →L[Real]
        tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 0 :=
    fun t => conjA2MR (I := I) (M := M) S T t
  let A1 : Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (0 + 1) →L[Real]
        tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 0 :=
    fun t => conjA1MR (I := I) (M := M) S T t
  have hA2' : AEStronglyMeasurable A2 (timeMeasure tau) := by
    simpa only [A2] using hA2
  have hC2' : ∀ᵐ t ∂timeMeasure tau, ‖A2 t‖ ≤ (C2 : Real) := by
    simpa only [A2] using hC2
  have hA1' : AEStronglyMeasurable A1 (timeMeasure tau) := by
    simpa only [A1] using hA1
  have hC1' : ∀ᵐ t ∂timeMeasure tau, ‖A1 t‖ ≤ (C1 : Real) := by
    simpa only [A1] using hC1
  obtain ⟨u, force, hu, hforce, htrace, hderiv⟩ :=
    nonaut_strong_exists (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0) (a := 0)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        (S.family.metric (T : Real)) 0 0)
      htau htau1 u0 A2 hA2' C2 hC2' A1 hA1' C1 hC1' hsmall
  exact ⟨tau, htau, htau1, C2, C1, hA2', hC2', hA1', hC1', u,
    force, hu, hforce, htrace, hderiv⟩

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
