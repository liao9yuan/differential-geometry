import DifferentialGeometry.Analysis.Integration.Measure.MetricComparison
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCBallCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCSourceTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegRangeBall

/-!
# Uniform controlled-ball reduced-volume upper bounds

This module combines ball-local metric and regularized-ray range estimates with
the reusable good/bad-source reduced-volume assembly.  All small-time constants
are chosen before the flow, terminal time, controlled ball, and actual scale.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem lSrcGauss_all (eta : ENNReal) (heta : 0 < eta) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
        (T : Real) (x : M),
        (∫⁻ Z : E in
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
            ENNReal.ofReal (lSrcGauss S T x Z)
              ∂(modelHaar (E := E))) ≤ eta := by
  classical
  letI : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))⟩⟩
  obtain ⟨R, hR, htail⟩ := gaussSPDTail_unif
    (n := Fin (Module.finrank Real E)) eta heta
  refine ⟨R, hR, ?_⟩
  intro D S T x
  let A := lSrcGram S T x
  let e := toEuclidean (E := E)
  let sE : Set E :=
    {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)}
  let sU : Set (EuclideanSpace Real (Fin (Module.finrank Real E))) :=
    {y | R < Real.sqrt (inner Real y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
        (𝕜 := Real) A y))}
  let G : E → ENNReal :=
    sE.indicator (fun Z ↦ ENNReal.ofReal (lSrcGauss S T x Z))
  have hsE : MeasurableSet sE := by
    dsimp only [sE]
    apply measurableSet_lt measurable_const
    fun_prop
  have hsU : MeasurableSet sU := by
    dsimp only [sU]
    apply measurableSet_lt measurable_const
    fun_prop
  have hmem : ∀ y, e.symm y ∈ sE ↔ y ∈ sU := by
    intro y
    simp only [sE, sU, Set.mem_setOf_eq]
    have hquad := lSrcGram_quad S T x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
    rw [← hquad]
  have hpoint : ∀ y,
      G (e.symm y) =
        sU.indicator
          (fun z ↦ ENNReal.ofReal
            (((Real.pi : Real) ^
                ((Module.finrank Real E : Real) / 2))⁻¹ *
              Real.sqrt A.det *
              Real.exp (-inner Real z
                (Matrix.toEuclideanCLM
                  (n := Fin (Module.finrank Real E))
                  (𝕜 := Real) A z)))) y := by
    intro y
    by_cases hy : y ∈ sU
    · have hEy : e.symm y ∈ sE := (hmem y).2 hy
      simp only [G, Set.indicator_of_mem hEy, Set.indicator_of_mem hy]
      rw [lSrcGauss_eq]
      have hquad := lSrcGram_quad S T x (e.symm y)
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
      rw [← hquad]
      rfl
    · have hEy : e.symm y ∉ sE := fun h ↦ hy ((hmem y).1 h)
      simp only [G, Set.indicator_of_notMem hEy,
        Set.indicator_of_notMem hy]
  calc
    (∫⁻ Z : E in sE, ENNReal.ofReal (lSrcGauss S T x Z)
        ∂(modelHaar (E := E))) =
        ∫⁻ Z : E, G Z ∂(modelHaar (E := E)) := by
      rw [← lintegral_indicator hsE]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(Measure.map (toEuclidean (E := E)) (modelHaar (E := E))) := by
      symm
      calc
        (∫⁻ y, G ((toEuclidean (E := E)).symm y)
            ∂(Measure.map (toEuclidean (E := E)) (modelHaar (E := E)))) =
            ∫⁻ Z, G ((toEuclidean (E := E)).symm
              (toEuclidean (E := E) Z)) ∂(modelHaar (E := E)) :=
          (toEuclidean (E := E)).toHomeomorph.measurableEmbedding.lintegral_map _
        _ = ∫⁻ Z, G Z ∂(modelHaar (E := E)) := by
          refine lintegral_congr fun Z ↦ ?_
          rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(volume : Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU,
          ENNReal.ofReal
            (((Real.pi : Real) ^
                ((Module.finrank Real E : Real) / 2))⁻¹ *
              Real.sqrt A.det *
              Real.exp (-inner Real y
                (Matrix.toEuclideanCLM
                  (n := Fin (Module.finrank Real E))
                  (𝕜 := Real) A y))) ∂volume := by
      rw [← lintegral_indicator hsU]
      exact lintegral_congr fun y ↦ by
        simpa only [e] using hpoint y
    _ ≤ eta := by
      simpa only [sU, Fintype.card_fin] using
        htail A (lSrcGram_pd S T x)

/-- At fixed dimension, on a short interval uniform over flows and balls, the
moving volume of the terminal closed radius-`1/32` ball is controlled by the
terminal flow-ball volume. -/
theorem ballVol_local_unif
    [T2Space (TangentBundle I M)] [ConnectedSpace M] :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
        IsSolutionOn (I := I) S →
        ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
          B.IsRmControlled →
          Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
          ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
            let K : Set M := {y | riemannianEDistOf (I := I)
              (S.base.metric (time : Real)) B.center y ≤
                ENNReal.ofReal (B.radius / 32)}
            riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric ((time : Real) - eps * B.radius ^ 2)) K ≤
              ENNReal.ofReal
                  (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
                B.volume := by
  obtain ⟨epsM, hepsM, hmetric⟩ := lMetric_ball (E := E) (I := I) (M := M)
  let n : Real := Module.finrank Real E
  let epsF : Real := Real.log (4 / 3) / (2 * (n ^ 2 + 1))
  have hdenF : 0 < 2 * (n ^ 2 + 1) := by positivity
  have hepsF : 0 < epsF :=
    div_pos (Real.log_pos (by norm_num)) hdenF
  let eps₀ : Real := min epsM epsF
  have heps₀ : 0 < eps₀ := lt_min hepsM hepsF
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hB hreg eps heps heps₀
  dsimp only
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have hcomplete :
      RiemannianMetricComplete (I := I) (S.base.metric (time : Real)) :=
    RiemannianMetricComplete.of_compact (I := I) (S.base.metric (time : Real))
  have hKcompact : IsCompact K := by
    simpa only [K] using
      RiemannianMetricComplete.closedEBall_isCompact
        (I := I) hcomplete B.center (B.radius / 32)
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hepsM' : eps ≤ epsM := heps₀.trans (min_le_left epsM epsF)
  have hepsF' : eps ≤ epsF := heps₀.trans (min_le_right epsM epsF)
  have ht : (time : Real) - eps * B.radius ^ 2 ∈
      Set.Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
    ⟨le_rfl, sub_le_self _ (mul_nonneg heps.le (sq_nonneg B.radius))⟩
  have hmetric' := hmetric hS B hB hreg hcomplete eps heps hepsM'
    ((time : Real) - eps * B.radius ^ 2) ht
  have harg : 2 * n ^ 2 * eps ≤ Real.log (4 / 3) := by
    have hcore : eps * (2 * (n ^ 2 + 1)) ≤ Real.log (4 / 3) := by
      apply (le_div_iff₀ hdenF).mp
      simpa only [epsF] using hepsF'
    nlinarith [sq_nonneg n, heps.le]
  have hexp : Real.exp (2 * n ^ 2 * eps) ≤ 4 / 3 := by
    calc
      Real.exp (2 * n ^ 2 * eps) ≤ Real.exp (Real.log (4 / 3)) :=
        Real.exp_le_exp.mpr harg
      _ = 4 / 3 := Real.exp_log (by norm_num)
  have hcomp : ∀ x ∈ K, ∀ v : TangentSpace I x,
      (S.base.metric ((time : Real) - eps * B.radius ^ 2)).inner x v v ≤
        (4 / 3 : Real) * (S.base.metric (time : Real)).inner x v v := by
    intro x hx v
    have hx' : riemannianEDistOf (I := I) (S.base.metric (time : Real))
        B.center x ≤ ENNReal.ofReal (B.radius / 32) := by
      simpa only [K] using hx
    exact (hmetric' x hx' v).2.trans
      (mul_le_mul_of_nonneg_right hexp
        (by
          by_cases hv : v = 0
          · subst v
            simp
          · exact ((S.base.metric (time : Real)).pos x v hv).le))
  have hmeasure := volume_restrict_le (I := I) (M := M)
    (S.base.metric (time : Real))
    (S.base.metric ((time : Real) - eps * B.radius ^ 2))
    (Q := (4 / 3 : Real)) (by norm_num) hKmeas hcomp
  have hKmeasure := Measure.le_iff.mp hmeasure K hKmeas
  rw [Measure.restrict_apply hKmeas, Measure.smul_apply,
    Measure.restrict_apply hKmeas, smul_eq_mul, inter_self] at hKmeasure
  have hKB : K ⊆ B.set := by
    intro x hx
    change riemannianEDistOf (I := I) (S.base.metric (time : Real))
      B.center x < ENNReal.ofReal B.radius
    have hx' : riemannianEDistOf (I := I) (S.base.metric (time : Real))
        B.center x ≤ ENNReal.ofReal (B.radius / 32) := by
      simpa only [K] using hx
    exact hx'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))
  calc
    riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric ((time : Real) - eps * B.radius ^ 2)) K ≤
      ENNReal.ofReal (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) K := hKmeasure
    _ ≤ ENNReal.ofReal (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by
      simpa only [mul_comm] using
        mul_le_mul_right (measure_mono hKB)
          (ENNReal.ofReal
            (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)))
    _ = ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) * B.volume := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Uniformly small sources contribute at most a constant reduced density times
the moving volume of the terminal closed radius-`1/32` ball. -/
theorem lRedJac_ball_unif
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    [BoundarylessManifold I M] :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              let tau := eps * B.radius ^ 2
              let c := Real.exp
                ((Module.finrank Real E : Real) ^ 2 * eps -
                  ((Module.finrank Real E : Real) / 2) * Real.log tau -
                  ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
              let K : Set M := {y | riemannianEDistOf (I := I)
                (S.base.metric (time : Real)) B.center y ≤
                  ENNReal.ofReal (B.radius / 32)}
              (∫⁻ Z : E in
                  lInjDomain S (time : Real) B.center tau ∩
                    {Z | Real.sqrt
                      ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                        1 / (128 * Real.sqrt eps)},
                  ENNReal.ofReal
                    (lRedJac S (time : Real) B.center Z tau *
                      lSrcDensity S (time : Real) B.center)
                    ∂(modelHaar (E := E))) ≤
                ENNReal.ofReal c *
                  riemannianVolumeMeasure (I := I) (M := M)
                    (S.base.metric ((time : Real) - tau)) K := by
  obtain ⟨theta, htheta, hthetaOne, hrange⟩ :=
    lRegRange_unif (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  obtain ⟨epsR, hepsR, hrange'⟩ := hrange rho hrho
  let eps₀ : Real := min epsR 1
  have heps₀ : 0 < eps₀ := lt_min hepsR zero_lt_one
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg eps heps heps₀
  dsimp only
  have hepsR' : eps ≤ epsR := heps₀.trans (min_le_left epsR 1)
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_right epsR 1)
  let tau : Real := eps * B.radius ^ 2
  let b : Real := Real.sqrt eps * B.radius
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩
    {Z | Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
      1 / (128 * Real.sqrt eps)}
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hbpos : 0 < b := mul_pos (Real.sqrt_pos.2 heps) B.radius_pos
  have hb : Real.sqrt tau = b := by
    dsimp only [tau, b]
    rw [Real.sqrt_mul heps.le, Real.sqrt_sq_eq_abs, abs_of_pos B.radius_pos]
  have hcomplete : ∀ q ∈ Set.Icc
      ((time : Real) - theta * B.radius ^ 2) (time : Real),
      RiemannianMetricComplete (I := I) (S.base.metric q) := by
    intro q hq
    exact RiemannianMetricComplete.of_compact (I := I) (S.base.metric q)
  have hnormMeas : MeasurableSet
      {Z : E | Real.sqrt
        ((S.base.metric (time : Real)).inner B.center Z Z) ≤
          1 / (128 * Real.sqrt eps)} := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hAmeas : MeasurableSet A := by
    exact (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter hnormMeas
  have hAinj : A ⊆ lInjDomain S (time : Real) B.center tau := inter_subset_left
  have hrangeZ : ∀ Z ∈ A, ∀ s ∈ Set.Icc (0 : Real) b,
      s ∈ lRegDomain S (time : Real) B.center Z ∧
        riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
            (lRegCurve S (time : Real) B.center Z s) ≤
          ENNReal.ofReal (B.radius / 32) ∧
        riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - s ^ 2)) B.center
            (lRegCurve S (time : Real) B.center Z s) <
          ENNReal.ofReal (B.radius / 16) := by
    intro Z hZA
    simpa only [b] using
      hrange' hS B hBrho hB hreg hcomplete eps heps hepsR' Z hZA.2
  have hImage : ∀ Z ∈ A,
      lExp S (time : Real) B.center Z tau ∈ K := by
    intro Z hZA
    have h := (hrangeZ Z hZA b ⟨hbpos.le, le_rfl⟩).2.1
    change riemannianEDistOf (I := I) (S.base.metric (time : Real)) B.center
      (lExp S (time : Real) B.center Z tau) ≤ ENNReal.ofReal (B.radius / 32)
    rw [lExp, hb]
    exact h
  have hden : ∀ Z ∈ A,
      redDensity S (time : Real) B.center
          (lExp S (time : Real) B.center Z tau) tau ≤ c := by
    intro Z hZA
    apply lRedDen_of_len (J := I) S (time : Real) B.center
      (lExp S (time : Real) B.center Z tau) tau
      ((Module.finrank Real E : Real) ^ 2 * eps)
    apply lRedLen_of_range (J := I) S hS time heps heps1 B hB Z hZA.1
    dsimp only
    intro s hs
    have hsMove := (hrangeZ Z hZA s hs).2.2
    change riemannianEDistOf (I := I)
      (S.base.metric ((time : Real) - s ^ 2)) B.center
        (lRegCurve S (time : Real) B.center Z s) < ENNReal.ofReal B.radius
    exact hsMove.trans ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).2 (by
      nlinarith only [B.radius_pos]))
  change (∫⁻ Z in A,
      ENNReal.ofReal
        (lRedJac S (time : Real) B.center Z tau *
          lSrcDensity S (time : Real) B.center)
        ∂(modelHaar (E := E))) ≤ _
  simpa only [c] using
    lRedJac_set_le (I := I) S hS (time : Real) B.center htau A K
      hAmeas hAinj c hImage hden

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Uniformly over compact smooth flows and terminal controlled balls below a
fixed radius ceiling, reduced volume is bounded by the terminal-ball term plus
an arbitrary prescribed positive source-Gaussian tail. -/
theorem redVolume_ball_unif
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    [BoundarylessManifold I M] :
    ∀ rho : Real, 0 < rho → ∀ eta : ENNReal, 0 < eta →
      ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D} (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              let tau := eps * B.radius ^ 2
              let c := Real.exp
                ((Module.finrank Real E : Real) ^ 2 * eps -
                  ((Module.finrank Real E : Real) / 2) * Real.log tau -
                  ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
              redVolume S (time : Real) B.center tau ≤
                ENNReal.ofReal c *
                    (ENNReal.ofReal
                        (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
                      B.volume) +
                  eta := by
  obtain ⟨theta, htheta, hthetaOne, hsmall⟩ :=
    lRedJac_ball_unif (E := E) (I := I) (M := M)
  obtain ⟨epsV, hepsV, hmove⟩ :=
    ballVol_local_unif (E := E) (I := I) (M := M)
  intro rho hrho eta heta
  obtain ⟨epsJ, hepsJ, hsmall'⟩ := hsmall rho hrho
  obtain ⟨R, hR, htail⟩ :=
    lSrcGauss_all (E := E) (I := I) (M := M) eta heta
  let d : Real := 1 / (128 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hRone)
  let eps₀ : Real := min epsJ (min epsV (min (1 / 2) (d ^ 2)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsJ (lt_min hepsV (lt_min (by norm_num) (sq_pos_of_pos hd)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg eps heps heps₀
  dsimp only
  have hepsJ' : eps ≤ epsJ :=
    heps₀.trans (min_le_left epsJ (min epsV (min (1 / 2) (d ^ 2))))
  have hepsV' : eps ≤ epsV :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      (min_le_left epsV (min (1 / 2) (d ^ 2))))
  have hepsHalf : eps ≤ (1 / 2 : Real) :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      ((min_le_right epsV (min (1 / 2) (d ^ 2))).trans
        (min_le_left (1 / 2) (d ^ 2))))
  have hepsLt : eps < 1 := by linarith
  have hepsd : eps ≤ d ^ 2 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min (1 / 2) (d ^ 2)))).trans
      ((min_le_right epsV (min (1 / 2) (d ^ 2))).trans
        (min_le_right (1 / 2) (d ^ 2))))
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsqrtd : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsd⟩
  have hcut : R ≤ 1 / (128 * Real.sqrt eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsqrteps)).2
    calc
      R * (128 * Real.sqrt eps) ≤ (R + 1) * (128 * Real.sqrt eps) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (R + 1) * (128 * d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsqrtd (by norm_num)) hRone.le
      _ = 1 := by
        dsimp only [d]
        field_simp [hRone.ne']
  let tau : Real := eps * B.radius ^ 2
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let q : E → Real := fun Z ↦
    Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z)
  let U : Set E := lInjDomain S (time : Real) B.center tau
  let A : Set E := U ∩ {Z | q Z ≤ 1 / (128 * Real.sqrt eps)}
  let C : Set E := U ∩ {Z | 1 / (128 * Real.sqrt eps) < q Z}
  let f : E → ENNReal := fun Z ↦
    ENNReal.ofReal
      (lRedJac S (time : Real) B.center Z tau *
        lSrcDensity S (time : Real) B.center)
  let K : Set M := {y | riemannianEDistOf (I := I)
    (S.base.metric (time : Real)) B.center y ≤ ENNReal.ofReal (B.radius / 32)}
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hCmeas : MeasurableSet C := by
    apply (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter
    apply measurableSet_lt measurable_const
    dsimp only [q]
    fun_prop
  have hunion : A ∪ C = U := by
    ext Z
    simp only [A, C, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (hZ | hZ) <;> exact hZ.1
    · intro hZ
      exact (le_or_gt (q Z) (1 / (128 * Real.sqrt eps))).elim
        (fun h ↦ Or.inl ⟨hZ, h⟩) (fun h ↦ Or.inr ⟨hZ, h⟩)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro Z hZA hZC
    exact (not_lt_of_ge
      (show q Z ≤ 1 / (128 * Real.sqrt eps) from hZA.2))
      (show 1 / (128 * Real.sqrt eps) < q Z from hZC.2)
  have hsmallK : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) K := by
    simpa only [A, U, q, f, tau, c, K] using
      hsmall' hS B hBrho hB hreg eps heps hepsJ'
  have hmove' :
      riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric ((time : Real) - tau)) K ≤
        ENNReal.ofReal
            (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
          B.volume := by
    simpa only [tau, K] using hmove hS B hB hreg eps heps hepsV'
  have hsmallFinal : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        (ENNReal.ofReal
            (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
          B.volume) := by
    exact hsmallK.trans (by
      simpa only [mul_comm] using
        mul_le_mul_right hmove' (ENNReal.ofReal c))
  have htail' : (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤ eta := by
    calc
      (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤
          ∫⁻ Z : E in {Z | 1 / (128 * Real.sqrt eps) < q Z},
            ENNReal.ofReal (lSrcGauss S (time : Real) B.center Z)
              ∂(modelHaar (E := E)) := by
        simpa only [C, U, q, f] using
          lRedJac_tail_le S hS (time : Real) B.center tau
            (1 / (128 * Real.sqrt eps)) htau
      _ ≤ ∫⁻ Z : E in {Z | R < q Z},
          ENNReal.ofReal (lSrcGauss S (time : Real) B.center Z)
            ∂(modelHaar (E := E)) := by
        apply MeasureTheory.lintegral_mono_set
        intro Z hZ
        exact lt_of_le_of_lt hcut hZ
      _ ≤ eta := by
        simpa only [q] using htail S (time : Real) B.center
  rw [redVolume_lint S hS (time : Real) B.center tau htau (by
    intro t ht
    apply hreg
    have htauLt : tau < B.radius ^ 2 := by
      dsimp only [tau]
      nlinarith [sq_pos_of_pos B.radius_pos, hepsLt]
    exact ⟨by linarith [ht.1], ht.2⟩)]
  change (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) ≤ _
  exact redVolume_split (E := E) hCmeas hunion hdisj hsmallFinal htail'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
