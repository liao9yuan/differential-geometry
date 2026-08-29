import DifferentialGeometry.Analysis.Integration.Measure.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCBallCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCSourceTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.CurvatureBound

/-!
# Reduced-volume upper bounds from controlled metric balls

This module assembles the small-source endpoint localization and the exact
source-Gaussian tail into the upper estimate used by smooth noncollapsing.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.Euclidean
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem exp_quarter_le {x : Real} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x ≤ 4 / 3 := by
  calc
    Real.exp x ≤ 1 / (1 - x) :=
      Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)
    _ ≤ 4 / 3 := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Along a small minimizing source ray contained in a controlled flow ball,
reduced length has a scale-uniform lower bound. -/
theorem lRedLen_scale
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [NeZero (Module.finrank Real F)]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D') (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D'.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          ∀ Z : TangentSpace J B.center,
            Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                1 / (8 * Real.sqrt eps) →
              Z ∈ lInjDomain S (time : Real) B.center (eps * B.radius ^ 2) →
                -((Module.finrank Real F : Real) ^ 2 * eps) ≤
                  redLength S (time : Real) B.center
                    (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
                    (eps * B.radius ^ 2) := by
  obtain ⟨epsR, hepsR, hrange⟩ :=
    lRegRange_scale (J := J) S hS time hrho hreg
  let eps₀ : Real := min epsR 1
  have heps₀ : 0 < eps₀ := lt_min hepsR zero_lt_one
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ hZinj
  have hepsR' : eps ≤ epsR := heps₀.trans (min_le_left epsR 1)
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_right epsR 1)
  have hrange' := hrange eps heps hepsR' B hBrho hB Z hZ
  dsimp only at hrange'
  exact lRedLen_of_range (J := J) S hS time heps heps1 B hB Z hZinj
    (fun s hs ↦ (hrange' s hs).2)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The reduced density at a small minimizing source endpoint is bounded by an
explicit scale-invariant exponential factor. -/
theorem lRedDen_scale
    {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F] [NeZero (Module.finrank Real F)]
    {G : Type uH} [TopologicalSpace G]
    {J : ModelWithCorners Real F G} [J.Boundaryless]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace G N]
    [IsManifold J ∞ N] [T2Space N] [CompactSpace N]
    {D' : RealTimeInterval}
    (S : SolutionOn (I := J) (M := N) D') (hS : IsSolutionOn (I := J) S)
    (time : RealTimeInterval.FlowTime D') {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D'.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          ∀ Z : TangentSpace J B.center,
            Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                1 / (8 * Real.sqrt eps) →
              Z ∈ lInjDomain S (time : Real) B.center (eps * B.radius ^ 2) →
                redDensity S (time : Real) B.center
                    (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
                    (eps * B.radius ^ 2) ≤
                  Real.exp
                    ((Module.finrank Real F : Real) ^ 2 * eps -
                      ((Module.finrank Real F : Real) / 2) *
                        Real.log (eps * B.radius ^ 2) -
                      ((Module.finrank Real F : Real) / 2) *
                        Real.log (4 * Real.pi)) := by
  obtain ⟨eps₀, heps₀, hlen⟩ :=
    lRedLen_scale (J := J) S hS time hrho hreg
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB Z hZ hZinj
  exact lRedDen_of_len (J := J) S (time : Real) B.center
    (lExp S (time : Real) B.center Z (eps * B.radius ^ 2))
    (eps * B.radius ^ 2) ((Module.finrank Real F : Real) ^ 2 * eps)
    (hlen eps heps heps₀ B hBrho hB Z hZ hZinj)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The small-source part of the pulled-back reduced-volume integral is bounded
by a constant reduced density times the moving volume of the controlled ball. -/
theorem lRedJac_ball_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
          let tau := eps * B.radius ^ 2
          let c := Real.exp
            ((Module.finrank Real E : Real) ^ 2 * eps -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
          (∫⁻ Z : E in
              lInjDomain S (time : Real) B.center tau ∩
                {Z | Real.sqrt
                  ((S.base.metric (time : Real)).inner B.center Z Z) ≤
                    1 / (8 * Real.sqrt eps)},
              ENNReal.ofReal
                (lRedJac S (time : Real) B.center Z tau *
                  lSrcDensity S (time : Real) B.center)
                ∂(modelHaar (E := E))) ≤
            ENNReal.ofReal c *
              riemannianVolumeMeasure (I := I) (M := M)
                (S.base.metric ((time : Real) - tau)) B.set := by
  obtain ⟨epsD, hepsD, hden⟩ :=
    lRedDen_scale (J := I) S hS time hrho hreg
  obtain ⟨epsE, hepsE, hend⟩ :=
    lExp_scale_ball (J := I) S hS time hrho hreg
  let eps₀ : Real := min epsD epsE
  have heps₀ : 0 < eps₀ := lt_min hepsD hepsE
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB
  dsimp only
  let tau : Real := eps * B.radius ^ 2
  let c : Real := Real.exp
    ((Module.finrank Real E : Real) ^ 2 * eps -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let A : Set E := lInjDomain S (time : Real) B.center tau ∩
    {Z | Real.sqrt ((S.base.metric (time : Real)).inner B.center Z Z) ≤
      1 / (8 * Real.sqrt eps)}
  have hepsD' : eps ≤ epsD := heps₀.trans (min_le_left epsD epsE)
  have hepsE' : eps ≤ epsE := heps₀.trans (min_le_right epsD epsE)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact mul_pos heps (sq_pos_of_pos B.radius_pos)
  have hnormMeas : MeasurableSet
      {Z : E | Real.sqrt
        ((S.base.metric (time : Real)).inner B.center Z Z) ≤
          1 / (8 * Real.sqrt eps)} := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hAmeas : MeasurableSet A := by
    exact (lInj_isOpen S hS (time : Real) B.center tau).measurableSet.inter hnormMeas
  change (∫⁻ Z in A,
      ENNReal.ofReal
        (lRedJac S (time : Real) B.center Z tau *
          lSrcDensity S (time : Real) B.center)
      ∂modelHaar (E := E)) ≤
    ENNReal.ofReal c *
      riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric ((time : Real) - tau)) B.set
  exact lRedJac_set_le (I := I) S hS (time : Real) B.center htau
    A B.set hAmeas inter_subset_left c
    (fun Z hZA ↦ by
      simpa only [tau] using hend eps heps hepsE' B hBrho hB Z hZA.2)
    (fun Z hZA ↦ by
      simpa only [c, tau] using
        hden eps heps hepsD' B hBrho hB Z hZA.2 hZA.1)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
/-- On a sufficiently short parabolic interval, the moving volume of the
terminal flow-metric ball is bounded by a fixed multiple of terminal volume. -/
theorem ballVol_move_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho →
          riemannianVolumeMeasure (I := I) (M := M)
              (S.base.metric ((time : Real) - eps * B.radius ^ 2)) B.set ≤
            ENNReal.ofReal
                (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
              B.volume := by
  obtain ⟨A, hA, hmetric⟩ :=
    lMetric_scale (I := I) S hS (time : Real) hrho hreg
  let eps₀ : Real := min 1 (1 / (8 * (A * rho ^ 2 + 1)))
  have hden : 0 < A * rho ^ 2 + 1 := by
    nlinarith [mul_nonneg hA (sq_nonneg rho)]
  have heps₀ : 0 < eps₀ :=
    lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hden))
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho
  have heps1 : eps ≤ 1 := heps₀.trans (min_le_left 1 _)
  have hepsM : eps ≤ 1 / (8 * (A * rho ^ 2 + 1)) :=
    heps₀.trans (min_le_right 1 _)
  let Q : Real := Real.exp (2 * A * eps * B.radius ^ 2)
  have hQpos : 0 < Q := Real.exp_pos _
  have harg0 : 0 ≤ 2 * A * eps * B.radius ^ 2 := by positivity
  have harg : 2 * A * eps * B.radius ^ 2 ≤ 1 / 4 := by
    have hrad : B.radius ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ B.radius_pos.le hrho.le).2 hBrho
    have hscale : eps * (A * rho ^ 2 + 1) ≤ 1 / 8 := by
      apply (le_div_iff₀ (by norm_num : 0 < (8 : Real))).2
      calc
        eps * (A * rho ^ 2 + 1) * 8 = eps * (8 * (A * rho ^ 2 + 1)) := by ring
        _ ≤ (1 / (8 * (A * rho ^ 2 + 1))) *
            (8 * (A * rho ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_right hepsM (by positivity)
        _ = 1 := by field_simp [hden.ne']
    have hAr : A * B.radius ^ 2 ≤ A * rho ^ 2 :=
      mul_le_mul_of_nonneg_left hrad hA
    calc
      2 * A * eps * B.radius ^ 2 = 2 * eps * (A * B.radius ^ 2) := by ring
      _ ≤ 2 * eps * (A * rho ^ 2) := by
        exact mul_le_mul_of_nonneg_left hAr (mul_nonneg (by norm_num) heps.le)
      _ ≤ 2 * (eps * (A * rho ^ 2 + 1)) := by
        have hAρ : A * rho ^ 2 ≤ A * rho ^ 2 + 1 := by linarith
        calc
          2 * eps * (A * rho ^ 2) ≤ 2 * eps * (A * rho ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hAρ (mul_nonneg (by norm_num) heps.le)
          _ = 2 * (eps * (A * rho ^ 2 + 1)) := by ring
      _ ≤ 1 / 4 := by linarith
  have hQle : Q ≤ 4 / 3 := by
    exact exp_quarter_le harg0 harg
  have ht : (time : Real) - eps * B.radius ^ 2 ∈
      Icc ((time : Real) - eps * B.radius ^ 2) (time : Real) :=
    ⟨le_rfl, sub_le_self _ (mul_nonneg heps.le (sq_nonneg B.radius))⟩
  have hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      (S.base.metric ((time : Real) - eps * B.radius ^ 2)).inner x v v ≤
        Q * (S.base.metric (time : Real)).inner x v v := by
    intro x v
    simpa only [Q] using
      (hmetric eps heps.le heps1 B.radius B.radius_pos hBrho
        ((time : Real) - eps * B.radius ^ 2) ht x v).2
  have hmeasure := volumeMeasure_le (I := I) (M := M)
    (S.base.metric (time : Real))
    (S.base.metric ((time : Real) - eps * B.radius ^ 2)) hQpos hcomp
  have hfactor : ENNReal.ofReal
      (Real.sqrt (Q ^ Module.finrank Real E)) ≤
        ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    exact pow_le_pow_left₀ hQpos.le hQle _
  calc
    riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric ((time : Real) - eps * B.radius ^ 2)) B.set ≤
      (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) •
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real))) B.set := hmeasure B.set
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by simp
    _ ≤ ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
        riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (time : Real)) B.set := by
      simpa only [mul_comm] using
        mul_le_mul_right hfactor
          (riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (time : Real)) B.set)
    _ = ENNReal.ofReal
          (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) * B.volume := by
      rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- At one terminal compact regular slab, reduced volume at sufficiently short
parabolic scale is bounded by the controlled terminal-ball volume term plus an
arbitrary prescribed positive source-Gaussian tail. -/
theorem redVolume_ball_eta [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular)
    (eta : ENNReal) (heta : 0 < eta) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
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
  obtain ⟨epsJ, hepsJ, hsmall⟩ :=
    lRedJac_ball_le (I := I) S hS time hrho hreg
  obtain ⟨epsV, hepsV, hmove⟩ :=
    ballVol_move_le (I := I) S hS time hrho hreg
  obtain ⟨R, hR, htail⟩ :=
    lSrcGauss_unif (E := E) (I := I) (M := M) (D := D)
      eta heta
  let d : Real := 1 / (8 * (R + 1))
  have hRone : 0 < R + 1 := by linarith
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hRone)
  let eps₀ : Real := min epsJ (min epsV (min 1 (d ^ 2)))
  have heps₀ : 0 < eps₀ :=
    lt_min hepsJ (lt_min hepsV (lt_min zero_lt_one (sq_pos_of_pos hd)))
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps heps₀ B hBrho hB
  dsimp only
  have hepsJ' : eps ≤ epsJ :=
    heps₀.trans (min_le_left epsJ (min epsV (min 1 (d ^ 2))))
  have hepsV' : eps ≤ epsV :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      (min_le_left epsV (min 1 (d ^ 2))))
  have heps1 : eps ≤ 1 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      ((min_le_right epsV (min 1 (d ^ 2))).trans (min_le_left 1 (d ^ 2))))
  have hepsd : eps ≤ d ^ 2 :=
    heps₀.trans ((min_le_right epsJ (min epsV (min 1 (d ^ 2)))).trans
      ((min_le_right epsV (min 1 (d ^ 2))).trans (min_le_right 1 (d ^ 2))))
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsqrtd : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsd⟩
  have hcut : R ≤ 1 / (8 * Real.sqrt eps) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsqrteps)).2
    calc
      R * (8 * Real.sqrt eps) ≤ (R + 1) * (8 * Real.sqrt eps) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (R + 1) * (8 * d) :=
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
  let A : Set E := U ∩ {Z | q Z ≤ 1 / (8 * Real.sqrt eps)}
  let C : Set E := U ∩ {Z | 1 / (8 * Real.sqrt eps) < q Z}
  let f : E → ENNReal := fun Z ↦
    ENNReal.ofReal
      (lRedJac S (time : Real) B.center Z tau *
        lSrcDensity S (time : Real) B.center)
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
      exact (le_or_gt (q Z) (1 / (8 * Real.sqrt eps))).elim
        (fun h ↦ Or.inl ⟨hZ, h⟩) (fun h ↦ Or.inr ⟨hZ, h⟩)
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro Z hZA hZC
    exact (not_lt_of_ge
      (show q Z ≤ 1 / (8 * Real.sqrt eps) from hZA.2))
      (show 1 / (8 * Real.sqrt eps) < q Z from hZC.2)
  have hsmall' : (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
      ENNReal.ofReal c *
        (ENNReal.ofReal
            (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
          B.volume) := by
    calc
      (∫⁻ Z in A, f Z ∂(modelHaar (E := E))) ≤
          ENNReal.ofReal c *
            riemannianVolumeMeasure (I := I) (M := M)
              (S.base.metric ((time : Real) - tau)) B.set := by
        simpa only [A, U, q, f, tau, c] using
          hsmall eps heps hepsJ' B hBrho hB
      _ ≤ ENNReal.ofReal c *
          (ENNReal.ofReal
              (Real.sqrt ((4 / 3 : Real) ^ Module.finrank Real E)) *
            B.volume) := by
        simpa only [mul_comm] using
          mul_le_mul_right (hmove eps heps hepsV' B hBrho) (ENNReal.ofReal c)
  have htail' : (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤ eta := by
    calc
      (∫⁻ Z in C, f Z ∂(modelHaar (E := E))) ≤
          ∫⁻ Z : E in
            {Z | 1 / (8 * Real.sqrt eps) < q Z},
            ENNReal.ofReal (lSrcGauss S (time : Real) B.center Z)
              ∂(modelHaar (E := E)) := by
        simpa only [C, U, q, f] using
          lRedJac_tail_le S hS (time : Real) B.center tau
            (1 / (8 * Real.sqrt eps)) htau
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
    have hrSq : B.radius ^ 2 ≤ rho ^ 2 :=
      (sq_le_sq₀ B.radius_pos.le hrho.le).2 hBrho
    have htauR : tau ≤ rho ^ 2 := by
      dsimp only [tau]
      calc
        eps * B.radius ^ 2 ≤ 1 * B.radius ^ 2 :=
          mul_le_mul_of_nonneg_right heps1 (sq_nonneg B.radius)
        _ ≤ rho ^ 2 := by simpa only [one_mul] using hrSq
    exact ⟨by linarith [ht.1], ht.2⟩)]
  change (∫⁻ Z in U, f Z ∂(modelHaar (E := E))) ≤ _
  exact redVolume_split (E := E) hCmeas hunion hdisj hsmall' htail'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The fixed one-quarter-tail form of `redVolume_ball_eta`. -/
theorem redVolume_ball_le [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (time : RealTimeInterval.FlowTime D) {rho : Real} (hrho : 0 < rho)
    (hreg : Icc ((time : Real) - rho ^ 2) (time : Real) ⊆ D.regular) :
    ∃ eps₀ : Real, 0 < eps₀ ∧
      ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
        ∀ B : FlowMetricBall S time, B.radius ≤ rho → B.IsRmControlled →
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
              (1 / 4 : ENNReal) := by
  exact redVolume_ball_eta (I := I) S hS time hrho hreg
    (1 / 4 : ENNReal) (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
