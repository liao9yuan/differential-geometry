import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDirectJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgAllMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegUnifBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSRepresentation

/-!
# Same-horizon bootstrap for the fixed-background low solve

This module isolates the one analytic producer still missing from the uniform
short-time-existence lane.  The class-first fixed point is already available at
Sobolev order one.  The packet below records exactly the order-two carrier and
closed-slab forcing regularity consumed by the existing, background-generic
joint-smoothness endpoint.

The conversion from such a packet to a smooth Ricci--DeTurck metric family is
proved here.  The production metricwise route is `bg_packet_of_adapt`, which
consumes the adapted solve and its all-order mass.  The older
`bg_packet_of_solve` frontier remains visible because a bare solve does not
contain the absorption data needed to construct that adapted package.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
/-- The smooth-state DeTurck remainder with an independent fixed background. -/
noncomputable def lowregNsecBg (g g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g_bg
    (symmS (I := I) (M := M) g S) hδ_lt
    (gFibreOpBound_symmS (I := I) (M := M) g S hδ)

set_option linter.unusedVariables false in
/-- The same-horizon order-two regularity packet needed to turn a fixed-
background low solution into a jointly smooth metric solution. -/
structure BgSmoothPacket (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData) (T : ℝ) where
  carrier : MaxRegSolutionSpace (I := I) (M := M)
    (g := g) (r := 0) (s := 2) (2 : ℝ) T
  modePath : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ
  radius : ℝ
  trace_zero : timeH1.trace0 _ T carrier = 0
  mode_smooth : ∀ i, ContDiff ℝ ∞ (modePath i)
  mode_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
    ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i τ *
            (iteratedDeriv j (modePath i) t) ^ 2 ≤ B i
  mode_eq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t)) i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (modePath i) t
  state_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun carrier t‖ ≤
    lowregStateRad K.top K.slope K.outer K.realize
  radius_pos : 0 < radius
  realize_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
    SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t) →
      ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ radius
  force_coeff : ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ : ℝ}
      (hδ_lt : δ < 1)
      (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g (F t)) δ)
      (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun carrier t))
      (hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
        ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) (F t)‖ ≤ radius),
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      modePath i t = tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (lowregNsecBg (I := I) (M := M) g g_bg (F t) hδ_lt (hδ t))) i

/-- A fixed-background order-one solve with all spatial spectral masses
directly supplies the same-horizon smoothness packet.  The dimension-dependent
work is isolated in the producer of `hmass`. -/
theorem bg_packet_of_mass
    (g g_bg : SmoothRiemannianMetric I M) (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (uLo : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsLowSolveBg (I := I) (M := M)
      g g_bg K hK hT hT1 uLo gforce)
    (hmass : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    Nonempty (BgSmoothPacket (I := I) (M := M) g g_bg K T) := by
  let R := lowregStateRad K.top K.slope K.outer K.realize
  have hR : 0 < R :=
    lowregStateRad_pos K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) K.threshold :=
    lowregRealRad (I := I) (M := M) g K.realize_pos.le hK.hreal
  have hforce : gforce =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g g_bg hR K.threshold_lt hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce) t) := by
    simpa only [R, hreal, lowregNfun] using hsol.force_eq
  obtain ⟨carrier, _fHi, modePath, radius, htrace, _hmap, _hpin,
      hsmooth, hjet, hmode, hradius, hrealize, hforceCoeff, hstate⟩ :=
    direct_jet_of_mass (I := I) (M := M) g g_bg hR K.threshold_lt hreal
      hK.core_cont hT hT1 gforce (by simpa only [R] using hsol.field_mem)
      hforce hmass
  refine ⟨{
    carrier := carrier
    modePath := modePath
    radius := radius
    trace_zero := htrace
    mode_smooth := hsmooth
    mode_mass := hjet
    mode_eq := hmode
    state_bound := ?_
    radius_pos := hradius
    realize_bound := hrealize
    force_coeff := ?_ }⟩
  · intro t ht
    simpa only [R] using hstate t ht
  · intro F δ hδ_lt hδ hpin _hball
    simpa only [lowregNsecBg] using hforceCoeff F hδ_lt hδ hpin

/-- A fixed-background regularity packet realizes a smooth Ricci--DeTurck
solution on exactly the packet's horizon. -/
theorem dt_of_bg_packet (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g g_bg K) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (P : BgSmoothPacket (I := I) (M := M) g g_bg K T) :
    ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  have hrepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ)
      (x : M) (v w : TangentSpace I x),
    ccTensorBilinSymm (I := I) g
        (lowregNsecBg (I := I) (M := M) g g_bg S hδ_lt hδ +
          rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w := by
    intro S δ hδ_lt hδ x v w
    simpa only [lowregNsecBg] using
      deTurck_rem_repr (I := I) (M := M) g g_bg S hδ_lt hδ x v w
  have hthreshold : K.threshold ≤ 1 :=
    hK.threshold_le_third.trans (by norm_num)
  obtain ⟨C, hC_pos, hCraw, hcap⟩ :=
    realize_h2_bound (I := I) (M := M) g K.realize_pos hthreshold hK.hreal
  have horder : (((1 : ℕ) : ℝ) + 1) = (2 : ℝ) := by norm_num
  rw [horder] at hCraw
  have hC : ∀ S : SmoothCcTensor g 0 2,
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖) := by
    exact hCraw
  have hstate : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖timeH1.toFun P.carrier t‖ ≤ 1 / (2 * C) := by
    intro t ht
    exact (P.state_bound t ht).trans
      ((stateRad_le_P4 (Ctop := K.top) (B1 := K.slope)
        (ρ := K.outer) (P := K.realize)).trans hcap)
  obtain ⟨F, δ, hδ_lt, hδ, hF0, _hpin, hflow, hJ⟩ :=
    maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
      (I := I) (M := M) g 2
      (deTurckRicciRHS (I := I) g_bg)
      (lowregNsecBg (I := I) (M := M) g g_bg) hrepr hT hT1
      P.carrier P.trace_zero P.modePath P.mode_smooth P.mode_mass P.mode_eq
      C hC_pos hC hstate P.radius_pos P.realize_bound P.force_coeff
  refine ⟨fun t : ℝ => tensorSectionRealizeMetric (I := I) g
      (F t) hδ_lt (hδ t), ⟨hT, ?_, ?_⟩, hJ⟩
  · apply smoothRiemannianMetric_ext_inner
    intro x v w
    simp only [tensorSectionRealizeMetric_inner, hF0,
      ccTensorBilinSymm_zero_apply, add_zero]
  · intro t ht x v w
    have heq : (fun s : ℝ =>
        (tensorSectionRealizeMetric (I := I) g (F s) hδ_lt (hδ s)).inner x v w) =
        fun s : ℝ => g.inner x v w +
          ccTensorBilinSymm (I := I) g (F s) x v w := by
      funext s
      rw [tensorSectionRealizeMetric_inner]
    rw [heq]
    exact (hflow t ht x v w).const_add (g.inner x v w)

/-- The order-one fixed-background solve has a canonical same-horizon `H²`
cross representative.  It realizes the supplied maximal-regularity carrier at
every time and inherits its lower-state bound on the whole closed slab. -/
theorem lowSolve_cross
    (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsLowSolveBg (I := I) (M := M) g g_bg K hK hT hT1 u gforce) :
    ∃ v : CrossScaleField (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) T,
      v.lo = u ∧
        v.hiL2 = maxRegDuhamelSolField (I := I) (M := M)
          ((1 : ℕ) : ℝ) hT hT1 0 gforce ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
              (v.repr t) = u.toFun t) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ‖v.repr t‖ ≤
          lowregStateRad K.top K.slope K.outer K.realize := by
  let v := duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)
    hT hT1 0 gforce
  have hvlo : v.lo = u := by
    change maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
      hT hT1 0 gforce = u
    exact hsol.map_eq.symm
  have hfield : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ)
            hT hT1 0 gforce t)‖ ≤
        lowregStateRad K.top K.slope K.outer K.realize := by
    filter_upwards [hsol.field_mem] with t ht
    simpa only [lowerState, lowerBall] using ht
  refine ⟨v, hvlo, rfl, ?_, ?_⟩
  · intro t ht
    rw [crossRepr_toFun (I := I) (M := M) v hT ht, hvlo]
  · exact crossRepr_ball (I := I) (M := M) v hT
      (lowregStateRad_pos K.top_nonneg K.slope_nonneg K.outer_pos
        K.realize_pos).le hfield

/-- An adapted fixed-background solve supplies the same-horizon smoothness
packet through its all-order spatial mass.  This is a metricwise consumer; it
does not choose an adapted packet or assert class-first uniformity. -/
theorem bg_packet_of_adapt (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) (K : LowRegBoundData)
    {T Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (uLo : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowSolveBg (I := I) (M := M) g g_bg K hT hT1
      uLo gforce Rcap Ctop₂ Kr2 Kr1 Kcap) :
    Nonempty (BgSmoothPacket (I := I) (M := M) g g_bg K T) := by
  have hsolve := hlo.toIsBgSolveAt
  exact bg_packet_of_mass (I := I) (M := M) g g_bg K hsolve.bounds
    hT hT1 uLo gforce hsolve.solve
      (fun σ => lowreg_loMassBg (I := I) (M := M) hDim g g_bg K
        hT hT1 uLo gforce hlo σ)

/-- **The remaining analytic frontier.**  Bootstrap the class-first order-one
fixed-background solve to the order-two closed-slab packet without shortening
its horizon. -/
theorem bg_packet_of_solve (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsLowSolveBg (I := I) (M := M) g g_bg K hK hT hT1 u gforce) :
    Nonempty (BgSmoothPacket (I := I) (M := M) g g_bg K T) := by
  sorry

/-- A class-first low solve yields a smooth fixed-background DeTurck solution
on the same horizon. -/
theorem lowreg_dt_of_solve (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hsol : IsLowSolveBg (I := I) (M := M) g g_bg K hK hT hT1 u gforce) :
    ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  obtain ⟨P⟩ := bg_packet_of_solve (I := I) (M := M) hDim g g_bg K hK
    hT hT1 u gforce hsol
  exact dt_of_bg_packet (I := I) (M := M) g g_bg K hK hT hT1 P

/-- Every three-dimensional order-three metric class has a common horizon for
smooth Ricci--DeTurck solutions against the fixed class background. -/
theorem lowreg_dt_unif (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
          IsQuasilinearMetricParabolicSolution (I := I)
            (deTurckRicciRHS (I := I) gBase) g T g_DT ∧
          JointChartGramSmooth (I := I) T g_DT := by
  obtain ⟨U, hU, hsolve⟩ :=
    lowreg_solve_unif (I := I) (M := M) hDim gBase hΛ
  let T : ℝ := min
    (lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize) 1
  have hT : 0 < T := lt_min hU one_pos
  have hTh : T ≤ lowregHorizon U.top U.base U.slope U.zeroBd U.outer U.realize :=
    min_le_left _ _
  have hT1 : T ≤ 1 := min_le_right _ _
  refine ⟨T, hT, ?_⟩
  intro g hEq hjet
  obtain ⟨K, hK, u, gforce, _hcap, hsol⟩ :=
    hsolve g hEq hjet hT hTh hT1
  exact lowreg_dt_of_solve (I := I) (M := M) hDim g gBase K hK hT hT1
    u gforce hsol

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
