import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Lift
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseTime
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr

/-!
# Radial inactivity along a rough solution, and one adjacent-scale lift

Two solver-side bricks of the low-regularity Ricci--DeTurck bootstrap.

* `lowRadialH3_eq_self` / `lowRadialHs_eq_self` are the honest `eq_self`
  bridges for the two total radial maps: each is the identity exactly at a
  spectrally symmetric state whose `H2` size is inside the cutoff radius.
  A ball bound alone is **not** enough -- symmetrization is part of both maps.
* `lowRadial_eq_self_along_sol` transports those two identities along a
  time-dependent `H3` state path, which is how the frozen radial coefficients
  along the order-one solution become the genuine coefficients.
* `lowreg_lift_two` is the one-step adjacent-scale bootstrap: it feeds the
  compatible high/low coefficient families and the low affine fixed point into
  `nonautL2_lift` on the unchanged horizon, and additionally exports the two
  *pointwise almost-everywhere* inclusion identities for the forcing and for
  the Duhamel field (the engine only produces the `L2`-class equalities).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricH3 (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (by norm_num)

/-! ## The two radial `eq_self` bridges -/

/-- The total spectral `H2` radial map is the identity at a spectrally
symmetric state lying inside its cutoff ball.  Both hypotheses are needed:
`lowRadialHs` symmetrizes before retracting, so a ball bound alone does not
make it the identity. -/
theorem lowRadialHs_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {v : metricH2 (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 2) v = v)
    (hv : ‖v‖ ≤ ρ) :
    lowRadialHs (I := I) (M := M) g ρ v = v := by
  refine (lowRadialHs_eq (I := I) (M := M) g hρ v).trans ?_
  refine Eq.trans (congrArg (ballRetraction ρ) hsymm) ?_
  exact ballRetraction_eq_self_of_mem hv

/-- The total mixed-scale `H3` radial map is the identity at a spectrally
symmetric state whose `H2` inclusion lies inside the cutoff ball. -/
theorem lowRadialH3_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    {u : metricH3 (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) u = u)
    (hu : ‖incl32 (I := I) (M := M) g u‖ ≤ ρ) :
    lowRadialH3 (I := I) (M := M) g ρ u = u := by
  refine (lowRadialH3_eq (I := I) (M := M) g hρ u).trans ?_
  refine Eq.trans
    (congrArg (lowScaleCutoff (incl32 (I := I) (M := M) g) ρ) hsymm) ?_
  exact lowScaleCutoff_eq_self _
    (tensorHsInclusion_injective (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (by norm_num)) hu

/-- Along a spectrally symmetric `H3` state path whose `H2` size stays inside
the cutoff radius, both total radial maps are the identity almost everywhere.
This is the bridge that lets the frozen radial coefficients along the
order-one solution be replaced by the genuine coefficients.

The spectral symmetry `hsymm` is an honest input: it is *not* implied by the
`H2` ball bound, and symmetry preservation for the rough fixed-point solution
is a separate, still unproved statement. -/
theorem lowRadial_eq_self_along_sol
    (g : SmoothRiemannianMetric I M) {T ρ R : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    {u : ℝ → metricH3 (I := I) (M := M) g}
    (hsymm : ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) (u t) = u t)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖incl32 (I := I) (M := M) g (u t)‖ ≤ R) :
    (∀ᵐ t ∂timeMeasure T,
        lowRadialH3 (I := I) (M := M) g ρ (u t) = u t) ∧
      (∀ᵐ t ∂timeMeasure T,
        lowRadialHs (I := I) (M := M) g ρ
            (incl32 (I := I) (M := M) g (u t)) =
          incl32 (I := I) (M := M) g (u t)) := by
  constructor
  · filter_upwards [hsymm, hball] with t hs hb
    exact lowRadialH3_eq_self (I := I) (M := M) g hρ hs (hb.trans hRρ)
  · filter_upwards [hsymm, hball] with t hs hb
    refine lowRadialHs_eq_self (I := I) (M := M) g hρ.le ?_ (hb.trans hRρ)
    have hcomm := DFunLike.congr_fun
      (symmHs_incl (I := I) (M := M) g
        (τ := (2 : ℝ)) (σ := (3 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)) (u t)
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    refine hcomm.symm.trans ?_
    exact congrArg (incl32 (I := I) (M := M) g) hs

/-! ## One adjacent-scale lift of the rough solution -/

omit [BoundarylessManifold I M] in
/-- A commuting inclusion square produced at *literal* domain exponents — the
shape of `a1_pair` (`1 ≤ 2` against `2 ≤ 3`) and of `a2_pair` (`1 ≤ 2` against
`3 ≤ 4`) — transports to the *arithmetic* domain exponents demanded by
`lowreg_lift_two` (`aLo + 1 ≤ aHi + 1`, resp. `aLo + 2 ≤ aHi + 2`), after
precomposing each coefficient with the exponent transport.

The codomains `aLo`, `aHi` need no transport: instantiating the lift at
`aLo := (1 : ℝ)`, `aHi := (2 : ℝ)` already puts the two forcing scales at their
literal orders, and the outer inclusion order `aLo ≤ aHi` is literally the
`1 ≤ 2` of the pair endpoints. -/
theorem liftCompat_congr {g : SmoothRiemannianMetric I M}
    {aLo aHi pLo pHi qLo qHi : ℝ}
    (hLo : pLo = qLo) (hHi : pHi = qHi)
    (hOrd : aLo ≤ aHi) (hp : pLo ≤ pHi) (hq : qLo ≤ qHi)
    (AHi : tensorHs (I := I) (M := M) g 0 2 qHi →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aHi)
    (ALo : tensorHs (I := I) (M := M) g 0 2 qLo →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aLo)
    (hsq : (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp AHi =
        ALo.comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hq)) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp
        (AHi.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hHi)) =
      (ALo.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hLo)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hp) := by
  have hnat := tensorHsCongrL_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
    hLo hHi hp hq
  rw [ContinuousLinearMap.comp_assoc, hnat,
    ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hsq]

omit [BoundarylessManifold I M] in
/-- Same-horizon adjacent-scale bootstrap of a zero-initial non-autonomous
maximal-regularity solution, with the low Sobolev order carried by its own
name `aLo` and with the two *pointwise* almost-everywhere inclusion identities
exported alongside the `L2`-class ones produced by `nonautL2_lift`.

Every coefficient-family input (measurability, the uniform `A2` bound, the
`L2`-in-time `A1` bound, the two contraction smallness conditions) and the low
affine fixed point are hypothesis parameters: they are exactly what the
time-dependent low-base families of the Ricci--DeTurck lane must supply, and
none of them is assumed silently. -/
theorem lowreg_lift_two
    {g : SmoothRiemannianMetric I M} {T aLo aHi : ℝ}
    (hlo : aLo = aHi - 1) (hOrd : aLo ≤ aHi)
    (hOrdA1 : aLo + 1 ≤ aHi + 1) (hOrdSt : aLo + 2 ≤ aHi + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (A2Hi : ℝ → tensorHs (I := I) (M := M) g 0 2 (aHi + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aHi)
    (hA2Hi : AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → tensorHs (I := I) (M := M) g 0 2 (aHi + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aHi)
    (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    (f0Hi : timeL2 (tensorHs (I := I) (M := M) g 0 2 aHi) T)
    (hsmallHi : (C2Hi : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
    (A2Lo : ℝ → tensorHs (I := I) (M := M) g 0 2 (aLo + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aLo)
    (hA2Lo : AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → tensorHs (I := I) (M := M) g 0 2 (aLo + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 aLo)
    (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    (f0Lo : timeL2 (tensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hsmallLo : (C2Lo : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1)
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdA1))
    (hf0 : timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd f0Hi = f0Lo)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo) :
    ∃ (uHi : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) aHi T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 aHi) T),
      uHi = maxRegDuhamelMap (I := I) (M := M) aHi hT hT1 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        timeH1.trace0 _ T uHi = 0 ∧
        timeH1.timeDeriv _ T uHi =
          timeScaleLaplacian (I := I) (M := M) aHi
              (maxRegDuhamelSolField (I := I) (M := M) aHi hT hT1 0 fHi) +
            (timeOp A2Hi hA2Hi C2Hi hC2Hi
                (maxRegDuhamelSolField (I := I) (M := M) aHi hT hT1 0 fHi) +
              a1L2Term (I := I) (M := M) hT hT1
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                A1Hi hA1Hi fHi +
              f0Hi) ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi = fLo ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maxRegDuhamelSolField (I := I) (M := M) aHi hT hT1 0 fHi) =
          maxRegDuhamelSolField (I := I) (M := M) aLo hT hT1 0 fLo ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) = fLo t) ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT hT1 0 fHi t) =
            maxRegDuhamelSolField (I := I) (M := M) aLo hT hT1 0 fLo t) := by
  subst hlo
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield⟩ :=
    nonautL2_lift (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi hsmallHi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo f0Lo hsmallLo
      hA2compat hA1compat hf0 fLo hfLo
  refine ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield, ?_, ?_⟩
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd).coeFn_compLpL (p := 2) (μ := timeMeasure T) fHi
    have hcoe2 :
        fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) := by
      rw [← hforce]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maxRegDuhamelSolField (I := I) (M := M)
              aHi hT hT1 0 fHi) =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT hT1 0 fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrdSt).coeFn_compLpL (p := 2) (μ := timeMeasure T)
          (maxRegDuhamelSolField (I := I) (M := M) aHi hT hT1 0 fHi)
    have hcoe2 :
        maxRegDuhamelSolField (I := I) (M := M)
            (aHi - 1) hT hT1 0 fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT hT1 0 fHi t) := by
      rw [← hfield]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
