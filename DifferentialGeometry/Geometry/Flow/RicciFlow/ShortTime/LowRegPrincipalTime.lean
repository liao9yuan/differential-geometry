import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalTimeH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBootstrapOne

/-!
# Low-regularity Ricci--DeTurck principal time family

This file connects the same-horizon `H2` representative of the order-one
Ricci--DeTurck solution to the actual low-regularity `H4 -> H2` principal
operator family.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

/-- The canonical identification of the order-one intermediate exponent
`1 + 1` with the literal Sobolev exponent `2`. -/
def orderOneH2Iso (g : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 1) ≃ₗᵢ[ℝ]
      metricH2 (I := I) (M := M) g := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  exact LinearIsometryEquiv.refl ℝ _

/-- The order-one Ricci--DeTurck solution's same-horizon `H2` representative,
packaged as a time-`L2` field. -/
def lowRegStateL2
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    timeL2 (metricH2 (I := I) (M := M) g) T :=
  (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.compLpL
    2 (timeMeasure T)
      (duhReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT hT1 0 f hR hball)

omit [BoundarylessManifold I M] in
/-- The `H2` state field agrees almost everywhere with the direct inclusion of
the order-one top companion field. -/
theorem lowRegState_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegStateL2 (I := I) (M := M)
        g hT hT1 f hR hball =ᵐ[timeMeasure T]
      fun t => orderOneH2Iso (I := I) (M := M) g
        (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
          (maxRegDuhamelSolField (I := I) (M := M)
            (1 : ℝ) hT hT1
            (0 : metricH3 (I := I) (M := M) g) f t)) := by
  have hmap :=
    (orderOneH2Iso (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := timeMeasure T)
      (duhReprL2 (I := I) (M := M)
        g 0 2 (1 : ℝ) hT hT1 0 f hR hball)
  have hcoe := duhReprL2_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT hT1 0 f hR hball
  have hfield := duhRepr_field_ae (I := I) (M := M)
    g 0 2 (1 : ℝ) hT hT1 0 f
  filter_upwards [hmap, hcoe, hfield] with t hm hc hf
  simpa only [lowRegStateL2] using
    hm.trans (congrArg
      (orderOneH2Iso (I := I) (M := M) g) (hc.trans hf))

omit [BoundarylessManifold I M] in
/-- The packaged `H2` state retains the order-one solver's state radius almost
everywhere. -/
theorem lowRegState_ae_le
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ∀ᵐ t ∂timeMeasure T,
      ‖lowRegStateL2 (I := I) (M := M)
        g hT hT1 f hR hball t‖ ≤ R := by
  filter_upwards [
    lowRegState_ae (I := I) (M := M)
      g hT hT1 f hR hball,
    hball] with t ht hbound
  rw [ht, LinearIsometryEquiv.norm_map]
  exact hbound

/-- The actual low-regularity Ricci--DeTurck principal operator evaluated along
the order-one solution's same-horizon `H2` state field. -/
def lowRegA2Time
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    ℝ → (metricH4 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g) :=
  principalTime (I := I) (M := M) g hR
    (lowRegStateL2 (I := I) (M := M)
      g hT hT1 f hR hball)

/-- The packaged principal family is almost everywhere the genuine
low-regularity principal operator of the original top companion field. -/
theorem lowRegA2_ae
    (g : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (metricH1 (I := I) (M := M) g) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          (1 : ℝ) hT hT1
          (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R) :
    lowRegA2Time (I := I) (M := M)
        g hT hT1 f hR hball =ᵐ[timeMeasure T]
      fun t => lowRegPrincipal (I := I) (M := M) g
        (orderOneH2Iso (I := I) (M := M) g
          (tensorHsInclusion (I := I) (M := M)
            (g := g) (r := 0) (s := 2)
            (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
            (maxRegDuhamelSolField (I := I) (M := M)
              (1 : ℝ) hT hT1
              (0 : metricH3 (I := I) (M := M) g) f t))) := by
  have hstate := lowRegState_ae_le (I := I) (M := M)
    g hT hT1 f hR hball
  have hprincipal := principalTime_ae (I := I) (M := M)
    g hR
      (lowRegStateL2 (I := I) (M := M)
        g hT hT1 f hR hball) hstate
  have hfield := lowRegState_ae (I := I) (M := M)
    g hT hT1 f hR hball
  filter_upwards [hprincipal, hfield] with t hp hf
  simpa only [lowRegA2Time] using hp.trans (congrArg
    (lowRegPrincipal (I := I) (M := M) g) hf)

/-- In dimension three, one positive `H2` radius controls the actual
time-dependent principal family on every smaller state ball, with a bound
linear in the chosen radius. -/
theorem lowRegA2_data
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ (ρ : ℝ) (C : NNReal), 0 < ρ ∧
      ∀ {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
          (f : timeL2 (metricH1 (I := I) (M := M) g) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M)
              (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maxRegDuhamelSolField (I := I) (M := M)
                (1 : ℝ) hT hT1
                (0 : metricH3 (I := I) (M := M) g) f t)‖ ≤ R),
          AEStronglyMeasurable
              (lowRegA2Time (I := I) (M := M)
                g hT hT1 f hR hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖lowRegA2Time (I := I) (M := M)
                g hT hT1 f hR hball t‖ ≤ (C : ℝ) * R) ∧
            lowRegA2Time (I := I) (M := M)
                g hT hT1 f hR hball =ᵐ[timeMeasure T]
              fun t => lowRegPrincipal (I := I) (M := M) g
                (orderOneH2Iso (I := I) (M := M) g
                  (tensorHsInclusion (I := I) (M := M)
                    (g := g) (r := 0) (s := 2)
                    (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
                    (maxRegDuhamelSolField (I := I) (M := M)
                      (1 : ℝ) hT hT1
                      (0 : metricH3 (I := I) (M := M) g) f t))) := by
  obtain ⟨ρ, C, hρ, hdata⟩ :=
    principalTime_data (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, ?_⟩
  intro R hR hRρ T hT hT1 f hball
  have hstate := lowRegState_ae_le (I := I) (M := M)
    g hT hT1 f hR hball
  obtain ⟨hmeas, hbound, _⟩ := hdata hR hRρ
    (lowRegStateL2 (I := I) (M := M)
      g hT hT1 f hR hball) hstate
  exact ⟨by
      simpa only [lowRegA2Time] using hmeas,
    by
      simpa only [lowRegA2Time] using hbound,
    lowRegA2_ae (I := I) (M := M)
      g hT hT1 f hR hball⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
