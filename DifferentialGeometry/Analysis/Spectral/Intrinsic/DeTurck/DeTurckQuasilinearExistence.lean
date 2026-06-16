import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit

/-!
# Quasilinear maximal-regularity existence for the DeTurck–Ricci flow (mixed-view contraction)

The Ricci–DeTurck remainder nonlinearity is genuinely **second order**: the continuous Sobolev
Nemytskii operator `deTurckSobolevNHa2 g₀ g_bg a : H^{a+2} → H^a` loses two derivatives.  The
abstract critical-loss engine `quasilinear_strong_existence`
(`Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/ForcingFixedPoint.lean`) needs `2K < 1`
for the **full** Lipschitz constant `K` of `N`, which fails here: `K` does not shrink below the
lower-order part `‖N'(0)‖ ∼ ‖Rm‖` of the DeTurck linearization.  The subcritical small-time engine
`quasilinear_strong_existence_smallTime` is hardwired to the `H^{a+1}`-view and cannot see a
genuine two-derivative nonlinearity.

This file builds the genuine quasilinear engine via a **mixed-view contraction**.  The fixed-point
map is the composed forcing map

  `Ψ(F) := nemytskii (deTurckSobolevNHa2 g₀ g_bg a) (maxRegDuhamelSolField (a:ℝ) hT hT1 0 F)`

on the forcing space `L²([0,T]; H^a)`.  Its Lipschitz modulus on the `L²(H^a)`-ball of radius `ρ`
is

  `Λ(ρ, T) = C₁ · ρ · (1 + T)² · 2 + C₂ · 2√T`,

obtained from the **refined mixed forcing estimate** `deTurckSobolevNHa2_mixed_lipschitz` (the one
honest analytic child): the second-order part of `N` is paired with the two-derivative-gain field
bound `‖field(F) − field(F')‖_{L²(H^{a+2})} ≤ (1+T)‖F−F'‖` (`maxRegDuhamelSolField_dist_le`) times
a `ρ`-coefficient, while the lower-order part of `N` is paired with the `√T`-decaying lower-view
field bound `‖field_{a+1}(F) − field_{a+1}(F')‖_{L²(H^{a+1})} ≤ 2√T‖F−F'‖`
(`maxRegDuhamelSolFieldHa1_dist_le`), the two views being identified by the structural inclusion
`timeL2Inclusion (field_{a+2} F) = field_{a+1} F`.  Choosing `ρ` small kills the second-order arm
and `T` small kills the lower-order arm, so `Λ(ρ,T) < 1`; the stay-in-ball inequality
`‖Ψ(0)‖ ≤ ρ(1 − Λ)` closes for small `T` because `Ψ(0) = N(0)`-spectral is constant in time, of
`L²([0,T])` norm `√T·M`.  The Banach fixed point of `Ψ` produces the strong maximal-regularity
solution `deTurckRicci_quasilinear_maxreg_solution`.

## Main results

* `timeL2_norm_le_of_ae_mixed_bound` — the reusable two-term `L²` Minkowski bound: an a.e.
  pointwise mixed bound `‖h t‖ ≤ A‖p t‖ + B‖q t‖` integrates to `‖h‖ ≤ A‖p‖ + B‖q‖`.
* `timeL2Inclusion_maxRegDuhamelSolField` — the structural identification of the two scale views of
  the Duhamel field: `timeL2Inclusion (field_{a+2} F) = field_{a+1} F`.
* `deTurckSobolevNHa2_mixed_lipschitz` — POSITED honest leaf: the refined mixed forcing estimate.
* `deTurckRicci_quasilinear_maxreg_solution` — the strong quasilinear maximal-regularity solution.
-/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **A two-term `L²` Minkowski bound.**  If a time-`L²` field `h` is a.e. dominated by
`A·‖p t‖ + B·‖q t‖` for nonnegative constants `A, B` and time-`L²` fields `p, q` (in possibly
different spatial spaces), then `‖h‖ ≤ A·‖p‖ + B·‖q‖`.  This is the `L²`-triangle inequality
applied to the scalar majorants `A·‖p·‖`, `B·‖q·‖`. -/
theorem timeL2_norm_le_of_ae_mixed_bound
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ := by
  -- the scalar majorant functions `A • ‖p ·‖` and `B • ‖q ·‖`
  set Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖ with hPf
  set Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖ with hQf
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) :=
    (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) :=
    (Lp.aestronglyMeasurable q).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  -- bound `eLpNorm h` by the eLpNorm of the (a.e.) majorant `A • Pf + B • Qf`
  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : (A • Pf + B • Qf) t = A * ‖p t‖ + B * ‖q t‖ := by
      simp [hPf, hQf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hge : 0 ≤ (A • Pf + B • Qf) t := by
      rw [happ]; exact add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hge, happ]
    exact ht
  -- triangle inequality + scalar pull-out at the `eLpNorm` level
  have htri : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
    eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]
  -- assemble the eLpNorm bound, then push to real norms
  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    calc eLpNorm (h : ℝ → X) 2 (timeMeasure T)
        ≤ eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
          hmono.trans htri
      _ = _ := by rw [hscaleP, hscaleQ]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hnormh : ‖h‖ = (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal := rfl
  have hnormp : ‖p‖ = (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal := rfl
  have hnormq : ‖q‖ = (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal := rfl
  have hrhs_ne : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top⟩
  rw [hnormh, hnormp, hnormq]
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB]

variable {g₀ g_bg : SmoothRiemannianMetric I M}

/-- **The two scale views of the affine Duhamel solution field coincide under inclusion.**

For a forcing `gforce ∈ L²([0,T]; H^a)`, the order-`(a+2)` Duhamel field `maxRegDuhamelSolField`
included down to the order-`(a+1)` scale equals the order-`(a+1)`-view Duhamel field
`maxRegDuhamelSolFieldHa1`.  Both fields are built from the same homogeneous-flow and
maximal-regularity mode families (the time-mode coordinates `homModeCoeff`, `solModeCoeff` do not
depend on the spatial scale), and the time-`L²` inclusion preserves every time-mode coordinate
(`timeModeCoeff_timeL2Inclusion`); the identity then follows from time-mode injectivity. -/
theorem timeL2Inclusion_maxRegDuhamelSolField {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) =
      maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)]
  -- both sides: `homModeCoeff u₀ i + solModeCoeff gforce i`
  rw [maxRegDuhamelSolField, maxRegDuhamelSolFieldHa1,
    timeModeCoeff_add (I := I) (M := M), timeModeCoeff_add (I := I) (M := M),
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le gforce i,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce i]

/-- **The continuous DeTurck–Ricci Lipschitz constant** `K`, the witness of
`deTurckSobolevNHa2_lipschitzWith`: `deTurckSobolevNHa2 g₀ g_bg a` is `LipschitzWith K`. -/
def deTurckLipConst (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a) : ℝ≥0 :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose

/-- The witnessed Lipschitz bound: `deTurckSobolevNHa2 g₀ g_bg a` is `LipschitzWith`
`deTurckLipConst …`. -/
theorem deTurckSobolevNHa2_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a) :
    LipschitzWith (deTurckLipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even)
      (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose_spec

/-- **The time-`L²` DeTurck–Ricci Nemytskii operator** `L²([0,T]; H^{a+2}) → L²([0,T]; H^a)`,
`f ↦ deTurckSobolevNHa2 g₀ g_bg a ∘ f`, the pointwise-in-time composition with the genuine
second-order DeTurck–Ricci nonlinearity.  It is `nemytskii` of the witnessed global Lipschitz bound
of `deTurckSobolevNHa2`. -/
def deTurckTimeNemytskii (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a)
    {T : ℝ} :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  nemytskii (I := I) (M := M)
    (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super ha_even)

/-- **The refined mixed forcing estimate for the DeTurck–Ricci Nemytskii operator (the one honest
analytic leaf).**

For the time-`L²` DeTurck–Ricci Nemytskii operator `N = deTurckTimeNemytskii …` there are
constants `C₁, C₂` such that for any `L²(H^{a+2})`-ball radius `R ≥ 0` and any two `H^{a+2}`-valued
time-`L²` fields `f, f'` of norm `≤ R`,

  `‖N f − N f'‖_{L²(H^a)} ≤ C₁·R·‖f − f'‖_{L²(H^{a+2})} + C₂·‖timeL2Inclusion (f − f')‖_{L²(H^{a+1})}`,

i.e. the second-order part of the nonlinearity is controlled by the ball radius times the full
`H^{a+2}`-distance, and the lower-order part by the `H^{a+1}`-distance of the difference alone.

POSITED (recursion frontier — the genuine missing analytic prerequisite).  This is the
time-integration of the pointwise mixed Nemytskii bound

  `‖N v − N v'‖_{H^a} ≤ C₁·R·‖v − v'‖_{H^{a+2}} + C₂·‖ι (v − v')‖_{H^{a+1}}`   (`‖v‖,‖v'‖ ≤ R`),

the refined Moser / Gagliardo–Nirenberg split of the chart-polynomial remainder difference
`chartDeTurckRicciRHS_sub_eq` by the **order of the difference factor**: each monomial carries a
single `(T − T')` jet of chart order `≤ 2`; the genuinely-second-order jets are paired with a
bounded (ball-radius `R`) plain factor and majorised in `H^{a+2}`, while the order-`≤ 1` jets need
only the `H^{a+1}` norm of the difference.  Neither the pointwise split nor its time-integration is
yet an unconditional public declaration (`deTurckSmoothN_ballLipschitz_Ha2` carries only the
single-order `H^{a+2}` bound), so the mixed estimate is the single named honest leaf on which the
mixed-view contraction below rests. -/
theorem deTurckSobolevNHa2_mixed_lipschitz (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ {T : ℝ}, 0 < T → ∀ (R : ℝ), 0 ≤ R →
      ∀ (f f' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T),
        ‖f‖ ≤ R → ‖f'‖ ≤ R →
        ‖deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f -
            deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even f'‖ ≤
          (C₁ : ℝ) * R * ‖f - f'‖ +
            (C₂ : ℝ) *
              ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖ :=
  sorry

/-- **The mixed-view forcing fixed-point map of the DeTurck–Ricci quasilinear equation.**

  `Ψ(F) := deTurckTimeNemytskii … (maxRegDuhamelSolField (a:ℝ) hT hT1 0 F)`,

a self-map of the forcing space `L²([0,T]; H^a)`: form the order-`(a+2)` Duhamel solution field of
the forcing `F` (with zero initial datum), then apply the genuine second-order DeTurck–Ricci
time-`L²` Nemytskii operator.  A fixed point `F⋆ = Ψ(F⋆)` is a forcing reproducing the nonlinearity
along its own Duhamel solution; the strong solution is the Duhamel image of `F⋆`. -/
def deTurckMixedForcingMap (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  fun F => deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F)

@[simp] theorem deTurckMixedForcingMap_apply (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1 F =
      deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F) :=
  rfl

/-- The order-`(a+2)` Duhamel field of `F` (zero initial datum) has `L²(H^{a+2})` norm bounded by
`(1 + T)·‖F‖`: the homogeneous part vanishes (`u₀ = 0`) and the maximal-regularity field gains two
derivatives with norm `≤ (1 + T)·‖F‖`. -/
theorem norm_maxRegDuhamelSolField_zero_le {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) :
    ‖maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2)) F‖ ≤ (1 + T) * ‖F‖ := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  rw [maxRegDuhamelSolField]
  refine le_trans (norm_add_le _ _) ?_
  have hhom : ‖maxRegHomogeneousSolField (I := I) (M := M) a T
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))‖ ≤ Real.sqrt T * ‖(0 : tensorHs
        (I := I) (M := M) g₀ 0 2 (a + 2))‖ :=
    maxRegHomogeneousSolField_norm_le (I := I) (M := M) (h_compact := h_compact) _ hT.le
  rw [norm_zero, mul_zero] at hhom
  have hreg : ‖maximalRegularitySolField (I := I) (M := M) a hT.le F‖ ≤ (1 + T) * ‖F‖ :=
    maximalRegularitySolField_norm_le (I := I) (M := M) (h_compact := h_compact) hT.le F
  have hhom0 : ‖maxRegHomogeneousSolField (I := I) (M := M) a T
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))‖ = 0 :=
    le_antisymm hhom (norm_nonneg _)
  rw [hhom0, zero_add]
  exact hreg

/-- **The mixed-view Lipschitz estimate for the forcing map on the `L²(H^a)`-ball of radius `ρ`.**

For `‖F‖, ‖F'‖ ≤ ρ` (`ρ ≥ 0`),

  `‖Ψ(F) − Ψ(F')‖ ≤ (C₁·(1 + T)·ρ·(1 + T) + C₂·2√T)·‖F − F'‖`,

with `C₁, C₂` the constants of the refined mixed forcing estimate.  The second-order arm pairs the
ball bound `‖field(F)‖ ≤ (1+T)ρ` with the two-derivative-gain field distance
`‖field(F) − field(F')‖_{L²(H^{a+2})} ≤ (1+T)‖F−F'‖`; the lower-order arm pairs `C₂` with the
`√T`-decaying lower-view field distance `‖field_{a+1}(F) − field_{a+1}(F')‖ ≤ 2√T‖F−F'‖`, the two
field views identified by `timeL2Inclusion_maxRegDuhamelSolField`. -/
theorem deTurckMixedForcingMap_dist_le (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ ρ) (hF' : ‖F'‖ ≤ ρ) :
    ‖deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1 F -
        deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1 F'‖ ≤
      ((deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
            a ha_super ha_even).choose * (1 + T) * ρ * (1 + T) +
          (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
            a ha_super ha_even).choose_spec.choose * (2 * Real.sqrt T)) * ‖F - F'‖ := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set z : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := 0 with hz
  set fF := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 z F with hfF
  set fF' := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 z F' with hfF'
  set C₁ := (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
    a ha_super ha_even).choose with hC₁
  set C₂ := (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
    a ha_super ha_even).choose_spec.choose with hC₂
  have hmix := (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
    a ha_super ha_even).choose_spec.choose_spec hT
  -- ball bound on the fields
  set R := (1 + T) * ρ with hR
  have hT_pos : (0 : ℝ) < 1 + T := by linarith
  have hRnn : 0 ≤ R := mul_nonneg (by linarith) hρ
  have hfFball : ‖fF‖ ≤ R := by
    refine le_trans (norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) hT hT1 F) ?_
    rw [hR]; exact mul_le_mul_of_nonneg_left hF (by linarith)
  have hfF'ball : ‖fF'‖ ≤ R := by
    refine le_trans (norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) hT hT1 F') ?_
    rw [hR]; exact mul_le_mul_of_nonneg_left hF' (by linarith)
  -- field distance bounds
  have hfield_dist : ‖fF - fF'‖ ≤ (1 + T) * ‖F - F'‖ :=
    maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact) (a := (a : ℝ))
      hT hT1 z F F'
  have hincl_dist :
      ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ ≤
        2 * Real.sqrt T * ‖F - F'‖ := by
    rw [map_sub, timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1 z F,
      timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1 z F']
    exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1 z F F'
  -- the mixed estimate on the two fields
  have hmain := hmix R hRnn fF fF' hfFball hfF'ball
  calc ‖deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1 F -
          deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1 F'‖
      = ‖deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even fF -
          deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even fF'‖ := by
        rw [deTurckMixedForcingMap_apply, deTurckMixedForcingMap_apply]
    _ ≤ (C₁ : ℝ) * R * ‖fF - fF'‖ +
          (C₂ : ℝ) * ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ := hmain
    _ ≤ (C₁ : ℝ) * R * ((1 + T) * ‖F - F'‖) +
          (C₂ : ℝ) * (2 * Real.sqrt T * ‖F - F'‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hfield_dist (mul_nonneg C₁.coe_nonneg hRnn)
        · exact mul_le_mul_of_nonneg_left hincl_dist C₂.coe_nonneg
    _ = ((C₁ : ℝ) * (1 + T) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
        rw [hR]; ring

/-- The order-`(a+2)` Duhamel field of the **zero** forcing (zero initial datum) is `0`. -/
theorem maxRegDuhamelSolField_zero_zero {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))
        (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) = 0 := by
  have h := norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g₀)
    hT hT1 (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T)
  rw [norm_zero, mul_zero] at h
  exact norm_le_zero_iff.mp h

/-- The forcing map sends the zero forcing to the constant-in-time spectral nonlinearity
`deTurckSobolevNHa2 g₀ g_bg a 0`, with `L²([0,T];H^a)` norm at most `√T·‖N 0‖`. -/
theorem norm_deTurckMixedForcingMap_zero_le (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1
        (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤
      Real.sqrt T * ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
  rw [deTurckMixedForcingMap_apply,
    maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1]
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskii_coeFn (I := I) (M := M)
    (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super ha_even)
    (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
  have hzero := Lp.coeFn_zero (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzero] with t ht htz
  rw [deTurckTimeNemytskii, ht, htz, Pi.zero_apply]

/-- **The strong quasilinear maximal-regularity solution of the DeTurck–Ricci flow.**

For a closed Riemannian manifold `(M, g₀)`, DeTurck background `g_bg`, and a **supercritical**
spectral Sobolev exponent `a : ℕ` (`ha_super : 2·finrank E + 3 ≤ a`, the Sobolev algebra
threshold), there is a positive horizon `T₀` such that for every short interval `(0, T]` with
`T ≤ T₀ ≤ 1` there is a strong maximal-regularity solution `u ∈ H¹([0,T]; Hᵃ)` together with its
forcing `gforce ∈ L²([0,T]; Hᵃ)` of the **genuinely second-order** Ricci–DeTurck quasilinear tensor
heat equation

  `∂_t u = Δ_∇ (field_{a+2} u) + N(field_{a+2} u)`,   `u(0) = 0`,
  `N = deTurckSobolevNHa2 g₀ g_bg a : H^{a+2} → Hᵃ`,

driven by the continuous, non-gated second-order Ricci–DeTurck nonlinearity.  Concretely:

* `u = maxRegDuhamelMap (a:ℝ) hT hT1 0 gforce` — `u` is the affine Duhamel image of `gforce`;
* `gforce =ᵐ (fun t => N (field_{a+2} gforce t))` — the forcing reproduces the genuine second-order
  nonlinearity a.e. along the order-`(a+2)` Duhamel solution field;
* `trace₀ u = 0` — the initial value is `0`;
* `∂_t u = Δ_∇ (field_{a+2} gforce) + gforce` — the strong `L²(Hᵃ)` flow identity.

Existence is the Banach fixed point of the **mixed-view forcing contraction**
`deTurckMixedForcingMap` on the `L²(Hᵃ)`-ball of radius `ρ`, whose Lipschitz modulus
`Λ(ρ,T) = C₁(1+T)²ρ + C₂·2√T` is `< 1` for small `ρ` (killing the second-order arm, paired with
the `(1+T)`-field bound) and small `T` (killing the lower-order arm, paired with the `2√T`-decaying
`H^{a+1}`-field bound); the second-order pairing rests on the one honest analytic leaf
`deTurckSobolevNHa2_mixed_lipschitz`. -/
theorem deTurckRicci_quasilinear_maxreg_solution (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) (ha_even : Even a) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (a : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) +
              gforce := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  -- the two refined-estimate constants and the spectral source-mass
  set C₁ := (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
    a ha_super ha_even).choose with hC₁def
  set C₂ := (deTurckSobolevNHa2_mixed_lipschitz (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
    a ha_super ha_even).choose_spec.choose with hC₂def
  set M₀ := ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  -- the forcing-ball radius (kills the second-order arm for `T ≤ 1`)
  set ρ : ℝ := 1 / (16 * ((C₁ : ℝ) + 1)) with hρdef
  have hC₁p : (0 : ℝ) < 16 * ((C₁ : ℝ) + 1) := by positivity
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  -- the time horizon (kills the lower-order arm and closes stay-in-ball)
  set T₀ : ℝ := min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2)) ((ρ / (2 * (M₀ + 1))) ^ 2)) with hT₀def
  have hT₀pos : 0 < T₀ := by
    refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · have : 0 < ρ / (2 * (M₀ + 1)) := by positivity
      positivity
  refine ⟨T₀, hT₀pos, ?_⟩
  intro T hT hTT₀ hT1
  -- bounds on `T` from the horizon
  have hT_le1 : T ≤ 1 := hT1
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hT_stay : T ≤ (ρ / (2 * (M₀ + 1))) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the contraction modulus
  set Λ : ℝ := (C₁ : ℝ) * (1 + T) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T) with hΛdef
  have hΛnn : 0 ≤ Λ := by
    rw [hΛdef]; have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  -- second-order arm `≤ 1/4`
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have harm1 : (C₁ : ℝ) * (1 + T) * ρ * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (1 + T) * ρ * (1 + T) ≤ (C₁ : ℝ) * 2 * ρ * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      gcongr
    refine le_trans hle ?_
    rw [hρdef]
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]
  -- lower-order arm `≤ 1/4`
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  have hΛ_le : Λ ≤ 1 / 2 := by rw [hΛdef]; linarith
  have hΛ_lt : Λ < 1 := by linarith
  -- the truncated global contraction `Ψ̃ = Ψ ∘ retract`
  set Ψ := deTurckMixedForcingMap (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even hT hT1
    with hΨdef
  set z₀ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := 0 with hz₀
  set ρt := recenteredBallRetraction (z₀) ρ with hρtdef
  set Ψ' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := fun F => Ψ (ρt F) with hΨ'def
  -- `Ψ` is `Λ`-Lipschitz on the `ρ`-ball
  have hΨ_ball : ∀ (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖F‖ ≤ ρ → ‖F'‖ ≤ ρ → ‖Ψ F - Ψ F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F' hF hF'
    have h := deTurckMixedForcingMap_dist_le (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super ha_even hT hT1 hρpos.le F F' hF hF'
    rw [hΛdef]
    exact h
  -- `ρt` maps everything into the ball and is `1`-Lipschitz
  have hρt_mem : ∀ F, ρt F ∈ Metric.closedBall z₀ ρ := fun F =>
    recenteredBallRetraction_mapsTo (X := _) hρpos.le z₀ (Set.mem_univ F)
  have hρt_norm : ∀ F, ‖ρt F‖ ≤ ρ := by
    intro F
    have := hρt_mem F
    rw [Metric.mem_closedBall, hz₀, dist_zero_right] at this
    exact this
  have hρt_lip : LipschitzWith 1 ρt := recenteredBallRetraction_lipschitzWith hρpos.le z₀
  -- `Ψ'` is globally `Λ`-Lipschitz
  have hΨ'_lip : ∀ (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖Ψ' F - Ψ' F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F'
    have hbase := hΨ_ball (ρt F) (ρt F') (hρt_norm F) (hρt_norm F')
    refine le_trans hbase ?_
    have hretr : ‖ρt F - ρt F'‖ ≤ ‖F - F'‖ := by
      have := hρt_lip.dist_le_mul F F'
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at this
      exact this
    exact mul_le_mul_of_nonneg_left hretr hΛnn
  -- assemble the contraction
  have hcontr : ContractingWith Λ.toNNReal Ψ' := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hΛnn]
      simpa using hΛ_lt
    · refine LipschitzWith.of_dist_le_mul (fun F F' => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛnn]
      exact hΨ'_lip F F'
  -- the fixed point
  set Fstar := ContractingWith.fixedPoint Ψ' hcontr with hFstar_def
  have hFstar_fix : Ψ' Fstar = Fstar := ContractingWith.fixedPoint_isFixedPt hcontr
  -- `Ψ(0)` is `√T·M₀`-small, hence `Ψ'` maps the ball into itself, hence `Fstar ∈ ball`
  have hΨ0 : ‖Ψ z₀‖ ≤ Real.sqrt T * M₀ := by
    rw [hΨdef, hz₀, hM₀def]
    exact norm_deTurckMixedForcingMap_zero_le (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super ha_even hT hT1
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (M₀ + 1)) := by
      rw [show ρ / (2 * (M₀ + 1)) = Real.sqrt ((ρ / (2 * (M₀ + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (M₀ + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (M₀ + 1))) * (M₀ + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (M₀ + 1) ≠ 0 := by positivity
          field_simp
  have hz₀norm : ‖z₀‖ = 0 := by rw [hz₀, norm_zero]
  -- `Ψ` maps the `ρ`-ball into itself
  have hΨ_stay : ∀ G, ‖G‖ ≤ ρ → ‖Ψ G‖ ≤ ρ := by
    intro G hG
    have hball := hΨ_ball G z₀ hG (by rw [hz₀norm]; exact hρpos.le)
    have hGz : ‖G - z₀‖ = ‖G‖ := by rw [hz₀, sub_zero]
    rw [hGz] at hball
    calc ‖Ψ G‖ = ‖(Ψ G - Ψ z₀) + Ψ z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ψ G - Ψ z₀‖ + ‖Ψ z₀‖ := norm_add_le _ _
      _ ≤ Λ * ‖G‖ + Real.sqrt T * M₀ := add_le_add hball hΨ0
      _ ≤ (1 / 2) * ρ + ρ / 2 := by
          refine add_le_add ?_ hsqrtTM
          calc Λ * ‖G‖ ≤ Λ * ρ := mul_le_mul_of_nonneg_left hG hΛnn
            _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hΛ_le hρpos.le
      _ = ρ := by ring
  -- the fixed point lies in the ball: `Fstar = Ψ' Fstar = Ψ (ρt Fstar)` and `ρt Fstar ∈ ball`
  have hFstar_mem : ‖Fstar‖ ≤ ρ := by
    have heq : Fstar = Ψ (ρt Fstar) := hFstar_fix.symm
    rw [heq]
    exact hΨ_stay (ρt Fstar) (hρt_norm Fstar)
  -- on the ball the retraction is the identity, so `Fstar` is a genuine fixed point of `Ψ`
  have hρt_Fstar : ρt Fstar = Fstar :=
    recenteredBallRetraction_eq_self_of_mem (by
      rw [Metric.mem_closedBall, hz₀, dist_zero_right]; exact hFstar_mem)
  have hΨFstar : Ψ Fstar = Fstar := by
    have hstep : Ψ' Fstar = Ψ Fstar := by simp only [hΨ'def, hρt_Fstar]
    rw [← hstep]; exact hFstar_fix
  -- unfold the fixed-point equation to the Nemytskii reproduction identity
  set field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar with hfielddef
  have hforce_eq : Fstar = deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super ha_even field := by
    rw [← hΨFstar, hΨdef, deTurckMixedForcingMap_apply]
  -- the strong solution and its forcing
  refine ⟨maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, Fstar, rfl, ?_, ?_, ?_⟩
  · -- forcing reproduces `N` a.e. along the order-`(a+2)` Duhamel field
    have hcoe := nemytskii_coeFn (I := I) (M := M)
      (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
        a ha_super ha_even) field
    have hforce_ae : ⇑Fstar =ᵐ[timeMeasure T]
        ⇑(deTurckTimeNemytskii (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super ha_even field) := by
      rw [hforce_eq]
    refine hforce_ae.trans ?_
    rw [deTurckTimeNemytskii]
    exact hcoe
  · -- initial value `0`
    rw [maxRegDuhamelMap_trace0 (I := I) (M := M) (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, map_zero]
  · -- the `L²(Hᵃ)` flow identity
    rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) (T := T) hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
