import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftSmall
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifNZeroBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseFixedPoint

/-!
# The frozen forcing of the adjacent-scale lift (the `N`-term at `aHi = 2`)

`lowreg_lift_two` (`ShortTime/LowRegLiftTwo.lean`) drives the order-two
bootstrap by an *affine* fixed-point equation

```
f = nonautL2Map … A2 A1 f + f0
```

at each of the two scales.  The state-dependent part of the Ricci--DeTurck
nonlinearity is carried entirely by the coefficient families `A2`, `A1`
(Lane B, `TensorMaximalRegularity/LowRegOperatorTime.lean`); what is left is the
constant term `f0`, the nonlinearity **frozen at the zero state**.  This file
produces it at both scales, together with the compatibility the lift consumes:

```
hf0 : timeL2Inclusion hOrd f0Hi = f0Lo
```

## The frozen split

Writing the quasilinear right-hand side against the frozen base state,
`N u = N 0 + (A2 u + A1 u) u` (`lowBaseN_frozen`, `lowCore_split`), the high-rung
`N`-input reduces to

1. a **static** object `N 0`, and
2. the `A1`/`A2` operator bounds, which already exist.

Part 2 is not touched here.  Part 1 is `deTurckRHSSection g_bg g₀` -- Ricci of
`g₀` plus the `g_bg`-DeTurck vector-field term, with no Laplacian and no third
metric (`deTurckRem_zero`, `nZero_eq_static`).  Its spectral embedding
`staticForce g₀ g_bg σ` exists at *every* order `σ` and is natural for the scale
inclusions, which is exactly why the `N`-side of the lift costs nothing: the
frozen forcing is a fixed smooth field, so its `H^σ` norms are plain finite
constants and raising the order is free.

## Main statements

* `timeConstL2` -- the constant-in-time `L²(0,T)` class of a fixed vector, with
  `norm_timeConstL2_le` (size `‖x‖ √T`, through `norm_toLp_le_bd`) and
  `compLpL_timeConstL2` (any continuous linear map commutes with it).
* `staticForce` -- the frozen Ricci--DeTurck field at an arbitrary spectral
  order, with `staticForce_incl` (inclusion naturality) and `staticForce_congr`
  (exponent transport).
* `baseForceH2_eq_static`, `lowBaseForce_eq_static` -- the two forcing objects
  the low-base layer already carries are this static field at orders `2`, `1`.
* `nZero_staticForce`, `nZero_h1_eq` -- the static field really is `N(0)`, also
  at the literal order `1` at which the lift is instantiated.
* `liftForceHi` / `liftForceLo` and `lift_force_incl` -- the `f0Hi`, `f0Lo` and
  `hf0` inputs of `lowreg_lift_two` at `aHi = 2`, with the two static size
  bounds `norm_liftForceHi_le` / `norm_liftForceLo_le`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

/-! ## The constant-in-time `L²` class

Canonical home if this gets reused outside the lift lane:
`Analysis/Parabolic/TimeSobolev/BochnerL2.lean`.  It is kept here so that the
low-level time layer is not invalidated while other lanes build. -/

section TimeConst

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y]

/-- The constant-in-time element of `L²([0,T]; X)` with value `x`. -/
def timeConstL2 (T : ℝ) (x : X) : timeL2 X T :=
  (memLp_const (μ := timeMeasure T) (p := 2) x).toLp _

theorem timeConstL2_coeFn (T : ℝ) (x : X) :
    timeConstL2 T x =ᵐ[timeMeasure T] fun _ => x :=
  MemLp.coeFn_toLp _

/-- The constant-in-time class has the `√T` size of its value.  This is the
`M √T` shape the smallness layer of the lift already speaks
(`norm_toLp_le_bd`, `LowRegLiftSmall.lean`). -/
theorem norm_timeConstL2_le (T : ℝ) (x : X) :
    ‖timeConstL2 T x‖ ≤ ‖x‖ * Real.sqrt T :=
  norm_toLp_le_bd (memLp_const (μ := timeMeasure T) (p := 2) x) (norm_nonneg x)
    (Filter.Eventually.of_forall fun _ => le_rfl)

/-- Every continuous linear map commutes with the constant-in-time class. -/
theorem compLpL_timeConstL2 (L : X →L[ℝ] Y) (T : ℝ) (x : X) :
    L.compLpL 2 (timeMeasure T) (timeConstL2 T x) = timeConstL2 T (L x) := by
  refine Lp.ext ?_
  have h1 := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) (timeConstL2 T x)
  have h2 := timeConstL2_coeFn (X := X) T x
  have h3 := timeConstL2_coeFn (X := Y) T (L x)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3]

end TimeConst

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
/-- The time-`L²` scale inclusion is computed pointwise on constant-in-time
classes. -/
theorem timeL2Inclusion_const {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) (x : tensorHs (I := I) (M := M) g 0 2 σ) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (timeConstL2 T x) =
      timeConstL2 T
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hτσ x) :=
  compLpL_timeConstL2 _ T x

/-! ## The frozen Ricci--DeTurck forcing at an arbitrary order -/

/-- **The frozen (zero-state) Ricci--DeTurck forcing at spectral order `σ`.**
It is the spectral embedding of the static field `deTurckRHSSection g_bg g₀`:
Ricci of `g₀` plus the `g_bg`-DeTurck vector-field term, with no Laplacian and
no third metric. -/
def staticForce (g₀ g_bg : SmoothRiemannianMetric I M) (σ : ℝ) :
    tensorHs (I := I) (M := M) g₀ 0 2 σ :=
  smoothCcToTensorHs (I := I) (M := M) g₀ σ
    (deTurckRHSSection (I := I) g_bg g₀)

/-- The frozen forcing is natural for the scale inclusions: raising its order
and including back is the identity.  This is what makes the `N`-side of the
adjacent-scale lift free. -/
theorem staticForce_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (staticForce (I := I) (M := M) g₀ g_bg σ) =
      staticForce (I := I) (M := M) g₀ g_bg τ :=
  tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hτσ _

/-- The frozen forcing survives the exponent transport of `ExponentCongr`. -/
theorem staticForce_congr (g₀ g_bg : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2 hab
        (staticForce (I := I) (M := M) g₀ g_bg a) =
      staticForce (I := I) (M := M) g₀ g_bg b := by
  cases hab
  rfl

/-- The order-two affine forcing already carried by the low-base layer is the
frozen field. -/
theorem baseForceH2_eq_static (g₀ g_bg : SmoothRiemannianMetric I M) :
    baseForceH2 (I := I) (M := M) g₀ g_bg =
      staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ) := by
  refine Eq.trans (congrArg (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ))
    (deTurckRem_zero (I := I) (M := M) g₀ g_bg _ _)) ?_
  exact tensorHs.ext (funext fun _ => rfl)

/-- The order-one affine forcing already carried by the low-base layer is the
frozen field at the background `g_bg := g`. -/
theorem lowBaseForce_eq_static (g : SmoothRiemannianMetric I M) :
    lowBaseForce (I := I) (M := M) g =
      staticForce (I := I) (M := M) g g (1 : ℝ) := by
  refine Eq.trans (congrArg
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
    (baseForceH2_eq_static (I := I) (M := M) g g)) ?_
  exact staticForce_incl (I := I) (M := M) g g _

/-! ## The frozen forcing is `N(0)` -/

/-- **`N(0)` is the frozen forcing.**  The `staticForce` restatement of
`nZero_eq_static`: the genuine low-regularity nonlinearity at the zero state is
the frozen field at spectral order `((1 : ℕ) : ℝ)`. -/
theorem nZero_staticForce (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal)) :
    lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩ =
      staticForce (I := I) (M := M) g₀ g_bg ((1 : ℕ) : ℝ) :=
  nZero_eq_static (I := I) (M := M) g₀ g_bg hR hδ hreal hcore

/-- The same at the *literal* order `1` at which `lowreg_lift_two` is
instantiated: transporting `N(0)` across `((1 : ℕ) : ℝ) = (1 : ℝ)` gives the
frozen forcing that this file feeds into the low slot of the lift. -/
theorem nZero_h1_eq (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal)) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
          ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩) =
      staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ) := by
  refine Eq.trans (congrArg
    (fun v => tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) v)
    (nZero_staticForce (I := I) (M := M) g₀ g_bg hR hδ hreal hcore)) ?_
  exact staticForce_congr (I := I) (M := M) g₀ g_bg _

/-! ## The two forcing inputs of `lowreg_lift_two` at `aHi = 2` -/

/-- The `f0Hi` input of `lowreg_lift_two` at `aHi = 2`: the frozen
Ricci--DeTurck forcing, constant in time, at spectral order `2`. -/
def liftForceHi (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ))

/-- The `f0Lo` input of `lowreg_lift_two` at `aLo = 1`: the same frozen forcing
at spectral order `1`. -/
def liftForceLo (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)) T :=
  timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ))

/-- **The forcing compatibility of the adjacent-scale lift.**  The high-rung
frozen forcing includes onto the low-rung one, at any pair of orders; no
smallness, no coefficient bound and no regularity of the state enters. -/
theorem timeConst_static_incl (g₀ g_bg : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg σ)) =
      timeConstL2 T (staticForce (I := I) (M := M) g₀ g_bg τ) := by
  rw [timeL2Inclusion_const, staticForce_incl]

/-- **The `hf0` input of `lowreg_lift_two` at `aHi = 2`, verbatim.** -/
theorem lift_force_incl (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        (liftForceHi (I := I) (M := M) g₀ g_bg T) =
      liftForceLo (I := I) (M := M) g₀ g_bg T :=
  timeConst_static_incl (I := I) (M := M) g₀ g_bg _ T

/-- The size of the high-rung frozen forcing, closed in the frozen data: any
bound `D` on the `H²(g₀)` norm of the static field bounds it by `D √T`.  The
constant does not involve the `A1`/`A2` coefficient constants at all. -/
theorem norm_liftForceHi_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (2 : ℝ)‖ ≤ D) :
    ‖liftForceHi (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

/-- The size of the low-rung frozen forcing. -/
theorem norm_liftForceLo_le (g₀ g_bg : SmoothRiemannianMetric I M) (T : ℝ)
    {D : ℝ} (hD : ‖staticForce (I := I) (M := M) g₀ g_bg (1 : ℝ)‖ ≤ D) :
    ‖liftForceLo (I := I) (M := M) g₀ g_bg T‖ ≤ D * Real.sqrt T :=
  (norm_timeConstL2_le T _).trans
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg T))

/-- The low-rung frozen forcing is the one the *existing* low-base layer already
names (`lowBaseForce`), at the background `g_bg := g`. -/
theorem liftForceLo_lowBase (g : SmoothRiemannianMetric I M) (T : ℝ) :
    liftForceLo (I := I) (M := M) g g T =
      timeConstL2 T (lowBaseForce (I := I) (M := M) g) := by
  rw [liftForceLo, lowBaseForce_eq_static]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
