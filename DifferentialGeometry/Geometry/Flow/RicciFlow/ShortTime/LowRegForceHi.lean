import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRealizeTwo
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftAffine

/-!
# High-scale Ricci--DeTurck forcing identity

The adjacent-scale lift already identifies the high forcing after inclusion
into `H¹`, while `lowReg_force_smooth` identifies that lower forcing with the
genuine smooth Ricci--DeTurck nonlinearity.  Injectivity of the spectral
inclusion upgrades the equality back to `H²` along the realized smooth family.

## The frozen split as the high-scale Nemytskii map

`force_hi_smooth` is the *smooth-era* variant: it needs a smooth family
realizing the trajectory, which the low-regularity solver does not produce.
The honest producer at `aHi = 2` is the **frozen split**

```
N₂ v = N 0 + A₂(v) v + A₁(v) v          (`liftHiN`)
```

read at the `H⁴` regularity the lifted solution actually has.  Every summand is
`H²`-valued there: the static field `staticForce` exists at every spectral
order, the completed second-order action `lowA2Hi` is `H⁴ → H²`, and the
completed refolded first-order action `FHi` is `H³ → H²`.

`hiN_incl` proves that `liftHiN` is a lift of the *low* frozen split
`refoldBaseN` along the scale inclusion `H⁴ → H³`.  No density argument is
needed: the two commuting inclusion squares that `lowA2_small` and `refold_aff`
already export, the radial commutation `radialCLM_incl` / `radialCLM_h3` /
`lowRadialH3_incl`, and the naturality `staticForce_incl` of the frozen field
compose summand for summand.  Chaining with `lowreg_N_affine` gives
`hiN_lowreg`, the `N₂` slot of `lowreg_force_id` in `H⁴` form, and `force_hi_id`
is the resulting a.e. Nemytskii identity `fHi =ᵐ N₂ ∘ state` for any lifted
trajectory pinned to the low state.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The lifted `H²` forcing is the genuine smooth Ricci--DeTurck
nonlinearity along any smooth family realizing the lower solution field. -/
theorem force_hi_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t))
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂timeMeasure T,
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := by
  have hlo := lowReg_force_smooth (I := I) (M := M) g₀ g_bg hR hδ
    hreal hcore field fLo hstate hforce F hpin hball
  filter_upwards [hincl, hlo] with t hi hlow
  apply tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
  calc
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t := hi
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := hlow
    _ = tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
          (symmS (I := I) (M := M) g₀ (F t)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) :=
      (deTurckSmoothN_incl (I := I) (M := M) g₀ g_bg
        (a := 1) (b := 2) (by norm_num)
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))).symm

/-! ## The frozen-split high-scale nonlinearity -/

/-- **The frozen-split Ricci--DeTurck nonlinearity at the high scale.**  It is
the `H²`-valued reading of `N v = N 0 + A₂(v) v + A₁(v) v` at an `H⁴` state:
the frozen field `staticForce` at spectral order `2`, the completed
second-order action `lowA2Hi` on its `H⁴` radial passenger, and the completed
refolded first-order action `FHi` on its `H³` radial passenger.

Both coefficient arguments are selected from the same lower `H²` view of the
state, exactly as in the low-scale `refoldBaseN`, so the two maps form a
commuting square for the scale inclusion (`hiN_incl`). -/
noncomputable def liftHiN
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
  staticForce (I := I) (M := M) g g (2 : ℝ) +
    lowA2Hi (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v) v) +
    FHi (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v)
        (lowRadialH3 (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v))

/-- **The frozen split lifts along the scale inclusion.**  Including the
high-scale frozen split back to `H¹` is the low-scale frozen split
`refoldBaseN` of the included state.  The three summands are matched by
`staticForce_incl` (with `lowBaseForce_eq_static`), by the completed
second-order square `hA2sq` together with `radialCLM_incl` and `radialCLM_h3`,
and by the refolded first-order square `hFComm` together with
`lowRadialH3_incl`.

`hA2sq` is exported by `lowA2_small`; `hFComm` by `refold_aff`. -/
theorem hiN_incl
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w) =
        (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (v : tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FHi v) =
      refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FLo
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v) := by
  set u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v with hudef
  set w : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (4 : ℝ) by norm_num) v with hwdef
  -- the two views of the state are related by the composite inclusion
  have hwu : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u = w := by
    rw [hudef, hwdef]
    exact (tensorHsInclusion_trans_apply (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v).symm
  -- the frozen field is natural for the inclusion
  have hstat : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (staticForce (I := I) (M := M) g g (2 : ℝ)) =
      lowBaseForce (I := I) (M := M) g := by
    rw [staticForce_incl (I := I) (M := M) g g
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num),
      lowBaseForce_eq_static (I := I) (M := M) g]
  -- the radial passenger commutes with the inclusion, and is the canonical one
  have hrad4 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)
      (radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ
        w v) =
      radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ
        w u := by
    have h := DFunLike.congr_fun
      (radialCLM_incl (I := I) (M := M) g
        (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w) v
    simpa only [ContinuousLinearMap.comp_apply, hudef] using h
  have hrad3 : radialCLM (I := I) (M := M) g
      (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ρ w u =
      lowRadialH3 (I := I) (M := M) g ρ u := by
    rw [← hwu]
    exact radialCLM_h3 (I := I) (M := M) g hρ u
  -- the canonical radial state commutes with the inclusion
  have hradlo : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
      (lowRadialH3 (I := I) (M := M) g ρ u) =
      lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u) :=
    lowRadialH3_incl (I := I) (M := M) g hρ u
  -- the second-order summand
  have hA2 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w
        (radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)) =
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) := by
    have h := DFunLike.congr_fun (hA2sq w)
      (radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hrad4, hrad3, hwu]
  -- the first-order summand
  have hA1 : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
      (FHi u (lowRadialH3 (I := I) (M := M) g ρ u)) =
      FLo u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) := by
    have h := DFunLike.congr_fun (hFComm u)
      (lowRadialH3 (I := I) (M := M) g ρ u)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hradlo]
  rw [show refoldBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FLo u =
      lowBaseForce (I := I) (M := M) g +
        lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
          (lowRadialH3 (I := I) (M := M) g ρ u) +
        FLo u
          (lowRadialHs (I := I) (M := M) g ρ
            (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) from rfl,
    show liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal FHi v =
      staticForce (I := I) (M := M) g g (2 : ℝ) +
        lowA2Hi (I := I) (M := M) g hρ.le hδ0 hδ_le hreal w
          (radialCLM (I := I) (M := M) g
            (show (0 : ℝ) ≤ (4 : ℝ) by norm_num) ρ w v) +
        FHi u (lowRadialH3 (I := I) (M := M) g ρ u) from rfl,
    map_add, map_add, hstat, hA2, hA1]

/-- **The frozen split is the `N₂` slot of `lowreg_force_id`, in `H⁴` form.**
For every state `w` of the lower `H³` ball whose `H⁴` lift `v` is pinned to it
by the scale inclusion, the genuine dense-extension nonlinearity `lowRegN`
agrees, after the exponent transport `((1 : ℕ) : ℝ) = (1 : ℝ)`, with the
inclusion of the high-scale frozen split at `v`.

This is `hiN_incl` chained with `lowreg_N_affine`; all hypotheses are the ones
that theorem already consumes, plus the two commuting squares. -/
theorem hiN_lowreg
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hreal' : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g₀ 0 2,
      lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S).a2Lo
          (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFcore : ∀ S : SmoothCcTensor g₀ 0 2,
      FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w) =
        (lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (w : lowerState (I := I) (M := M) g₀ 1 R)
    (v : tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ))
    (hv : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) v =
      tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) w.1) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal w) =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (liftHiN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FHi v) := by
  rw [hiN_incl (I := I) (M := M) g₀ hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm v, hv]
  exact lowreg_N_affine (I := I) (M := M) hDim g₀ hR hρ hRρ hδ0 hδ_le hδ
    hreal hreal' hNcont hcore hA2cont hA2core FLo hFLo hFcore w

/-- **The honest high-scale Nemytskii identity at `aHi = 2`.**  For a lifted
trajectory whose `H⁴` field `hi` is pinned to the low `H³` state, the high
forcing is the frozen split evaluated along that field.

The proof is `lowreg_force_lo` (the unconditional lower-scale half) composed
with `hiN_lowreg` and injectivity of the scale inclusion; no regularity,
smallness or smooth-representative hypothesis enters.  This replaces
`force_hi_smooth` for the low-regularity era: the smooth family it needs has no
producer in the solution packet, whereas `hi` and its pin do. -/
theorem force_hi_id
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {R ρ δ T : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hreal' : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hNcont : Continuous (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g₀ hδ hreal))
    (hA2cont : Continuous
      (lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g₀ 0 2,
      lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S) =
        (refoldCore (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S).a2Lo
          (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFcore : ∀ S : SmoothCcTensor g₀ 0 2,
      FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M) +
          (oneCore (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' S).a1Lo (I := I) (M := M))
    (hA2sq : ∀ w : tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowA2Hi (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w) =
        (lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' w).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ (4 : ℝ) by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hi : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ))
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hpin : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (3 : ℝ) ≤ (4 : ℝ) by norm_num) (hi t) =
        tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) (state t).1)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal (state t)) :
    (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FHi
        (hi t) := by
  filter_upwards [lowreg_force_lo (I := I) (M := M) g₀ g₀ hR hδ hreal
    (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) state fHi fLo hincl hforce,
    hpin] with t ht hp
  -- transport the lower-scale identity to the literal exponent `1`
  have hcongr := congrArg
    (fun z => tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) z) ht
  simp only at hcongr
  rw [tensorHsCongr_incl (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
      (show (2 : ℝ) = (2 : ℝ) from rfl)
      (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
      (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t),
    tensorHsCongr_refl,
    hiN_lowreg (I := I) (M := M) hDim g₀ hR hρ hRρ hδ0 hδ_le hδ
      hreal hreal' hNcont hcore hA2cont hA2core FHi FLo hFLo hFcore
      hA2sq hFComm (state t) (hi t) hp] at hcongr
  exact tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) hcongr

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
