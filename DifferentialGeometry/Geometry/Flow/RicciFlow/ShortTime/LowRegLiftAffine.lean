import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftNTerm
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgA1Refold
import DifferentialGeometry.Analysis.DenseExtension

/-!
# The low-regularity nonlinearity is the frozen low-base affine action

`lowreg_lift_two` (`ShortTime/LowRegLiftTwo.lean`) drives the order-two
bootstrap by the *affine* fixed-point equation `f = nonautL2Map … A2 A1 f + f0`
and consumes it as the hypothesis `hfLo`.  The low-regularity solver
`lowreg_partial_sol` (`ShortTime/LowRegDenseSolve.lean`) instead exports its
forcing in *Nemytskii* form, `gforce t = lowRegN (field t)`.  This file is the
bridge between the two.

The whole bridge reduces to one **state-level** identity,

```
lowRegN g₀ g₀ … w  =  refoldBaseN g₀ … FLo w
                                                (for every `w` in the `H3` ball)
```

`lowreg_N_affine`, proved by a closed equalizer plus density of the smooth
core: on the smooth core both sides are the spectral embedding of the genuine
smooth Ricci--DeTurck remainder (`lowRegN_on_smooth`, then `refold_split`,
`a2Lo_core`, `refoldLo_core`, `lowRadial_eq_self`), and the equalizer is closed
because both sides are continuous.

Closedness needs continuity of the two completed coefficient maps.  The `A2`
half is banked (`lowA2_small` / `radialA2_lip`) and enters as the two
hypotheses `hA2cont`, `hA2core`.  The `A1` half is the refolded continuous map
`FLo`; its smooth-core formula is supplied by `refold_time`.  Thus the active
state identity no longer consumes the false raw `hA1pair` route.

**Background restriction.**  `lowBaseN`, `lowBaseForce` and `lowCoreData` are
all single-metric (`lowBaseData g g`), and `liftForceLo_lowBase` is stated only
at `g_bg = g`.  The bridge is therefore stated at `g_bg := g₀` and nowhere
claims a general DeTurck background.
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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ## Exponent and embedding bookkeeping -/

/-- The two spectral embeddings of a smooth compactly supported `(0,2)`-tensor
agree: they have the same eigenbasis coordinates by construction. -/
theorem smoothCcToTensorHs_eq_ccToHs (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g σ S =
      ccTensorToHs (I := I) (M := M) g 2 σ S :=
  tensorHs.ext (funext fun _ => rfl)

/-- Exponent transport of the smooth spectral embedding. -/
theorem tensorHsCongr_smoothCc (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (S : SmoothCcTensor g 0 2) :
    tensorHsCongr (I := I) (M := M) g 0 2 hab
        (smoothCcToTensorHs (I := I) (M := M) g a S) =
      smoothCcToTensorHs (I := I) (M := M) g b S := by
  cases hab
  rfl

/-- The scale inclusion computed on the smooth spectral embedding. -/
theorem tensorHsInclusion_ccToHs (g : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (S : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hτσ
        (ccTensorToHs (I := I) (M := M) g 2 σ S) =
      ccTensorToHs (I := I) (M := M) g 2 τ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff, ccTensorToHs_coeff]

/-- Exponent transport is involutive. -/
theorem tensorHsCongr_symm_self (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (u : tensorHs (I := I) (M := M) g 0 2 a) :
    tensorHsCongr (I := I) (M := M) g 0 2 hab.symm
        (tensorHsCongr (I := I) (M := M) g 0 2 hab u) = u := by
  cases hab
  rfl

/-- The `H^σ` size of a smooth tensor does not depend on the spelling of `σ`. -/
theorem norm_smoothCc_congr (g : SmoothRiemannianMetric I M) {a b : ℝ}
    (hab : a = b) (S : SmoothCcTensor g 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g a S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g b S‖ := by
  cases hab
  rfl

/-- The smooth Ricci--DeTurck nonlinearity is the spectral embedding of the
genuine smooth remainder; this is its definition, named for rewriting. -/
theorem deTurckSmoothN_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) :=
  rfl

/-- The smooth remainder depends on its tensor argument only, not on the
smallness certificates. -/
theorem deTurckSmoothRem_congr (g₀ g_bg : SmoothRiemannianMetric I M)
    {S U : SmoothCcTensor g₀ 0 2} (h : S = U) {δ : ℝ} (hδ_lt : δ < 1)
    (hS : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hU : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ U) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg S hδ_lt hS =
      deTurckSmoothRemainder (I := I) g₀ g_bg U hδ_lt hU := by
  subst h
  rfl

/-! ## The two consumers of the open `a1Lo` pair estimate -/

section A1

variable (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}

/-- The `D₄`-free ball-local pair estimate for the completed first-order low
coefficient on the smooth core.  This is the single open analytic input of the
`hfLo` bridge (the `a1Lo` half of the low-base pair lane's follow-up); it is
kept as a named abbreviation so that its two consumers below make the
dependency visible. -/
abbrev LowA1CorePair (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) : Prop :=
  ∀ r : ℝ, ∃ K : ℝ, ∀ S U : SmoothCcTensor g 0 2,
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r →
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
      ‖(lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a1Lo
              (I := I) (M := M) -
            (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal U).a1Lo
              (I := I) (M := M)‖ ≤
        K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S -
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖

variable {g}

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed first-order low coefficient reads off its smooth-core value.
Sibling of the `a2` statement in `radialA2_lip`. -/
theorem lowA1Lo_core {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : LowA1CorePair (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (S : SmoothCcTensor g 0 2) :
    lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal S).a1Lo
        (I := I) (M := M) :=
  DifferentialGeometry.Analysis.extend_pair_apply
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (LowBaseTimeInternal.a1LoCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (fun U => (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal U).a1Lo
      (I := I) (M := M))
    (LowBaseTimeInternal.a1LoCore_value (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    hpair S

set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed first-order low coefficient is continuous.  This is item (1)
of the low-base pair lane's follow-up, conditional on the same open estimate. -/
theorem lowA1Lo_cont {hρ : 0 ≤ ρ} {hδ0 : 0 ≤ δ} {hδ_le : δ ≤ 1 / 3}
    {hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ}
    (hpair : LowA1CorePair (I := I) (M := M) g hρ hδ0 hδ_le hreal) :
    Continuous (lowA1Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal) :=
  DifferentialGeometry.Analysis.cont_extend_pair
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (LowBaseTimeInternal.a1LoCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)
    (fun U => (lowCoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal U).a1Lo
      (I := I) (M := M))
    (LowBaseTimeInternal.a1LoCore_value (I := I) (M := M)
      g hρ hδ0 hδ_le hreal)
    hpair

end A1

/-! ## Continuity of the frozen low-base forcing -/

/-- The same-background low-base forcing with the refolded first-order
coefficient.  The second-order completion is unchanged; `FLo` is the complete
first-order action supplied by `refold_time`. -/
noncomputable def refoldBaseN
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)) :
    tensorHs (I := I) (M := M) g 0 2 (1 : ℝ) :=
  lowBaseForce (I := I) (M := M) g +
    lowA2Lo (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    FLo u
      (lowRadialHs (I := I) (M := M) g ρ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u))

/-- The autonomous low-base forcing on the `H3` state space is continuous as
soon as its two completed coefficient maps are.  Canonical home once both
continuity inputs are unconditional: `DeTurckRemainderLowBaseFixedPoint`. -/
theorem lowBaseN_cont
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hA2 : Continuous (lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal))
    (hA1 : Continuous (lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal)) :
    Continuous (lowBaseN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal) := by
  have hincl : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)).continuous
  have h2 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((hA2.comp hincl).prodMk (lowRadialH3_cont (I := I) (M := M) g hρ))
  have h1 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowA1Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hA1.prodMk
        ((lowRadialHs_cont (I := I) (M := M) g hρ.le).comp hincl))
  exact (continuous_const.add h2).add h1

/-- The refolded low-base forcing is continuous when its unchanged
second-order completion and its complete first-order coefficient are
continuous. -/
theorem refoldBaseN_cont
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hA2 : Continuous (lowA2Lo (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal))
    (hFLo : Continuous FLo) :
    Continuous (refoldBaseN (I := I) (M := M)
      g hρ.le hδ0 hδ_le hreal FLo) := by
  have hincl : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)).continuous
  have h2 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      lowA2Lo (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)
        (lowRadialH3 (I := I) (M := M) g ρ u) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((hA2.comp hincl).prodMk (lowRadialH3_cont (I := I) (M := M) g hρ))
  have h1 : Continuous fun u : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) =>
      FLo u
        (lowRadialHs (I := I) (M := M) g ρ
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num) u)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hFLo.prodMk ((lowRadialHs_cont (I := I) (M := M) g hρ.le).comp hincl))
  exact (continuous_const.add h2).add h1

/-! ## The state-level identity -/

/-- **The low-regularity Nemytskii nonlinearity is the refolded low-base affine
action.**  For every state `w` of the `H3` ball, the genuine dense-extension
nonlinearity `lowRegN` agrees, after the exponent transport
`((1 : ℕ) : ℝ) = (1 : ℝ)`, with `refoldBaseN` evaluated at the same state.

`hNcont` and `hcore` are exported verbatim by `lowreg_partial_sol`; `hA2cont`
and `hA2core` by `lowA2_small` / `radialA2_lip`.  The refolded first-order
coefficient and its smooth-core formula are the state-level outputs of
`refold_time`. -/
theorem lowreg_N_affine
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
    (w : lowerState (I := I) (M := M) g₀ 1 R) :
    tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal w) =
      refoldBaseN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
        (tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) w.1) := by
  classical
  have hzeroNorm : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
      (0 : SmoothCcTensor g₀ 0 2)‖ ≤ ρ := by
    rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2) = 0 by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ))]
    simpa only [norm_zero] using hρ.le
  have hΦcont : Continuous fun v : lowerState (I := I) (M := M) g₀ 1 R =>
      tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal v) :=
    (tensorHsCongr (I := I) (M := M) g₀ 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).continuous.comp hNcont
  have hΨcont : Continuous fun v : lowerState (I := I) (M := M) g₀ 1 R =>
      refoldBaseN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
        (tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1) :=
    (refoldBaseN_cont (I := I) (M := M) g₀ hρ hδ0 hδ_le hreal'
        FLo hA2cont hFLo).comp
      ((tensorHsCongr (I := I) (M := M) g₀ 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)).continuous.comp
          continuous_subtype_val)
  have hclosed : IsClosed {v : lowerState (I := I) (M := M) g₀ 1 R |
      tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
        refoldBaseN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
          (tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    isClosed_eq hΦcont hΨcont
  have hsub : smoothCore (I := I) (M := M) g₀ R ⊆
      {v : lowerState (I := I) (M := M) g₀ 1 R |
        tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
          refoldBaseN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} := by
    intro v hv
    obtain ⟨S, hS⟩ := hv
    -- the state-ball bound, read on the smooth representative
    have hball : ‖tensorHsInclusion (I := I) (M := M) (g := g₀)
        (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R := by
      rw [hS]
      exact v.2
    have hnorm : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R := by
      rwa [tensorHsInclusion_smoothCcToTensorHs] at hball
    have hnorm2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S‖ ≤ R := by
      rw [← smoothCcToTensorHs_eq_ccToHs,
        ← norm_smoothCc_congr (I := I) (M := M) g₀
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S]
      exact hnorm
    have hsymm2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (symmS (I := I) (M := M) g₀ S)‖ ≤ ρ := by
      refine le_trans ?_ (le_trans hnorm2 hRρ)
      rw [← smoothCcToTensorHs_eq_ccToHs, ← smoothCcToTensorHs_eq_ccToHs]
      exact norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (2 : ℝ) S
    have hrad : lowRadial (I := I) (M := M) g₀ ρ S =
        symmS (I := I) (M := M) g₀ S :=
      lowRadial_eq_self (I := I) (M := M) g₀ S hsymm2
    have hveq : v = ⟨smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) S, hball⟩ := Subtype.ext hS.symm
    -- abbreviations for the refolded coefficient bundle and the radial state
    set F := refoldCore (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S with hF
    set S' := lowRadial (I := I) (M := M) g₀ ρ S with hS'
    -- left-hand side on the smooth core
    have hLHS : tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
          (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))) := by
      rw [hveq,
        lowRegN_on_smooth (I := I) (M := M) g₀ g₀ hR hδ hreal hcore S hball,
        deTurckSmoothN_eq, tensorHsCongr_smoothCc,
        smoothCcToTensorHs_eq_ccToHs]
    -- the transported state is the smooth spectral embedding at order three
    have hu : tensorHsCongr (I := I) (M := M) g₀ 0 2
          (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
          (v.1 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) =
        ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S := by
      rw [hveq, tensorHsCongr_smoothCc, ccToHsLin_apply,
        smoothCcToTensorHs_eq_ccToHs]
    -- the zero-based smooth split
    have hsplit :
        deTurckSmoothRemainder (I := I) g₀ g₀ S' hδ
              (hreal' _ (lowRadial_norm (I := I) (M := M) g₀ hρ.le S)) -
            deTurckSmoothRemainder (I := I) g₀ g₀
              (0 : SmoothCcTensor g₀ 0 2) hδ (hreal' _ hzeroNorm) =
          F.a2 (I := I) (M := M) S' + F.a1 (I := I) (M := M) S' :=
      refold_split (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' S
    -- the smooth-core read-offs of the refolded operator
    have e1 : tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S := by
      rw [ccToHsLin_apply, ccToHsLin_apply]
      exact tensorHsInclusion_ccToHs (I := I) (M := M) g₀ _ S
    have e6 : F.a2Lo (I := I) (M := M)
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (F.a2 (I := I) (M := M) S') := by
      rw [ccToHsLin_apply]
      exact a2Lo_core (I := I) (M := M) hDim g₀ F S'
    have e7 : FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)
          (ccToHsLin (I := I) (M := M) g₀ 2 (2 : ℝ) S') =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (F.a1 (I := I) (M := M) S') := by
      rw [hFcore S, ccToHsLin_apply]
      simpa only [F] using
        (refoldLo_core (I := I) (M := M) hDim g₀
          hρ.le hδ0 hδ_le hreal' S S')
    have hRHS : refoldBaseN (I := I) (M := M)
          g₀ hρ.le hδ0 hδ_le hreal' FLo
          (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
        ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball))) := by
      rw [show refoldBaseN (I := I) (M := M)
            g₀ hρ.le hδ0 hδ_le hreal' FLo
            (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S) =
          lowBaseForce (I := I) (M := M) g₀ +
            lowA2Lo (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal'
              (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
                (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S))
              (lowRadialH3 (I := I) (M := M) g₀ ρ
                (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)) +
            FLo (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S)
              (lowRadialHs (I := I) (M := M) g₀ ρ
                (tensorHsInclusion (I := I) (M := M) (g := g₀)
                  (r := 0) (s := 2)
                  (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
                  (ccToHsLin (I := I) (M := M) g₀ 2 (3 : ℝ) S))) from rfl,
        e1,
        lowRadialH3_core (I := I) (M := M) g₀ hρ S,
        lowRadialHs_core (I := I) (M := M) g₀ hρ.le S,
        hA2core S, ← hF, ← hS', e6, e7,
        lowBaseForce_core (I := I) (M := M) g₀,
        ← ccTensorToHs_add, ← ccTensorToHs_add]
      refine congrArg (ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)) ?_
      have hz0 := deTurckRem_zero (I := I) (M := M) g₀ g₀
        (show (0 : ℝ) < 1 by norm_num)
        (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀)
      have hz1 := deTurckRem_zero (I := I) (M := M) g₀ g₀ hδ
        (hreal' (0 : SmoothCcTensor g₀ 0 2) hzeroNorm)
      have hrem : deTurckSmoothRemainder (I := I) g₀ g₀ S' hδ
            (hreal' _ (lowRadial_norm (I := I) (M := M) g₀ hρ.le S)) =
          deTurckSmoothRemainder (I := I) g₀ g₀
            (symmS (I := I) (M := M) g₀ S) hδ
            (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ S hball)) :=
        deTurckSmoothRem_congr (I := I) (M := M) g₀ g₀ hrad hδ _ _
      rw [← hrem, add_assoc, ← hsplit, hz0, ← hz1]
      abel
    rw [Set.mem_setOf_eq, hLHS, hu, hRHS]
  have hclos : closure (smoothCore (I := I) (M := M) g₀ R) ⊆
      {v : lowerState (I := I) (M := M) g₀ 1 R |
        tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
            (lowRegN (I := I) (M := M) g₀ g₀ hR hδ hreal v) =
          refoldBaseN (I := I) (M := M) g₀ hρ.le hδ0 hδ_le hreal' FLo
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num) v.1)} :=
    hclosed.closure_subset_iff.mpr hsub
  have hw : w ∈ closure (smoothCore (I := I) (M := M) g₀ R) := by
    rw [(smoothCore_dense (I := I) (M := M) g₀ hR).closure_eq]
    trivial
  exact hclos hw

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
