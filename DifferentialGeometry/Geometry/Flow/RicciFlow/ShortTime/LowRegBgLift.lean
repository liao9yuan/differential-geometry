import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifBgLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgA1Refold
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgA2Time

/-!
# Metricwise coefficient certificate for the fixed-background lift

The scalar data in `BgLiftData` is chosen before the class metric varies.  This
module keeps the subsequently constructed A1 maps separate from their proof
certificate and records exactly the durable facts consumed by the adjacent-
scale realization.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The two completed first-order maps constructed after the class metric is
known.  Proofs of continuity, core agreement, bounds, and compatibility live
in `IsBgLiftAt`. -/
structure BgLiftOps (g : SmoothRiemannianMetric I M) where
  a1Hi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
  a1Lo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))

/-- The class bound's realization certificate in the `ccTensorToHs` spelling
used by the low-base coefficient layer, on the full class radius `K.realize`.

This is the radius-maximal form, available before any `BgLiftData` is chosen,
so a per-metric producer may run the coefficient machinery once and only then
restrict to a lift datum's smaller coefficient radius. -/
theorem IsLowBoundsAt.realizeCc
    {g gB : SmoothRiemannianMetric I M}
    {K : LowRegBoundData}
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (S : SmoothCcTensor g 0 2)
    (hS : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ K.realize) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) K.threshold := by
  apply hK.hreal S
  rw [show (((1 : ℕ) : ℝ) + 1) = 2 by norm_num]
  have heq :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S =
        smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S :=
    tensorHs.ext (funext fun _ => rfl)
  rw [← heq]
  exact hS

namespace BgLiftData

/-- Restrict the low-bound realization certificate to the coefficient radius
stored in the class-first lift data. -/
theorem realize
    {g gB : SmoothRiemannianMetric I M}
    {K : LowRegBoundData} (D : BgLiftData K)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (S : SmoothCcTensor g 0 2)
    (hS : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤
      D.coeffRadius) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) K.threshold :=
  hK.realizeCc S (hS.trans D.coeffRadius_le_realize)

end BgLiftData

/-- Metricwise **second-order** coefficient certificate at the scalar bounds
fixed by `BgLiftData`.

The A2 maps are the canonical completed maps `lowA2HiBg` and `lowA2LoBg`, so
this half is pure proof content: it mentions no `BgLiftOps` data.  The core
identity uses the actual fixed-background bundle `lowCoreDataBg`; no
self-background refold identity is assumed.

Split off from `IsBgLiftAt` so that the A2 contraction constant — whose
class-uniform completion constant is still an open producer — does not block
the independently workable A1 half (`IsBgA1At`). -/
structure IsBgA2At
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (D : BgLiftData K) : Prop where
  a2Hi_cont : Continuous
    (lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  a2Lo_cont : Continuous
    (lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  a2Hi_bound : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  a2Lo_bound : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  a2Hi_core : ∀ S : SmoothCcTensor g 0 2,
    lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a2Hi
          (I := I) (M := M)
  a2Lo_core : ∀ S : SmoothCcTensor g 0 2,
    lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a2Lo
          (I := I) (M := M)
  a2_square : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
          hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v) =
      (lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num))

/-- Metricwise **first-order** coefficient certificate at the scalar bounds
fixed by `BgLiftData`, stated against the **refolded** first-order bundle.

The A1 maps are explicit `BgLiftOps` data because their class-first
construction remains a separate producer.  The core identities pin them to the
single refolded bundle `refoldCoreBg g gB`, whose coefficients are the
background-free order-zero refold, the two-metric path-integrated order-one arm,
and the order-zero background correction `deltaCoreBg g gB`.  That third
summand is what makes `refold_split_bg` reproduce the arbitrary-background
remainder exactly; a certificate stated against only the first two summands
does not (ledger №203, route error #2).  `bgA1_of_refold` discharges every
field below unconditionally, from `refold_aff_bg` for the first two summands
and from `c0bg_pack` for the third.

Why the refold is forced, not stylistic (ledger №196).  The two bound fields
carry the affine shape `zero + slope * ‖x‖`, a verbatim mirror of the diagonal
lift consumer `lowreg_apply_two` (`LowRegApplyTwo.lean`, hypotheses
`hFHiBd`/`hFLoBd`) that `BgLiftData.zero`/`slope` and the horizon
`lowregLiftHorizon' contract zero` are built for.  Against the *un-refolded*
core `lowCoreDataBg`, that affine shape is refuted: №196 records a scaling
witness on which the order-zero arm's connection-difference-quadratic terms grow
like `A^{3/2}` at fixed `H²` radius, outgrowing every affine envelope.  So the
bound fields are right and the core fields had to move — which is exactly the
route-(c) ruling of ledger №199.

`a1_square` needs no restatement: it is phrased on the `BgLiftOps` data, so
supplying the refolded maps makes it the refolded square automatically.

№194's `lowA1Bg_comm_bg`/`a1_comm` — the square of the *actual* fixed-background
bundle `lowCoreDataBg` — remain true and are banked canonical API; they simply
sit off this lift's critical path. -/
structure IsBgA1At
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (D : BgLiftData K) (F : BgLiftOps (I := I) (M := M) g) : Prop where
  a1Hi_cont : Continuous F.a1Hi
  a1Lo_cont : Continuous F.a1Lo
  a1Hi_bound : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.a1Hi x‖ ≤ D.zero + D.slope * ‖x‖
  a1Lo_bound : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.a1Lo x‖ ≤ D.zero + D.slope * ‖x‖
  a1Hi_core : ∀ S : SmoothCcTensor g 0 2,
    F.a1Hi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (refoldCoreBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a1Hi
          (I := I) (M := M)
  a1Lo_core : ∀ S : SmoothCcTensor g 0 2,
    F.a1Lo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (refoldCoreBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a1Lo
          (I := I) (M := M)
  a1_square : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp (F.a1Hi x) =
      (F.a1Lo x).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num))

/-- Metricwise coefficient certificate at the scalar bounds fixed by
`BgLiftData`: the conjunction of the second-order certificate `IsBgA2At` and
the first-order certificate `IsBgA1At`.

This is the entrypoint the adjacent-scale realization consumes.  It is kept as
the conjunction of the two halves so that the still-open A2 completion constant
does not block the A1 half, which `bgA1_of_refold` produces; every one of the
fourteen original fields remains reachable through the parent projections. -/
structure IsBgLiftAt
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (D : BgLiftData K) (F : BgLiftOps (I := I) (M := M) g) : Prop extends
  IsBgA2At (I := I) (M := M) g gB K hK D,
  IsBgA1At (I := I) (M := M) g gB K hK D F

/-- **The first-order certificate `IsBgA1At` holds at arbitrary DeTurck
background for the refolded A1 maps.**

On every coefficient radius below a positive `ρ0`, `refold_aff_bg` produces the
completed maps of the first two summands of `refoldCoreBg g gB` and `c0bg_pack`
those of the third, the order-zero background correction `deltaCoreBg g gB`.
Their pointwise sums are continuous, realize the whole refolded bundle's
completed actions on smooth data (this is `refoldBg_a1Hi_split` /
`refoldBg_a1Lo_split`, the coefficient additivity of the completions), satisfy
the affine certificate `‖F x‖ ≤ (Z₁+Z₀) + (L₁+L₀)‖x‖`, and form the
adjacent-scale inclusion square.  Those are precisely the seven fields of
`IsBgA1At`.

PDE honesty.  The bundle certified here is the one for which `refold_split_bg`
reconstructs the arbitrary-background Ricci--DeTurck remainder exactly: the
zero-based remainder difference at background `gB` equals `F.a2 S + F.a1 S` for
`F = refoldCoreBg g gB`.  Dropping the `deltaCoreBg` summand — the statement
this theorem carried before ledger entries 203--205 — would certify a bundle
that does not reproduce the remainder off the diagonal.

The two domination hypotheses `Z ≤ D.zero`, `L ≤ D.slope` are the honest seam
between this per-metric producer and the class-first scalar data: `Z` and `L`
still depend on `g`, so `BgLiftData.zero`/`slope` may only be chosen once a
class-uniform version of the packet's constants exists.  The diagonal lane is
arranged the same way — `lowreg_solve_open` obtains the packet *before* any
trajectory exists and caps its realization radius against `L`. -/
theorem bgA1_of_refold
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegBoundData}
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 →
        ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
          (Z ≤ D.zero → L ≤ D.slope →
            ∃ F : BgLiftOps (I := I) (M := M) g,
              IsBgA1At (I := I) (M := M) g gB K hK D F) := by
  obtain ⟨ρ1, hρ1, hpack⟩ := refold_aff_bg (I := I) (M := M) hDim g gB
  obtain ⟨ρ2, hρ2, hdel⟩ := c0bg_pack (I := I) (M := M) hDim g gB
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, ?_⟩
  intro D hD
  obtain ⟨Z1, L1, hZ1, hL1, FHi, FLo, hFHi, hFLo, hHiCore, hLoCore,
      hHiBd, hLoBd, hcomm⟩ :=
    hpack D.coeffRadius_pos (hD.trans (min_le_left _ _))
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
  obtain ⟨Z0, L0, hZ0, hL0, GHi, GLo, hGHi, hGLo, hGHiCore, hGLoCore,
      hGHiBd, hGLoBd, hGcomm⟩ :=
    hdel D.coeffRadius_pos (hD.trans (min_le_right _ _))
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
  refine ⟨Z1 + Z0, L1 + L0, add_nonneg hZ1 hZ0, add_nonneg hL1 hL0,
    fun hZD hLD => ⟨⟨fun x => FHi x + GHi x, fun x => FLo x + GLo x⟩, ?_⟩⟩
  refine
    { a1Hi_cont := hFHi.add hGHi
      a1Lo_cont := hFLo.add hGLo
      a1Hi_bound := ?_
      a1Lo_bound := ?_
      a1Hi_core := ?_
      a1Lo_core := ?_
      a1_square := ?_ }
  · intro x
    have hsum := norm_add_le (FHi x) (GHi x)
    have hx : ‖FHi x‖ + ‖GHi x‖ ≤ D.zero + D.slope * ‖x‖ := by
      calc
        ‖FHi x‖ + ‖GHi x‖ ≤ (Z1 + L1 * ‖x‖) + (Z0 + L0 * ‖x‖) :=
          add_le_add (hHiBd x) (hGHiBd x)
        _ = (Z1 + Z0) + (L1 + L0) * ‖x‖ := by ring
        _ ≤ D.zero + D.slope * ‖x‖ :=
          add_le_add hZD (mul_le_mul_of_nonneg_right hLD (norm_nonneg x))
    exact hsum.trans hx
  · intro x
    have hsum := norm_add_le (FLo x) (GLo x)
    have hx : ‖FLo x‖ + ‖GLo x‖ ≤ D.zero + D.slope * ‖x‖ := by
      calc
        ‖FLo x‖ + ‖GLo x‖ ≤ (Z1 + L1 * ‖x‖) + (Z0 + L0 * ‖x‖) :=
          add_le_add (hLoBd x) (hGLoBd x)
        _ = (Z1 + Z0) + (L1 + L0) * ‖x‖ := by ring
        _ ≤ D.zero + D.slope * ‖x‖ :=
          add_le_add hZD (mul_le_mul_of_nonneg_right hLD (norm_nonneg x))
    exact hsum.trans hx
  · intro S
    change FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
        GHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) = _
    rw [hHiCore S, hGHiCore S]
    exact (refoldBg_a1Hi_split (I := I) (M := M) hDim g gB
      D.coeffRadius_pos.le hK.threshold_nonneg hK.threshold_le_third
      (D.realize hK) S).symm
  · intro S
    change FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
        GLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) = _
    rw [hLoCore S, hGLoCore S]
    exact (refoldBg_a1Lo_split (I := I) (M := M) hDim g gB
      D.coeffRadius_pos.le hK.threshold_nonneg hK.threshold_le_third
      (D.realize hK) S).symm
  · intro x
    apply ContinuousLinearMap.ext
    intro v
    have h1 := DFunLike.congr_fun (hcomm x) v
    have h2 := DFunLike.congr_fun (hGcomm x) v
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    change tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) ≤ 2 by norm_num) ((FHi x + GHi x) v) =
      (FLo x + GLo x)
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num) v)
    simp only [ContinuousLinearMap.add_apply, map_add, h1, h2]

/-- **The second-order certificate `IsBgA2At` holds at arbitrary DeTurck
background.**

On every coefficient radius below a positive `ρ0`, `radialA2Bg_lip` reads the
two completed maps off the actual fixed-background bundle `lowCoreDataBg g gB`
on smooth data, and `lowA2Bg_small` supplies their continuity, the adjacent-scale
inclusion square, and two operator bounds that are *linear in the coefficient
radius*.  Those are precisely the seven fields of `IsBgA2At`.

The contraction knob is the RADIUS.  `C` is produced before any `BgLiftData` is
seen, so the domination `C * D.coeffRadius ≤ D.contract` is dischargeable by
choosing `D.coeffRadius ≤ min ρ0 (D.contract / C)` — subject only to
`BgLiftData.state_le_radius`, i.e. to shrinking `K`'s state radius alongside it.
The deviation threshold `K.threshold` is *not* a knob: it is pinned by the
realization certificate and its cap `1/3` carries no smallness of its own.

PDE honesty.  The core fields name `lowCoreDataBg g gB`, the bundle whose action
`lowCoreBg_split` shows reproduces the zero-based Ricci--DeTurck remainder at
background `gB`; no diagonal identification is used anywhere below.  The A1 half
had to refold its bundle (ledger №199--206); the A2 half does not, because the
complete second-order coefficient is already small at every background —
`c2Bg_h2_small` — while the A1 order-zero arm is not affine off the diagonal.

The domination hypothesis is the honest seam between this per-metric producer
and the class-first scalar data, exactly as `bgA1_of_refold`'s `Z ≤ D.zero` and
`L ≤ D.slope` are: `C` still depends on `g`, through `c2Bg_h2_small` and the
completion transfer `a2_pair`, so a class-uniform `C` remains open. -/
theorem bgA2_of_radial
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegBoundData}
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 ≤ C ∧
      ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 →
        (C * D.coeffRadius ≤ D.contract →
          IsBgA2At (I := I) (M := M) g gB K hK D) := by
  obtain ⟨ρL, _CL, hρL, _hρL_le, hlip⟩ :=
    radialA2Bg_lip (I := I) (M := M) hDim g gB K.realize_pos
      hK.threshold_nonneg hK.threshold_le_third hK.realizeCc
  obtain ⟨ρS, C, hρS, _hρS_le, hC, hsmall⟩ :=
    lowA2Bg_small (I := I) (M := M) hDim g gB K.realize_pos
      hK.threshold_nonneg hK.threshold_le_third hK.realizeCc
  refine ⟨min ρL ρS, C, lt_min hρL hρS, hC, ?_⟩
  intro D hD hdom
  have hr0 : (0 : ℝ) ≤ D.coeffRadius := D.coeffRadius_pos.le
  have hrL : D.coeffRadius ≤ ρL := hD.trans (min_le_left _ _)
  have hrS : D.coeffRadius ≤ ρS := hD.trans (min_le_right _ _)
  obtain ⟨-, -, hcoreHi, hcoreLo, -⟩ := hlip hr0 hrL
  obtain ⟨hcontHi, hcontLo, hbdHi, hbdLo, hsq⟩ := hsmall hr0 hrS
  exact
    { a2Hi_cont := hcontHi
      a2Lo_cont := hcontLo
      a2Hi_bound := fun v => (hbdHi v).trans hdom
      a2Lo_bound := fun v => (hbdLo v).trans hdom
      a2Hi_core := hcoreHi
      a2Lo_core := hcoreLo
      a2_square := hsq }

/-- **The whole metricwise certificate `IsBgLiftAt` at one arbitrary DeTurck
background**: `bgA1_of_refold` and `bgA2_of_radial` compose on the smaller of
their two coefficient radii.

What this does and does not say.  For a *fixed* pair `(g, gB)` the fourteen-field
certificate is now a theorem, conditional only on the three scalar dominations
`Z ≤ D.zero`, `L ≤ D.slope`, `C * D.coeffRadius ≤ D.contract`.  It says nothing
class-uniform: `Z`, `L` and `C` are all produced from `g`-dependent coefficient
estimates, so a single `BgLiftData K` serving *every* metric of the class still
needs class-uniform versions of the three constants.  That is the whole content
of the remaining G3 lane; do not read this theorem as closing it. -/
theorem bgLift_of_radial
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {K : LowRegBoundData}
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K) :
    ∃ ρ0 C : ℝ, 0 < ρ0 ∧ 0 ≤ C ∧
      ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 →
        ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
          (Z ≤ D.zero → L ≤ D.slope → C * D.coeffRadius ≤ D.contract →
            ∃ F : BgLiftOps (I := I) (M := M) g,
              IsBgLiftAt (I := I) (M := M) g gB K hK D F) := by
  obtain ⟨ρ1, hρ1, hA1⟩ := bgA1_of_refold (I := I) (M := M) hDim g gB hK
  obtain ⟨ρ2, C, hρ2, hC, hA2⟩ :=
    bgA2_of_radial (I := I) (M := M) hDim g gB hK
  refine ⟨min ρ1 ρ2, C, lt_min hρ1 hρ2, hC, ?_⟩
  intro D hD
  obtain ⟨Z, L, hZ, hL, hF⟩ := hA1 D (hD.trans (min_le_left _ _))
  refine ⟨Z, L, hZ, hL, fun hZD hLD hdom => ?_⟩
  obtain ⟨F, hF1⟩ := hF hZD hLD
  exact ⟨F,
    { toIsBgA2At := hA2 D (hD.trans (min_le_right _ _)) hdom
      toIsBgA1At := hF1 }⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
