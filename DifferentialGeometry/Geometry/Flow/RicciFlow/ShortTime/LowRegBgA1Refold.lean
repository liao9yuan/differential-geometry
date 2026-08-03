import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC1Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime

/-!
# Refolded same-background first-order action

This module combines the action-level order-zero refold with the original
order-one path coefficient.  The resulting bundle has the same second-order
coefficient as the canonical low-base split and agrees with that split on the
nonlinear self-action.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
private theorem zero_fb_refold
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- The path-integrated order-one arm against an arbitrary DeTurck background
`gB`, isolated as an action bundle over the state metric `g`.  The diagonal
`gB = g` is `oneCore`. -/
noncomputable def oneCoreBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g where
  C0 := 0
  C1 := (lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).C1
  C2 := 0

/-- The original path-integrated order-one arm, isolated as an action bundle.
It is the same-background diagonal `oneCoreBg g g` of the two-metric arm. -/
noncomputable def oneCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g :=
  oneCoreBg (I := I) (M := M) g g hρ hδ0 hδ_le hreal T

/-- The complete same-background refolded low-base bundle.  Its first-order
coefficient is the sum of the order-zero passenger produced by the refold and
the original path-integrated order-one coefficient. -/
noncomputable def refoldCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g where
  C0 := (c0CoreData (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T).C0
  C1 := (c0CoreData (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).C1 +
    (lowCoreDataBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T).C1
  C2 := (lowCoreDataBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T).C2

private theorem refold_c0
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).C0 =
      (c0CoreData (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).C0 := by
  rfl

private theorem refold_c1
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).C1 =
      (c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).C1 +
        (lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal T).C1 := by
  rfl

private theorem refold_c2
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).C2 =
      (lowCoreDataBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T).C2 := by
  rfl

/-- On the smooth core, the sum of the two completed low actions realizes the
complete refolded first-order action. -/
theorem refoldLo_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T W : SmoothCcTensor g 0 2) :
    ((c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) +
        (oneCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M))
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        ((refoldCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1 (I := I) (M := M) W) := by
  let C := c0CoreData (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let O := oneCore (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := refoldCore (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change (C.a1Lo (I := I) (M := M) + O.a1Lo (I := I) (M := M))
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
    ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
      (F.a1 (I := I) (M := M) W)
  have hcore :
      C.a1 (I := I) (M := M) W + O.a1 (I := I) (M := M) W =
        F.a1 (I := I) (M := M) W := by
    simp only [C, O, F, refoldCore, oneCore, oneCoreBg, LowBaseActionData.a1,
      ← appCcRS_zero_eq_appCc, appCcRS_zero_left, appCcRS_add_left,
      zero_add, add_assoc]
  rw [ContinuousLinearMap.add_apply,
    a1Lo_core_any (I := I) (M := M) hDim g C W,
    a1Lo_core_any (I := I) (M := M) hDim g O W,
    ← ccTensorToHs_add, hcore]

private theorem refold_zero
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (lowCoreDataBg (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal T).C0
        (iteratedCovGrad (I := I) g 0 2 0
          (lowRadial (I := I) (M := M) g ρ T)) =
      (c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1 (I := I) (M := M)
        (lowRadial (I := I) (M := M) g ρ T) := by
  simpa only [lowCoreDataBg, iteratedCovGrad_zero] using
    c0Core_self (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T

private theorem refold_first
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := refoldCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.a1 (I := I) (M := M) S = F.a1 (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreDataBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let C := c0CoreData (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := refoldCore (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change A.a1 (I := I) (M := M) S = F.a1 (I := I) (M := M) S
  have hzero := refold_zero (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  have hF0 : F.C0 = C.C0 :=
    refold_c0 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  have hF1 : F.C1 = C.C1 + A.C1 :=
    refold_c1 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  simp only [iteratedCovGrad_zero, LowBaseActionData.a1] at hzero
  rw [LowBaseActionData.a1, LowBaseActionData.a1]
  rw [hF0, hF1, appCc_add_left, hzero]
  abel

private theorem refold_second
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := refoldCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.a2 (I := I) (M := M) S = F.a2 (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreDataBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let F := refoldCore (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  change A.a2 (I := I) (M := M) S = F.a2 (I := I) (M := M) S
  have hF2 : F.C2 = A.C2 :=
    refold_c2 (I := I) (M := M) g hρ hδ0 hδ_le hreal T
  rw [LowBaseActionData.a2, LowBaseActionData.a2, hF2]

private theorem refold_action
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T
    let F := refoldCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    A.a2 (I := I) (M := M) S + A.a1 (I := I) (M := M) S =
      F.a2 (I := I) (M := M) S + F.a1 (I := I) (M := M) S := by
  exact congrArg₂ (· + ·)
    (refold_second (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T)
    (refold_first (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T)

/-- The canonical same-background remainder split is unchanged after the
order-zero self-action is refolded into `refoldCore`. -/
theorem refold_split
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let F := refoldCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g g S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fb_refold (I := I) (M := M) g hδ0) =
      F.a2 (I := I) (M := M) S + F.a1 (I := I) (M := M) S := by
  exact (lowCoreBg_split (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T).trans
      (refold_action (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T)

private abbrev metricH3 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricH3 (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

/-- **The trajectory-free affine packet of the complete refolded first-order
action against an arbitrary DeTurck background `gB`.**  It is the sum of the
background-free order-zero packet `c0_pack g` and the two-metric order-one
packet `c1_bg_pack g gB`: on every coefficient radius `ρ ≤ ρ₀` the two completed
action maps `FHi`, `FLo` are continuous, realize the refolded core action on
smooth data, satisfy a common affine growth certificate `‖F x‖ ≤ Z + L‖x‖`, and
form the Sobolev-inclusion square.

Only the state metric `g` indexes the Sobolev scales; the background enters
solely through the order-one coefficient `oneCoreBg g gB`.  The same-background
diagonal is `refold_aff`. -/
theorem refold_aff_bg
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricH3 (I := I) (M := M) g →
              (metricH3 (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricH3 (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ S : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (c0CoreData (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Hi
                    (I := I) (M := M) +
                (oneCoreBg (I := I) (M := M)
                  g gB hρ.le hδ0 hδ_le hreal S).a1Hi
                    (I := I) (M := M)) ∧
            (∀ S : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (c0CoreData (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Lo
                    (I := I) (M := M) +
                (oneCoreBg (I := I) (M := M)
                  g gB hρ.le hδ0 hδ_le hreal S).a1Lo
                    (I := I) (M := M)) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) := by
  obtain ⟨ρc, hρc, hc⟩ := c0_pack (I := I) (M := M) hDim g
  obtain ⟨ρo, hρo, ho⟩ := c1_bg_pack (I := I) (M := M) hDim g gB
  let ρ0 : ℝ := min ρc ρo
  have hρ0 : 0 < ρ0 := lt_min hρc hρo
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  have hρc' : ρ ≤ ρc := hρρ0.trans (min_le_left _ _)
  have hρo' : ρ ≤ ρo := hρρ0.trans (min_le_right _ _)
  obtain ⟨Zc, Lc, hZc, hLc, FcHi, FcLo, hFcHi, hFcLo,
      hcHiCore, hcLoCore, hcHiBd, hcLoBd, hcComm⟩ :=
    hc hρ hρc' hδ0 hδ_le hreal
  obtain ⟨Zo, Lo, hZo, hLo, FoHi, FoLo, hFoHi, hFoLo,
      hoHiCore, hoLoCore, hoHiBd, hoLoBd, hoComm⟩ :=
    ho hρ hρo' hδ0 hδ_le hreal
  let Z : ℝ := Zc + Zo
  let L : ℝ := Lc + Lo
  let FHi : metricH3 (I := I) (M := M) g →
      (metricH3 (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun x => FcHi x + FoHi x
  let FLo : metricH3 (I := I) (M := M) g →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun x => FcLo x + FoLo x
  have hZ : 0 ≤ Z := add_nonneg hZc hZo
  have hL : 0 ≤ L := add_nonneg hLc hLo
  have hFHi : Continuous FHi := hFcHi.add hFoHi
  have hFLo : Continuous FLo := hFcLo.add hFoLo
  have hFHiBd : ∀ x : metricH3 (I := I) (M := M) g,
      ‖FHi x‖ ≤ Z + L * ‖x‖ := by
    intro x
    calc
      ‖FHi x‖ ≤ ‖FcHi x‖ + ‖FoHi x‖ := by
        simpa only [FHi] using norm_add_le (FcHi x) (FoHi x)
      _ ≤ (Zc + Lc * ‖x‖) + (Zo + Lo * ‖x‖) :=
        add_le_add (hcHiBd x) (hoHiBd x)
      _ = Z + L * ‖x‖ := by
        simp only [Z, L]
        ring
  have hFLoBd : ∀ x : metricH3 (I := I) (M := M) g,
      ‖FLo x‖ ≤ Z + L * ‖x‖ := by
    intro x
    calc
      ‖FLo x‖ ≤ ‖FcLo x‖ + ‖FoLo x‖ := by
        simpa only [FLo] using norm_add_le (FcLo x) (FoLo x)
      _ ≤ (Zc + Lc * ‖x‖) + (Zo + Lo * ‖x‖) :=
        add_le_add (hcLoBd x) (hoLoBd x)
      _ = Z + L * ‖x‖ := by
        simp only [Z, L]
        ring
  have hHiCore : ∀ S : SmoothCcTensor g 0 2,
      FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal S).a1Hi (I := I) (M := M) +
        (oneCoreBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal S).a1Hi (I := I) (M := M) := by
    intro S
    rw [show FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        FcHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
          FoHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) by rfl,
      hcHiCore S, hoHiCore S]
    rfl
  have hLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (c0CoreData (I := I) (M := M)
          g hρ.le hδ0 hδ_le hreal S).a1Lo (I := I) (M := M) +
        (oneCoreBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal S).a1Lo (I := I) (M := M) := by
    intro S
    rw [show FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        FcLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) +
          FoLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) by rfl,
      hcLoCore S, hoLoCore S]
    rfl
  have hcomm : ∀ x : metricH3 (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (FHi x) =
        (FLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    apply ContinuousLinearMap.ext
    intro v
    have h1 := DFunLike.congr_fun (hcComm x) v
    have h2 := DFunLike.congr_fun (hoComm x) v
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    have hv : FHi x v = FcHi x v + FoHi x v := rfl
    have hw : FLo x (incl32 (I := I) (M := M) g v) =
        FcLo x (incl32 (I := I) (M := M) g v) +
          FoLo x (incl32 (I := I) (M := M) g v) := rfl
    simp only [ContinuousLinearMap.comp_apply, hv, hw, map_add, h1, h2]
  exact ⟨Z, L, hZ, hL, FHi, FLo, hFHi, hFLo,
    hHiCore, hLoCore, hFHiBd, hFLoBd, hcomm⟩

/-- **The trajectory-free affine packet of the complete same-background
refolded first-order action.**  It is the sum of the order-zero packet
`c0_pack` and the order-one packet `c1_bg_pack`: on every coefficient radius
`ρ ≤ ρ₀` the two completed action maps `FHi`, `FLo` are continuous, realize the
refolded core action on smooth data, satisfy a common affine growth certificate
`‖F x‖ ≤ Z + L‖x‖`, and form the Sobolev-inclusion square.

No time horizon and no trajectory occur, so a consumer may cap a radius against
`L` before any trajectory exists; the time-`L²` certificates along a trajectory
are produced from this packet alone by `refoldAffA1_memLp` and
`refoldAffA1Hi_memLp`, and the a.e. square by `refoldAffA1_compat`.

This is the same-background diagonal `gB = g` of `refold_aff_bg`. -/
theorem refold_aff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ),
      ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
        ∃ FHi : metricH3 (I := I) (M := M) g →
              (metricH3 (I := I) (M := M) g →L[ℝ]
                metricH2 (I := I) (M := M) g),
          ∃ FLo : metricH3 (I := I) (M := M) g →
              (metricH2 (I := I) (M := M) g →L[ℝ]
                metricH1 (I := I) (M := M) g),
            Continuous FHi ∧ Continuous FLo ∧
            (∀ S : SmoothCcTensor g 0 2,
              FHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (c0CoreData (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Hi
                    (I := I) (M := M) +
                (oneCore (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Hi
                    (I := I) (M := M)) ∧
            (∀ S : SmoothCcTensor g 0 2,
              FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
                (c0CoreData (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Lo
                    (I := I) (M := M) +
                (oneCore (I := I) (M := M)
                  g hρ.le hδ0 hδ_le hreal S).a1Lo
                    (I := I) (M := M)) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FHi x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              ‖FLo x‖ ≤ Z + L * ‖x‖) ∧
            (∀ x : metricH3 (I := I) (M := M) g,
              (incl12 (I := I) (M := M) g).comp (FHi x) =
                (FLo x).comp (incl32 (I := I) (M := M) g)) :=
  refold_aff_bg (I := I) (M := M) hDim g g

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
