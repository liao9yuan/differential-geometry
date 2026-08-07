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

/-- The complete refolded low-base bundle against an arbitrary DeTurck
background `gB`.  Besides the order-zero passenger produced by the refold and
the two-metric path-integrated order-one coefficient, its order-zero
coefficient carries the background correction of the canonical low-base
order-zero coefficient.  That correction vanishes on the diagonal, which is why
`refoldCore` does not see it. -/
noncomputable def refoldCoreBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g where
  C0 := (c0CoreData (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).C0 +
    ((lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C0 -
      (lowCoreDataBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T).C0)
  C1 := (c0CoreData (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).C1 +
    (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).C1
  C2 := (lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).C2

private theorem refoldBg_c0
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C0 =
      (c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).C0 +
        ((lowCoreDataBg (I := I) (M := M)
            g gB hρ hδ0 hδ_le hreal T).C0 -
          (lowCoreDataBg (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal T).C0) := by
  rfl

private theorem refoldBg_c1
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C1 =
      (c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).C1 +
        (lowCoreDataBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).C1 := by
  rfl

private theorem refoldBg_c2
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C2 =
      (lowCoreDataBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C2 := by
  rfl

/-- The same-background diagonal of the arbitrary-background refold is the
original refold: the order-zero background correction cancels. -/
theorem refoldCoreBg_diag
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    refoldCoreBg (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal T =
      refoldCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T := by
  simp only [refoldCoreBg, refoldCore, sub_self, add_zero]

private theorem refoldBg_first
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := refoldCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.a1 (I := I) (M := M) S = F.a1 (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  let D := lowCoreDataBg (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal T
  let C := c0CoreData (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  let F := refoldCoreBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  change A.a1 (I := I) (M := M) S = F.a1 (I := I) (M := M) S
  have hzero := refold_zero (I := I) (M := M)
    g hρ hδ0 hδ_le hreal T
  have hF0 : F.C0 = C.C0 + (A.C0 - D.C0) :=
    refoldBg_c0 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  have hF1 : F.C1 = C.C1 + A.C1 :=
    refoldBg_c1 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  have hkey : appCc (I := I) (M := M) g 2 2 A.C0 S =
      appCc (I := I) (M := M) g 2 2 (A.C0 - D.C0) S +
        appCc (I := I) (M := M) g 2 2 D.C0 S := by
    rw [← appCc_add_left, sub_add_cancel]
  simp only [iteratedCovGrad_zero, LowBaseActionData.a1] at hzero
  rw [LowBaseActionData.a1, LowBaseActionData.a1]
  rw [hF0, hF1, appCc_add_left, appCc_add_left, hkey, hzero]
  abel

private theorem refoldBg_second
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := refoldCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.a2 (I := I) (M := M) S = F.a2 (I := I) (M := M) S := by
  dsimp only
  let S := lowRadial (I := I) (M := M) g ρ T
  let A := lowCoreDataBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  let F := refoldCoreBg (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T
  change A.a2 (I := I) (M := M) S = F.a2 (I := I) (M := M) S
  have hF2 : F.C2 = A.C2 :=
    refoldBg_c2 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T
  rw [LowBaseActionData.a2, LowBaseActionData.a2, hF2]

private theorem refoldBg_action
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    let F := refoldCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    A.a2 (I := I) (M := M) S + A.a1 (I := I) (M := M) S =
      F.a2 (I := I) (M := M) S + F.a1 (I := I) (M := M) S := by
  exact congrArg₂ (· + ·)
    (refoldBg_second (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T)
    (refoldBg_first (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T)

/-- **The canonical zero-based Ricci--DeTurck remainder split against an
arbitrary DeTurck background, after the order-zero self-action is refolded.**
The refolded bundle `refoldCoreBg g gB` reproduces the two-metric low-base
split of `lowCoreBg_split` exactly; the same-background diagonal is
`refold_split`. -/
theorem refold_split_bg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let F := refoldCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g gB
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zero_fb_refold (I := I) (M := M) g hδ0) =
      F.a2 (I := I) (M := M) S + F.a1 (I := I) (M := M) S := by
  exact (lowCoreBg_split (I := I) (M := M)
    g gB hρ hδ0 hδ_le hreal T).trans
      (refoldBg_action (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T)

/-- The order-zero **background correction** of the arbitrary-background
low-base bundle, isolated as an action bundle over the state metric `g`.

Its order-zero coefficient is the difference of the canonical low-base
order-zero coefficients at background `gB` and at background `g`; its order-one
and order-two coefficients vanish.  This is exactly the passenger by which
`refoldCoreBg g gB` exceeds the pair `c0CoreData g`, `oneCoreBg g gB`, and it
vanishes on the diagonal `gB = g`. -/
noncomputable def deltaCoreBg
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g where
  C0 := (lowCoreDataBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).C0 -
    (lowCoreDataBg (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal T).C0
  C1 := 0
  C2 := 0

/-- The arbitrary-background refold with its order-zero background correction
removed: the coefficientwise sum of `c0CoreData g` and `oneCoreBg g gB`.  Only
its order-zero and order-one coefficients are used, so its `C2` is zero. -/
private noncomputable def refoldBgMid
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowBaseActionData g where
  C0 := (c0CoreData (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).C0 +
    (oneCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).C0
  C1 := (c0CoreData (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).C1 +
    (oneCoreBg (I := I) (M := M)
      g gB hρ hδ0 hδ_le hreal T).C1
  C2 := 0

private theorem refoldMid_split0
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C0 =
      (refoldBgMid (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).C0 +
        (deltaCoreBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).C0 := by
  simp only [refoldCoreBg, refoldBgMid, deltaCoreBg, oneCoreBg, add_zero]

private theorem refoldMid_split1
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).C1 =
      (refoldBgMid (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).C1 +
        (deltaCoreBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).C1 := by
  simp only [refoldCoreBg, refoldBgMid, deltaCoreBg, oneCoreBg, add_zero]

/-- **The `H³ → H²` completion of the arbitrary-background refold is the sum of
three completed actions**: the background-free order-zero refold action, the
two-metric order-one action, and the order-zero background-correction action of
`deltaCoreBg`.

The identity is not definitional — each `a1Hi` is a norm extension — so it is
supplied by the coefficient additivity `a1Hi_add` of the completion, applied
along the coefficient decomposition of `refoldCoreBg`. -/
theorem refoldBg_a1Hi_split
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) =
      ((c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) +
        (oneCoreBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M)) +
      (deltaCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Hi (I := I) (M := M) := by
  rw [a1Hi_add (I := I) (M := M) hDim g
      (refoldBgMid (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (deltaCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldMid_split0 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldMid_split1 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T),
    a1Hi_add (I := I) (M := M) hDim g
      (c0CoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal T)
      (oneCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldBgMid (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      rfl rfl]

/-- The adjacent-scale partner of `refoldBg_a1Hi_split`: the `H² → H¹`
completion of the arbitrary-background refold is the same three-term sum. -/
theorem refoldBg_a1Lo_split
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    (refoldCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) =
      ((c0CoreData (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) +
        (oneCoreBg (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M)) +
      (deltaCoreBg (I := I) (M := M)
        g gB hρ hδ0 hδ_le hreal T).a1Lo (I := I) (M := M) := by
  rw [a1Lo_add (I := I) (M := M) hDim g
      (refoldBgMid (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (deltaCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldMid_split0 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldMid_split1 (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T),
    a1Lo_add (I := I) (M := M) hDim g
      (c0CoreData (I := I) (M := M) g hρ hδ0 hδ_le hreal T)
      (oneCoreBg (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      (refoldBgMid (I := I) (M := M) g gB hρ hδ0 hδ_le hreal T)
      rfl rfl]

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

/-- The trajectory-free affine packet of the order-zero background correction
`deltaCoreBg g gB`, as a named predicate.

**Proved** by `c0bg_pack` below; it was a registered honest input between ledger
entries 205 and 207, and the name is kept because it is the interface through
which `bgA1_of_refold` carries the *correct* bundle `refoldCoreBg g gB`.

The clause list mirrors `c0_pack` and `c1_bg_pack` verbatim: on every
coefficient radius `ρ ≤ ρ₀` the two completed maps `GHi`, `GLo` are continuous,
realize the correction bundle's completed actions on smooth data, satisfy a
common affine growth certificate `‖G x‖ ≤ Z + L‖x‖`, and form the
Sobolev-inclusion square.  The square is a genuine obligation of the packet and
not a direct instance of `a1_comm`: the latter is an identity between one
*bundle*'s two completions, whereas the field it serves is an identity between
the *maps* at an arbitrary, possibly non-smooth, state `x`; `c0bg_pack` reaches
it as the density limit of `a1_comm`. -/
def BgDeltaPack (g gB : SmoothRiemannianMetric I M) : Prop :=
  ∃ ρ0 : ℝ, 0 < ρ0 ∧
    ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
      (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
      (hreal : ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ),
    ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
      ∃ GHi : metricH3 (I := I) (M := M) g →
            (metricH3 (I := I) (M := M) g →L[ℝ]
              metricH2 (I := I) (M := M) g),
        ∃ GLo : metricH3 (I := I) (M := M) g →
            (metricH2 (I := I) (M := M) g →L[ℝ]
              metricH1 (I := I) (M := M) g),
          Continuous GHi ∧ Continuous GLo ∧
          (∀ S : SmoothCcTensor g 0 2,
            GHi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
              (deltaCoreBg (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal S).a1Hi
                  (I := I) (M := M)) ∧
          (∀ S : SmoothCcTensor g 0 2,
            GLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
              (deltaCoreBg (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal S).a1Lo
                  (I := I) (M := M)) ∧
          (∀ x : metricH3 (I := I) (M := M) g,
            ‖GHi x‖ ≤ Z + L * ‖x‖) ∧
          (∀ x : metricH3 (I := I) (M := M) g,
            ‖GLo x‖ ≤ Z + L * ‖x‖) ∧
          (∀ x : metricH3 (I := I) (M := M) g,
            (incl12 (I := I) (M := M) g).comp (GHi x) =
              (GLo x).comp (incl32 (I := I) (M := M) g))

/-- The zero action bundle: the reference point against which `a1_diff` turns a
coefficient jet bound into an operator-norm bound. -/
private noncomputable def zeroBundle
    (g : SmoothRiemannianMetric I M) : LowBaseActionData g where
  C0 := 0
  C1 := 0
  C2 := 0

private theorem zeroBundle_a1
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    (zeroBundle (I := I) (M := M) g).a1 (I := I) (M := M) W = 0 := by
  simp only [zeroBundle, LowBaseActionData.a1, ← appCcRS_zero_eq_appCc,
    appCcRS_zero_left, zero_add]

private theorem iterZ
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j
        (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_smul (I := I) (M := M) g r s j
    (0 : ℝ) (0 : SmoothCcTensor g r s)
  simpa only [zero_smul] using h

private theorem lowJetZ
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    lowJetSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  simp only [lowJetSq, iterZ (I := I) (M := M), norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]

private theorem zeroBundle_pair
    (g : SmoothRiemannianMetric I M) :
    (zeroBundle (I := I) (M := M) g).a1Hi (I := I) (M := M) = 0 ∧
      (zeroBundle (I := I) (M := M) g).a1Lo (I := I) (M := M) = 0 := by
  obtain ⟨C, _, hpair⟩ := a1_pair (I := I) (M := M) g
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          ((zeroBundle (I := I) (M := M) g).a1 (I := I) (M := M) W) ≤
        (0 : ℝ) * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    rw [zeroBundle_a1 (I := I) (M := M),
      lowJetZ (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          ((zeroBundle (I := I) (M := M) g).a1 (I := I) (M := M) W) ≤
        (0 : ℝ) * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    rw [zeroBundle_a1 (I := I) (M := M),
      lowJetZ (I := I) (M := M)]
    simp only [zero_mul]
    exact le_rfl
  obtain ⟨hHiNorm, hLoNorm, _⟩ := hpair
    (zeroBundle (I := I) (M := M) g) 0 le_rfl hHi hLo
  constructor
  · refine (ContinuousLinearMap.opNorm_zero_iff _).mp
      (le_antisymm ?_ (norm_nonneg _))
    simpa only [Real.sqrt_zero, mul_zero] using hHiNorm
  · refine (ContinuousLinearMap.opNorm_zero_iff _).mp
      (le_antisymm ?_ (norm_nonneg _))
    simpa only [Real.sqrt_zero, mul_zero] using hLoNorm

/-- The order-zero background correction is jointly *affine* in the state.

This is the affine half of `BgDeltaPack`.  It is the exact analogue of the
background-free `c0_core_affine`, with the genuinely quadratic coefficient
envelope `c0Coeff_aff` replaced by the tame background-difference envelope
`c0Bg_diff_tame`: the three quadratic arms of the self-remainder carry no
background argument and cancel in the difference. -/
private theorem c0bg_aff
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
        ∀ T : SmoothCcTensor g 0 2,
          ‖(deltaCoreBg (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal T).a1Hi (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ∧
            ‖(deltaCoreBg (I := I) (M := M)
                g gB hρ.le hδ0 hδ_le hreal T).a1Lo (I := I) (M := M)‖ ≤
              Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  obtain ⟨B0, B1, hB0, hB1, htame⟩ :=
    c0Bg_diff_tame (I := I) (M := M) hDim g gB
  obtain ⟨C2, hC2, hjet2⟩ := jet2_le_hs (I := I) (M := M) g
  obtain ⟨C3, hC3, hjet3⟩ := jet3_le_hs (I := I) (M := M) g
  obtain ⟨Ca, hCa, hact⟩ := a1_diff (I := I) (M := M) hDim g
  refine ⟨1, one_pos, ?_⟩
  intro ρ δ hρ _ hδ0 hδ_le hreal
  let R2 : ℝ := C2 * ρ
  let Z : ℝ := Ca * B0 R2
  let L : ℝ := Ca * B1 R2 * C3
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hZ : 0 ≤ Z := mul_nonneg hCa (hB0 R2 hR2)
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg hCa (hB1 R2 hR2)) hC3
  refine ⟨Z, L, hZ, hL, ?_⟩
  intro T
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  let A : LowBaseActionData g := deltaCoreBg (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal T
  let A3 : ℝ := C3 *
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
  let Q : ℝ := B0 R2 + B1 R2 * A3
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 (norm_nonneg _)
  have hQ : 0 ≤ Q := add_nonneg (hB0 R2 hR2)
    (mul_nonneg (hB1 R2 hR2) hA3)
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fb_refold (I := I) (M := M) g hδ0
  have hS2 : lowJetSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hS3n :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad
  have hS3 : lowJetSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hS3n hC3) 2
  have hraw := htame S hδ_le hδ0 hSδ hZδ R2 A3 hR2 hA3 hS2 hS3
  have hcoeffAct :
      lowJetSq (I := I) (M := M) g 2
          (A.C0 - (zeroBundle (I := I) (M := M) g).C0) +
        lowJetSq (I := I) (M := M) g 2
          (A.C1 - (zeroBundle (I := I) (M := M) g).C1) ≤ Q ^ 2 := by
    have hC1 :
        lowJetSq (I := I) (M := M) g 2
            (A.C1 - (zeroBundle (I := I) (M := M) g).C1) = 0 := by
      simp only [A, deltaCoreBg, zeroBundle, sub_zero]
      exact lowJetZ (I := I) (M := M) g 3 2 2
    rw [hC1, add_zero]
    simpa only [A, deltaCoreBg, lowCoreDataBg, zeroBundle, S, sub_zero]
      using hraw
  have hop := hact A (zeroBundle (I := I) (M := M) g) Q hQ hcoeffAct
  obtain ⟨hzHi, hzLo⟩ := zeroBundle_pair (I := I) (M := M) g
  constructor
  · calc
      ‖A.a1Hi (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzHi, sub_zero] using hop.1
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring
  · calc
      ‖A.a1Lo (I := I) (M := M)‖ ≤ Ca * Q := by
        simpa only [hzLo, sub_zero] using hop.2
      _ = Z + L * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
        simp only [Q, A3, Z, L]
        ring

/-- On every bounded spectral `H3` core ball, the two completed realizations of
the order-zero background correction are jointly Lipschitz in the state.

This is the continuity half of `BgDeltaPack`.  Unlike `c0CorePair`, whose
coefficient input is a single-background Lipschitz estimate, the correction is a
*difference* of two backgrounds, so `c0_bg_pair_h2` is consumed twice — once at
`gB` and once at the diagonal `gB = g` — and the two estimates are recombined by
`jetSub`. -/
private theorem c0bg_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧
      ∀ {ρ δ : ℝ} (hρ : 0 < ρ) (_ : ρ ≤ ρ0)
        (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hreal : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        (r : ℝ),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        let AT := deltaCoreBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T
        let AU := deltaCoreBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal U
        ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ∧
          ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
            K * ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
              ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρb, Bsb, B0b, B1b, hρb, hBsb, hB0b, hB1b, hb⟩ :=
    c0_bg_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨ρs, Bss, B0s, B1s, hρs, hBss, hB0s, hB1s, hs⟩ :=
    c0_bg_pair_h2 (I := I) (M := M) hDim g g
  obtain ⟨C2, hC2, hjet2⟩ := jet2_le_hs (I := I) (M := M) g
  obtain ⟨C3, hC3, hjet3⟩ := jet3_le_hs (I := I) (M := M) g
  obtain ⟨Ca, hCa, hact⟩ := a1_diff (I := I) (M := M) hDim g
  refine ⟨min ρb ρs, lt_min hρb hρs, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal r
  have hρb' : ρ ≤ ρb := hρρ0.trans (min_le_left _ _)
  have hρs' : ρ ≤ ρs := hρρ0.trans (min_le_right _ _)
  let r0 : ℝ := max r 0
  let R2 : ℝ := C2 * ρ
  let A3 : ℝ := C3 * r0
  let Lr : ℝ := 1 + (1 / ρ) * r0
  let W : ℝ := C3 * Lr + C2 + 1
  let Pb : ℝ := Bsb R2 * (1 + A3 ^ 2) * W
  let Qb : ℝ := B0b R2 * (C3 * Lr) + B1b R2 * C2 +
    B1b R2 * A3 * C2 + B1b R2 + B1b R2 * A3
  let Ps : ℝ := Bss R2 * (1 + A3 ^ 2) * W
  let Qs : ℝ := B0s R2 * (C3 * Lr) + B1s R2 * C2 +
    B1s R2 * A3 * C2 + B1s R2 + B1s R2 * A3
  let Ebg : ℝ := 4 * (Pb ^ 2 + Qb ^ 2 + Ps ^ 2 + Qs ^ 2)
  let Kc : ℝ := Real.sqrt Ebg
  have hr0 : 0 ≤ r0 := le_max_right r 0
  have hR2 : 0 ≤ R2 := mul_nonneg hC2 hρ.le
  have hA3 : 0 ≤ A3 := mul_nonneg hC3 hr0
  have hLr : 0 ≤ Lr := by
    simp only [Lr]
    positivity
  have hEbg : 0 ≤ Ebg := by
    simp only [Ebg]
    positivity
  have hKc : 0 ≤ Kc := Real.sqrt_nonneg _
  have hKcsq : Kc ^ 2 = Ebg := Real.sq_sqrt hEbg
  refine ⟨Ca * Kc, mul_nonneg hCa hKc, ?_⟩
  intro T U hTr hUr
  let D : ℝ :=
    ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖
  let D2 : ℝ := C2 * D
  let D3 : ℝ := C3 * Lr * D
  let S : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ T
  let V : SmoothCcTensor g 0 2 := lowRadial (I := I) (M := M) g ρ U
  have hD : 0 ≤ D := norm_nonneg _
  have hD2 : 0 ≤ D2 := mul_nonneg hC2 hD
  have hD3 : 0 ≤ D3 := mul_nonneg (mul_nonneg hC3 hLr) hD
  have hTr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r0 :=
    hTr.trans (le_max_left r 0)
  have hUr0 : ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 :=
    hUr.trans (le_max_left r 0)
  have hSρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le T
  have hVρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ.le U
  have hSδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ := hreal S hSρ
  have hVδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g V) δ := hreal V hVρ
  have hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ :=
    zero_fb_refold (I := I) (M := M) g hδ0
  have hS2 : lowJetSq (I := I) (M := M) g 2 S ≤ R2 ^ 2 := by
    refine (hjet2 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSρ hC2) 2
  have hV2 : lowJetSq (I := I) (M := M) g 2 V ≤ R2 ^ 2 := by
    refine (hjet2 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVρ hC2) 2
  have hStop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)
    rw [lowRadialH3_core (I := I) (M := M) g hρ T] at hrad
    simpa only [S, ccToHsLin_apply] using hrad.trans hTr0
  have hVtop : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V‖ ≤ r0 := by
    have hrad := lowRadialH3_le (I := I) (M := M) g hρ
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [lowRadialH3_core (I := I) (M := M) g hρ U] at hrad
    simpa only [V, ccToHsLin_apply] using hrad.trans hUr0
  have hS3 : lowJetSq (I := I) (M := M) g 3 S ≤ A3 ^ 2 := by
    refine (hjet3 S).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hStop hC3) 2
  have hV3 : lowJetSq (I := I) (M := M) g 3 V ≤ A3 ^ 2 := by
    refine (hjet3 V).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hVtop hC3) 2
  have hincl :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ D := by
    have h := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2)
      (show (2 : ℝ) ≤ 3 by norm_num)
      (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U)
    rw [map_sub, LowRegBgC0Core.incl32_c0 (I := I) (M := M) g T,
      LowRegBgC0Core.incl32_c0 (I := I) (M := M) g U] at h
    simpa only [D, ccToHsLin_apply] using h
  have hSV2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤ D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V]
    exact (lowRadial_lip (I := I) (M := M) g hρ.le T U).trans hincl
  have hSV2j : lowJetSq (I := I) (M := M) g 2 (S - V) ≤ D2 ^ 2 := by
    refine (hjet2 (S - V)).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hC2 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV2 hC2) 2
  have hmax :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r0 := by
    simpa only [ccToHsLin_apply] using max_le hTr0 hUr0
  have hprod :
      max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ r0 * D :=
    mul_le_mul hmax hincl (norm_nonneg _) hr0
  have hSV3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V)‖ ≤
      Lr * D := by
    rw [show ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (S - V) =
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) V by
      simpa only [ccToHsLin_apply] using
        map_sub (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) S V]
    refine (lowRadial_h3_sub (I := I) (M := M) g hρ T U).trans ?_
    have hscaled := mul_le_mul_of_nonneg_left hprod
      ((one_div_pos.mpr hρ).le)
    have hscaled' :
        (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          (1 / ρ) * (r0 * D) := by
      calc
        _ = (1 / ρ) *
            (max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
                ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by ring
        _ ≤ (1 / ρ) * (r0 * D) := hscaled
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          (1 / ρ) *
            max ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
        D + (1 / ρ) * (r0 * D) := by
          change D + _ ≤ D + _
          exact add_le_add_right hscaled' D
      _ = Lr * D := by
        simp only [Lr]
        ring
  have hSV3j : lowJetSq (I := I) (M := M) g 3 (S - V) ≤ D3 ^ 2 := by
    refine (hjet3 (S - V)).trans ?_
    simpa only [D3, mul_assoc] using pow_le_pow_left₀
      (mul_nonneg hC3 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hSV3 hC3) 2
  have hbg := hb S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    R2 A3 D2 D3 D hR2 hA3 hD2 hD3 hD
    hS2 hV2 hS3 hV3 hSV2j hSV3j
    (hSρ.trans hρb') (hVρ.trans hρb') hSV2
  have hself := hs S V
    (lowRadial_symm (I := I) (M := M) g ρ T)
    (lowRadial_symm (I := I) (M := M) g ρ U)
    hδ_le hδ0 hSδ hVδ hZδ
    R2 A3 D2 D3 D hR2 hA3 hD2 hD3 hD
    hS2 hV2 hS3 hV3 hSV2j hSV3j
    (hSρ.trans hρs') (hVρ.trans hρs') hSV2
  have hbg' : lowJetSq (I := I) (M := M) g 2
      ((lowBaseData (I := I) (M := M) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C0 -
        (lowBaseData (I := I) (M := M) g gB V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).C0) ≤
      2 * (Pb ^ 2 + Qb ^ 2) * D ^ 2 := by
    refine hbg.trans (le_of_eq ?_)
    simp only [Pb, Qb, D2, D3, W]
    ring
  have hself' : lowJetSq (I := I) (M := M) g 2
      ((lowBaseData (I := I) (M := M) g g S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C0 -
        (lowBaseData (I := I) (M := M) g g V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).C0) ≤
      2 * (Ps ^ 2 + Qs ^ 2) * D ^ 2 := by
    refine hself.trans (le_of_eq ?_)
    simp only [Ps, Qs, D2, D3, W]
    ring
  let AT : LowBaseActionData g := deltaCoreBg (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal T
  let AU : LowBaseActionData g := deltaCoreBg (I := I) (M := M)
    g gB hρ.le hδ0 hδ_le hreal U
  have hsplit : AT.C0 - AU.C0 =
      ((lowBaseData (I := I) (M := M) g gB S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C0 -
        (lowBaseData (I := I) (M := M) g gB V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).C0) -
      ((lowBaseData (I := I) (M := M) g g S
          (lt_of_le_of_lt hδ_le (by norm_num)) hSδ hZδ).C0 -
        (lowBaseData (I := I) (M := M) g g V
          (lt_of_le_of_lt hδ_le (by norm_num)) hVδ hZδ).C0) := by
    simp only [AT, AU, deltaCoreBg, lowCoreDataBg, S, V]
    abel
  have hcoeff :
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) +
        lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤ (Kc * D) ^ 2 := by
    have hC1 : lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) = 0 := by
      simp only [AT, AU, deltaCoreBg, sub_self]
      exact lowJetZ (I := I) (M := M) g 3 2 2
    rw [hC1, add_zero, hsplit]
    refine (jetSub (I := I) (M := M) g 2 _ _).trans ?_
    have hsum := add_le_add hbg' hself'
    calc
      2 * (lowJetSq (I := I) (M := M) g 2 _ +
          lowJetSq (I := I) (M := M) g 2 _) ≤
          2 * (2 * (Pb ^ 2 + Qb ^ 2) * D ^ 2 +
            2 * (Ps ^ 2 + Qs ^ 2) * D ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = Ebg * D ^ 2 := by
        simp only [Ebg]
        ring
      _ = (Kc * D) ^ 2 := by
        rw [show (Kc * D) ^ 2 = Kc ^ 2 * D ^ 2 by ring, hKcsq]
  have hout := hact AT AU (Kc * D) (mul_nonneg hKc hD) hcoeff
  refine ⟨?_, ?_⟩
  · calc
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
          Ca * (Kc * D) := hout.1
      _ = Ca * Kc * D := by ring
  · calc
      ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
          Ca * (Kc * D) := hout.2
      _ = Ca * Kc * D := by ring

/-- **The trajectory-free affine packet of the order-zero background
correction**, i.e. the producer of `BgDeltaPack g gB`.

On every coefficient radius `ρ ≤ ρ₀` the correction supplies a pair of completed
action maps on the two adjacent scales, continuous, realizing `deltaCoreBg`'s
completed actions on smooth data, with a common affine growth certificate
`‖G x‖ ≤ Z + L‖x‖` and the Sobolev-inclusion square.

The affine certificate is `c0bg_aff`, resting on the tame background-difference
envelope `c0Bg_diff_tame`; the Lipschitz certificate needed to extend off the
smooth core is `c0bg_pair`; the square is the density limit of `a1_comm`, which
holds for every action bundle.  Together with `refold_aff_bg` this makes
`bgA1_of_refold` — the first-order half of the fixed-background lift —
unconditional. -/
theorem c0bg_pack
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    BgDeltaPack (I := I) (M := M) g gB := by
  obtain ⟨ρp, hρp, hpair⟩ := c0bg_pair (I := I) (M := M) hDim g gB
  obtain ⟨ρa, hρa, haff⟩ := c0bg_aff (I := I) (M := M) hDim g gB
  let ρ0 : ℝ := min ρp ρa
  have hρ0 : 0 < ρ0 := lt_min hρp hρa
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ δ hρ hρρ0 hδ0 hδ_le hreal
  have hρp' : ρ ≤ ρp := hρρ0.trans (min_le_left _ _)
  have hρa' : ρ ≤ ρa := hρρ0.trans (min_le_right _ _)
  obtain ⟨Z, L, hZ, hL, hbd⟩ :=
    haff hρ hρa' hδ0 hδ_le hreal
  let fHi : SmoothCcTensor g 0 2 →
      (metricH3 (I := I) (M := M) g →L[ℝ]
        metricH2 (I := I) (M := M) g) := fun T =>
    (deltaCoreBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T).a1Hi (I := I) (M := M)
  let fLo : SmoothCcTensor g 0 2 →
      (metricH2 (I := I) (M := M) g →L[ℝ]
        metricH1 (I := I) (M := M) g) := fun T =>
    (deltaCoreBg (I := I) (M := M)
      g gB hρ.le hδ0 hδ_le hreal T).a1Lo (I := I) (M := M)
  have hpairHi : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fHi T - fHi U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fHi] using (hK T U hT hU).1
  have hpairLo : ∀ r : ℝ, ∃ K : ℝ,
      ∀ T U : SmoothCcTensor g 0 2,
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ r →
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ ≤ r →
        ‖fLo T - fLo U‖ ≤ K *
          ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T -
            ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    intro r
    obtain ⟨K, _, hK⟩ := hpair hρ hρp' hδ0 hδ_le hreal r
    refine ⟨K, ?_⟩
    intro T U hT hU
    simpa only [fLo] using (hK T U hT hU).2
  have hbdHi : ∀ T : SmoothCcTensor g 0 2,
      ‖fHi T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fHi] using (hbd T).1
  have hbdLo : ∀ T : SmoothCcTensor g 0 2,
      ‖fLo T‖ ≤ Z + L *
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
    intro T
    simpa only [fLo] using (hbd T).2
  have hΦ : Continuous (fun x : ℝ => Z + L * x) := by
    fun_prop
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  obtain ⟨GHi, hGHi, hGHiCore, hGHiBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fHi hΦ hpairHi hbdHi
  obtain ⟨GLo, hGLo, hGLoCore, hGLoBd⟩ :=
    DifferentialGeometry.Analysis.exists_extend_le
      (j := ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
      hdense fLo hΦ hpairLo hbdLo
  have hleft : Continuous (fun x : metricH3 (I := I) (M := M) g =>
      (incl12 (I := I) (M := M) g).comp (GHi x)) :=
    (ContinuousLinearMap.compL ℝ
      (metricH3 (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (continuous_const.prodMk hGHi)
  have hright : Continuous (fun x : metricH3 (I := I) (M := M) g =>
      (GLo x).comp (incl32 (I := I) (M := M) g)) :=
    (ContinuousLinearMap.compL ℝ
      (metricH3 (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂.comp
        (hGLo.prodMk continuous_const)
  have hcomm : ∀ x : metricH3 (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp (GHi x) =
        (GLo x).comp (incl32 (I := I) (M := M) g) := by
    intro x
    refine hdense.induction_on x (isClosed_eq hleft hright) ?_
    intro T
    rw [hGHiCore T, hGLoCore T]
    simpa only [incl12, incl32] using
      a1_comm (I := I) (M := M) hDim g
        (deltaCoreBg (I := I) (M := M)
          g gB hρ.le hδ0 hδ_le hreal T)
  exact ⟨Z, L, hZ, hL, GHi, GLo, hGHi, hGLo,
    hGHiCore, hGLoCore, hGHiBd, hGLoBd, hcomm⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
