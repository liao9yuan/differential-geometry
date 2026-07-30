import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFlowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitBuild
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CurvTowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SourceCovLip
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SourceCovLipAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldEndgame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.OpenWindowEquiv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.NoncollapseInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDCanonP4
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessUncondH6
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonPositiveRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Adapter To The Hamilton Positive Ricci Endpoint

This file connects the concrete HCG compactness data to the Section 12 API in
`DimensionThree/HamiltonPositiveRicci.lean`.  The endpoint record now retains
the genuine comparison maps, composed subsequence, source identifications, and
all-time limit completeness; this adapter packages those fields without
inventing a desired-conclusion lift.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Bundle
open DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

private theorem srm_eq_of_inner
    {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

/-- The fixed closed backward interval used by the Hamilton blow-up sequence. -/
private def ham3CommonD :
    DifferentialGeometry.Integral.Connection.RealTimeInterval :=
  DifferentialGeometry.Integral.Connection.RealTimeInterval.closed
    (-(ham3_r0 ^ 2)) 0 (neg_nonpos.mpr (sq_nonneg ham3_r0))

/-- Strictly earlier left endpoint used to run the compact Shi estimate. -/
private def ham3ShiLeft : Real :=
  -(2 * ham3_r0 ^ 2)

/-- First index supplied by the fixed-window hypothesis. -/
private noncomputable def ham3WinStart
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) : Nat :=
  Classical.choose hwindow

/-- First index after which the selected rescalings contain a strict left
buffer for the fixed Hamilton window. -/
private noncomputable def ham3BufStart
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q) : Nat :=
  Classical.choose (hsel.2.2.2.1 (2 * ham3_r0 ^ 2))

/-- Canonical source start retaining both the requested window and its Shi
buffer. -/
private noncomputable def ham3Start
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) : Nat :=
  max (ham3WinStart (I := I) P Q hwindow) (ham3BufStart (I := I) P Q hsel)

private theorem ham3Start_spec
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    ∀ i : Nat, ham3Start (I := I) P Q hsel hwindow ≤ i →
      ∀ s : Real, -(ham3_r0 ^ 2) ≤ s → s ≤ 0 →
        -(ham3BlowupScale (I := I) P Q i * Q.time i) ≤ s ∧ s ≤ 0 :=
  fun i hi s hs h0 =>
    Classical.choose_spec hwindow i
      (le_trans (Nat.le_max_left _ _) hi) s hs h0

private theorem ham3Buf_spec
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    ∀ i : Nat, ham3Start (I := I) P Q hsel hwindow ≤ i →
      2 * ham3_r0 ^ 2 ≤
        ham3BlowupScale (I := I) P Q i * Q.time i :=
  fun i hi =>
    Classical.choose_spec (hsel.2.2.2.1 (2 * ham3_r0 ^ 2)) i
      (le_trans (Nat.le_max_right _ _) hi)

private theorem ham3_car_subset
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (i : Nat) :
    ham3CommonD.carrier ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (ham3Start (I := I) P Q hsel hwindow + i))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (ham3Start (I := I) P Q hsel hwindow + i))).carrier := by
  intro s hs
  change s ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 at hs
  let j := ham3Start (I := I) P Q hsel hwindow + i
  have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
  have hw :=
    ham3Start_spec (I := I) P Q hsel hwindow j hj s hs.1 hs.2
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_carrier]
  change ham3RescaledTime (I := I) P Q j s ∈ P.D.carrier
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hnum : 0 ≤ ham3BlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hw.1]
  have hlo : 0 ≤ ham3RescaledTime (I := I) P Q j s := by
    rw [show ham3RescaledTime (I := I) P Q j s =
        (ham3BlowupScale (I := I) P Q j * Q.time j + s) /
          ham3BlowupScale (I := I) P Q j by
      unfold ham3RescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_nonneg hnum hscale.le
  have hsdiv : s / ham3BlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hw.2 hscale.le
  have hhi : ham3RescaledTime (I := I) P Q j s < omega := by
    unfold ham3RescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

private theorem ham3_reg_subset
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (i : Nat) :
    ham3CommonD.regular ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (ham3Start (I := I) P Q hsel hwindow + i))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1 (ham3Start (I := I) P Q hsel hwindow + i))).regular := by
  intro s hs
  change s ∈ Set.Ioo (-(ham3_r0 ^ 2)) 0 at hs
  let j := ham3Start (I := I) P Q hsel hwindow + i
  have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
  have hw0 :=
    ham3Start_spec (I := I) P Q hsel hwindow j hj (-(ham3_r0 ^ 2))
      le_rfl (neg_nonpos.mpr (sq_nonneg ham3_r0))
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_regular]
  change ham3RescaledTime (I := I) P Q j s ∈ P.D.regular
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hnum : 0 < ham3BlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hw0.1, hs.1]
  have hlo : 0 < ham3RescaledTime (I := I) P Q j s := by
    rw [show ham3RescaledTime (I := I) P Q j s =
        (ham3BlowupScale (I := I) P Q j * Q.time j + s) /
          ham3BlowupScale (I := I) P Q j by
      unfold ham3RescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_pos hnum hscale
  have hsdiv : s / ham3BlowupScale (I := I) P Q j < 0 :=
    div_neg_of_neg_of_pos hs.2 hscale
  have hhi : ham3RescaledTime (I := I) P Q j s < omega := by
    unfold ham3RescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

private theorem ham3_shi_car
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (i : Nat) :
    Set.Icc ham3ShiLeft 0 ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (ham3Start (I := I) P Q hsel hwindow + i))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1
          (ham3Start (I := I) P Q hsel hwindow + i))).carrier := by
  intro s hs
  let j := ham3Start (I := I) P Q hsel hwindow + i
  have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
  have hbuf := ham3Buf_spec (I := I) P Q hsel hwindow j hj
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_carrier]
  change ham3RescaledTime (I := I) P Q j s ∈ P.D.carrier
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hsleft : -(2 * ham3_r0 ^ 2) ≤ s := by
    simpa only [ham3ShiLeft] using hs.1
  have hnum : 0 ≤ ham3BlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hsleft]
  have hlo : 0 ≤ ham3RescaledTime (I := I) P Q j s := by
    rw [show ham3RescaledTime (I := I) P Q j s =
        (ham3BlowupScale (I := I) P Q j * Q.time j + s) /
          ham3BlowupScale (I := I) P Q j by
      unfold ham3RescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_nonneg hnum hscale.le
  have hsdiv : s / ham3BlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 hscale.le
  have hhi : ham3RescaledTime (I := I) P Q j s < omega := by
    unfold ham3RescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

private theorem ham3_shi_reg
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (i : Nat) :
    Set.Ioc ham3ShiLeft 0 ⊆
      (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (ham3Start (I := I) P Q hsel hwindow + i))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + i))
        (hsel.2.2.1
          (ham3Start (I := I) P Q hsel hwindow + i))).regular := by
  intro s hs
  let j := ham3Start (I := I) P Q hsel hwindow + i
  have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
  have hbuf := ham3Buf_spec (I := I) P Q hsel hwindow j hj
  rw [DifferentialGeometry.PDE.RicciFlow.paraInterval_regular]
  change ham3RescaledTime (I := I) P Q j s ∈ P.D.regular
  rw [hD]
  have hscale := hsel.1 j
  have htimeMem := hsel.2.2.1 j
  rw [hD] at htimeMem
  have hsleft : -(2 * ham3_r0 ^ 2) < s := by
    simpa only [ham3ShiLeft] using hs.1
  have hnum : 0 < ham3BlowupScale (I := I) P Q j * Q.time j + s := by
    linarith [hsleft]
  have hlo : 0 < ham3RescaledTime (I := I) P Q j s := by
    rw [show ham3RescaledTime (I := I) P Q j s =
        (ham3BlowupScale (I := I) P Q j * Q.time j + s) /
          ham3BlowupScale (I := I) P Q j by
      unfold ham3RescaledTime
      field_simp [ne_of_gt hscale]]
    exact div_pos hnum hscale
  have hsdiv : s / ham3BlowupScale (I := I) P Q j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 hscale.le
  have hhi : ham3RescaledTime (I := I) P Q j s < omega := by
    unfold ham3RescaledTime
    linarith [htimeMem.2, hsdiv]
  exact ⟨hlo, hhi⟩

private theorem ham3_shi_rm
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hrm : Ham3RmBound (I := I) P Q)
    (i : Nat) :
    ∀ s ∈ Set.Icc ham3ShiLeft 0, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I)
          ((ham3RescaledSol (I := I) P Q hsel
            (ham3Start (I := I) P Q hsel hwindow + i)).base.metric s) x 4
          ((ham3RescaledSol (I := I) P Q hsel
            (ham3Start (I := I) P Q hsel hwindow + i)).base.rm04 s x) ≤
        (100 : Real) ^ 2 := by
  intro s hs x
  let j := ham3Start (I := I) P Q hsel hwindow + i
  have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
    simpa only [j] using
      Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
  have hbuf := ham3Buf_spec (I := I) P Q hsel hwindow j hj
  have hsleft : -(2 * ham3_r0 ^ 2) ≤ s := by
    simpa only [ham3ShiLeft] using hs.1
  have hleft :
      -(ham3BlowupScale (I := I) P Q j * Q.time j) ≤ s := by
    linarith
  have hold := hrm j s x hleft hs.2
  have hold' :
      Tensor0SBundle.normSq0S (I := I)
          (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (ham3BlowupScale (I := I) P Q j) s)) x 4
          (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (ham3BlowupScale (I := I) P Q j) s) x) ≤
        (100 : Real) ^ 2 *
          (ham3BlowupScale (I := I) P Q j) ^ 2 := by
    simpa [ham3RmNormSq, ham3Solution, ham3RescaledTime] using hold
  have hscale := hsel.1 j
  have hmul := mul_le_mul_of_nonneg_left hold'
    (sq_nonneg (ham3BlowupScale (I := I) P Q j)⁻¹)
  change Tensor0SBundle.normSq0S (I := I)
      ((ham3RescaledSol (I := I) P Q hsel j).base.metric s) x 4
      ((ham3RescaledSol (I := I) P Q hsel j).base.rm04 s x) ≤
    (100 : Real) ^ 2
  unfold ham3RescaledSol
  rw [DifferentialGeometry.PDE.RicciFlow.paraRmNormSq]
  calc
    (ham3BlowupScale (I := I) P Q j)⁻¹ ^ 2 *
        Tensor0SBundle.normSq0S (I := I)
          (P.S.base.metric (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (ham3BlowupScale (I := I) P Q j) s)) x 4
          (P.S.base.rm04 (DifferentialGeometry.PDE.RicciFlow.paraTime
            (Q.time j) (ham3BlowupScale (I := I) P Q j) s) x) ≤
      (ham3BlowupScale (I := I) P Q j)⁻¹ ^ 2 *
        ((100 : Real) ^ 2 *
          (ham3BlowupScale (I := I) P Q j) ^ 2) := hmul
    _ = (100 : Real) ^ 2 := by
      field_simp [ne_of_gt hscale]

/-- Every canonical Hamilton source member has scale-one curvature control on
any positive subradius of the fixed common-window radius. -/
private theorem ham3_ball_rm
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hrm : Ham3RmBound (I := I) P Q)
    {r : Real} (hr : 0 < r) (hrle : r ≤ ham3_r0)
    (i : Nat) :
    (ham3RescaledBall (I := I) P Q hsel
      (ham3Start (I := I) P Q hsel hwindow + i) r hr).IsRmControlled := by
  let j := ham3Start (I := I) P Q hsel hwindow + i
  let B := ham3RescaledBall (I := I) P Q hsel j r hr
  change B.IsRmControlled
  unfold PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled
  dsimp only [B, ham3RescaledBall, ham3RescaledZero]
  have hrsq : r ^ 2 ≤ ham3_r0 ^ 2 := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hrle)
        (add_nonneg hr.le ham3_r0_pos.le)]
  constructor
  · intro t ht
    apply ham3_shi_car (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [ham3ShiLeft]
    nlinarith [ht.1, hrsq, sq_nonneg ham3_r0]
  · intro t ht x _hx
    have htShi : t ∈ Set.Icc ham3ShiLeft 0 := by
      refine ⟨?_, ht.2⟩
      dsimp only [ham3ShiLeft]
      nlinarith [ht.1, hrsq, sq_nonneg ham3_r0]
    have hsq :=
      ham3_shi_rm (I := I) P Q hsel hwindow hrm i t htShi x
    change r ^ 4 *
        Tensor0SBundle.normSq0S (I := I)
          ((ham3RescaledSol (I := I) P Q hsel j).base.metric t) x 4
          ((ham3RescaledSol (I := I) P Q hsel j).base.rm04 t x) ≤ 1
    have hmul :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le 4)
    calc
      r ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              ((ham3RescaledSol (I := I) P Q hsel j).base.metric t) x 4
              ((ham3RescaledSol (I := I) P Q hsel j).base.rm04 t x)
          ≤ r ^ 4 * (100 : Real) ^ 2 := hmul
      _ ≤ ham3_r0 ^ 4 * (100 : Real) ^ 2 := by
        gcongr
      _ = 1 := by
        norm_num [ham3_r0]

/-- The buffered Hamilton rescalings admit one time-zero metric-equivalence
factor and one finite majorant on the full closed common window. -/
private theorem ham3_win_equiv
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hrm : Ham3RmBound (I := I) P Q) :
    ∃ A Bmax : Real, 0 ≤ A ∧ 1 ≤ Bmax ∧
      (∀ t : Real, t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
        metricEquivalenceFactor 1 A t 0 ≤ Bmax) ∧
      ∀ i : Nat,
        MetricUniformEquivalentOnWindow (I := I) Set.univ
          (-(ham3_r0 ^ 2)) 0
          ((ham3RescaledSol (I := I) P Q hsel
            (ham3Start (I := I) P Q hsel hwindow + i)).family.metric 0)
          (fun _ t ↦
            (ham3RescaledSol (I := I) P Q hsel
              (ham3Start (I := I) P Q hsel hwindow + i)).family.metric t)
          (fun t ↦ metricEquivalenceFactor 1 A t 0) := by
  let C : Real := (100 : Real) ^ 2
  let A : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt C
  let timeRadius : Real := ham3_r0 ^ 2
  let Bmax : Real := Real.exp (2 * A * timeRadius)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hRadius : 0 ≤ timeRadius := by
    dsimp only [timeRadius]
    positivity
  have hBmax : 1 ≤ Bmax := by
    dsimp only [Bmax]
    exact Real.one_le_exp
      (mul_nonneg (mul_nonneg (by norm_num) hA) hRadius)
  have habs : ∀ t : Real, t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
      |t| ≤ timeRadius := by
    intro t ht
    rw [abs_of_nonpos ht.2]
    dsimp only [timeRadius]
    nlinarith [ht.1]
  have hB : ∀ t : Real, t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
      metricEquivalenceFactor 1 A t 0 ≤ Bmax := by
    intro t ht
    rw [metricEquivalenceFactor]
    simp only [one_mul, sub_zero]
    dsimp only [Bmax]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (habs t ht)
      (mul_nonneg (by norm_num) hA)
  refine ⟨A, Bmax, hA, hBmax, hB, ?_⟩
  intro i
  let j := ham3Start (I := I) P Q hsel hwindow + i
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j) (ham3BlowupScale (I := I) P Q j)
    (hsel.1 j) (hsel.2.2.1 j)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw :=
    ham3RescaledSol (I := I) P Q hsel j
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
      (I := I) Sraw := by
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j)
      (ham3BlowupScale (I := I) P Q j)
      (hsel.1 j) (hsel.2.2.1 j)
  let Sseq : Nat → DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw := fun _ ↦ Sraw
  have hSseq : ∀ n : Nat,
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) (Sseq n) :=
    fun _ ↦ hraw
  have hcarrier : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ Draw.carrier := by
    intro t ht
    apply ham3_shi_car (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [ham3ShiLeft]
    nlinarith [sq_pos_of_pos ham3_r0_pos, ht.1]
  have hregular : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ Draw.regular := by
    intro t ht
    apply ham3_shi_reg (I := I) h0omega P hD Q hsel hwindow i
    refine ⟨?_, ht.2⟩
    dsimp only [ham3ShiLeft]
    nlinarith [sq_pos_of_pos ham3_r0_pos, ht.1]
  have hquad :=
    DifferentialGeometry.Integral.Connection.twoTensorQuadBound_of_solutions
      (I := I)
    Sseq Set.univ (-(ham3_r0 ^ 2)) 0 C hC hcarrier
    (fun _ t ht x _hx ↦ by
      simpa only [Sseq, Sraw, C, j] using
        ham3_shi_rm (I := I) P Q hsel hwindow hrm i t
          (by
            refine ⟨?_, ht.2⟩
            dsimp only [ham3ShiLeft]
            nlinarith [sq_pos_of_pos ham3_r0_pos, ht.1])
          x)
  have hequiv0 : ∀ n : Nat,
      MetricUniformEquivalentOn (I := I) Set.univ
        (Sraw.family.metric 0) ((Sseq n).family.metric 0) 1 := by
    intro n
    refine ⟨le_rfl, ?_⟩
    intro x _hx v
    simp only [Sseq, inv_one, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hzero : (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 :=
    ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  have hequiv :=
    metricUniformEquivalentOnWindow_of_solutions' (I := I)
      Sseq hSseq Set.univ (-(ham3_r0 ^ 2)) 0 0 1 A
      (Sraw.family.metric 0) hregular hzero le_rfl hA hequiv0 hquad.2
  simpa only [Sseq, Sraw, j] using hequiv

/-- The same buffered Hamilton rescalings satisfy one complete-Shi envelope,
chosen before the sequence index, on the full closed common window. -/
private theorem ham3_win_shi
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hrm : Ham3RmBound (I := I) P Q) :
    ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ i : Nat,
        MovingShiBoundOn (I := I) Set.univ
          (-(ham3_r0 ^ 2)) 0
          (fun _ t ↦
            (ham3RescaledSol (I := I) P Q hsel
              (ham3Start (I := I) P Q hsel hwindow + i)).family.metric t)
          N KShi := by
  letI : CompactSpace M := hcompact
  intro N
  let KShi : Real :=
    shiOpenConst (Module.finrank Real E) ((100 : Real) ^ 2)
      ham3ShiLeft (-(ham3_r0 ^ 2)) 0 N
  refine ⟨KShi, shiOpenConst_nonneg _ _ _ _ _ _, ?_⟩
  intro i
  let j := ham3Start (I := I) P Q hsel hwindow + i
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j) (ham3BlowupScale (I := I) P Q j)
    (hsel.1 j) (hsel.2.2.1 j)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw :=
    ham3RescaledSol (I := I) P Q hsel j
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
      (I := I) Sraw := by
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j)
      (ham3BlowupScale (I := I) P Q j)
      (hsel.1 j) (hsel.2.2.1 j)
  let Fraw : PointedFlowData (I := I) Draw :=
    { M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Q.point j
      S := Sraw
      isSolution := hraw }
  have hcomplete :
      MetricComplete (I := I) (Fraw.atTime (I := I) ham3ShiLeft) := by
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact Fraw.M ?_ ?_
    simpa only [Fraw] using hcompact
  have halphaBeta : ham3ShiLeft < -(ham3_r0 ^ 2) := by
    dsimp only [ham3ShiLeft]
    nlinarith [sq_pos_of_pos ham3_r0_pos]
  have hbetaZero : -(ham3_r0 ^ 2) ≤ (0 : Real) :=
    neg_nonpos.mpr (sq_nonneg ham3_r0)
  have hShi := movingShi_of_bound (I := I) Fraw
    halphaBeta hbetaZero
    (ham3_shi_car (I := I) h0omega P hD Q hsel hwindow i)
    (ham3_shi_reg (I := I) h0omega P hD Q hsel hwindow i)
    hcomplete (by positivity : (0 : Real) ≤ (100 : Real) ^ 2)
    (by
      intro t ht x
      change Tensor0SBundle.normSq0S (I := I)
          (Sraw.family.metric t) x 4 (Sraw.base.rm04 t x) ≤
        (100 : Real) ^ 2
      simpa only [Sraw, j] using
        ham3_shi_rm (I := I) P Q hsel hwindow hrm i t ht x)
    N
  simpa only [Fraw, Sraw, j, KShi] using hShi

/-- The actual tail of selected Hamilton rescalings, restricted to one common
closed backward time interval. -/
noncomputable def ham3SourceSeq
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ham3CommonD
  term := fun i =>
    { M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := Q.point (ham3Start (I := I) P Q hsel hwindow + i)
      S :=
        (ham3RescaledSol (I := I) P Q hsel
          (ham3Start (I := I) P Q hsel hwindow + i)).timeRestrict ham3CommonD
      isSolution :=
        DifferentialGeometry.PDE.RicciFlow.isSoln_timeRestrict (I := I)
          (DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
            P.isSmooth.isSolution
            (Q.time (ham3Start (I := I) P Q hsel hwindow + i))
            (ham3BlowupScale (I := I) P Q
              (ham3Start (I := I) P Q hsel hwindow + i))
            (hsel.1 (ham3Start (I := I) P Q hsel hwindow + i))
            (hsel.2.2.1 (ham3Start (I := I) P Q hsel hwindow + i)))
          (ham3_car_subset (I := I) h0omega P hD Q hsel hwindow i)
          (ham3_reg_subset (I := I) h0omega P hD Q hsel hwindow i) }

@[simp] theorem sourceSeq_carrier
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier =
      Set.Icc (-(ham3_r0 ^ 2)) 0 := by
  rfl

@[simp] theorem sourceSeq_regular
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.regular =
      Set.Ioo (-(ham3_r0 ^ 2)) 0 := by
  rfl

/-- Curvature control on a raw selected rescaling descends to the same
time-zero ball in the canonical common-window source. -/
private theorem ham3_src_rm
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hrm : Ham3RmBound (I := I) P Q)
    {r : Real} (hr : 0 < r) (hrle : r ≤ ham3_r0)
    (i : Nat) :
    let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
    let hzero : (0 : Real) ∈ X.D.carrier := by
      change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
      exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      hzero r hr).IsRmControlled := by
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  let hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  letI : TopologicalSpace (X.term i).M := (X.term i).topology
  letI : ChartedSpace H (X.term i).M := (X.term i).charted
  letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
  letI : IsManifold I 1 (X.term i).M :=
    IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
    change IsManifold I ∞ (X.term i).M
    infer_instance
  letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
  letI : T2Space (X.term i).M := (X.term i).t2
  let B := PointedFlowData.baseFlowBall (I := I) (X.term i)
    hzero r hr
  change B.IsRmControlled
  unfold PDE.RicciFlow.Perelman.FlowMetricBall.IsRmControlled
  have hrsq : r ^ 2 ≤ ham3_r0 ^ 2 := by
    nlinarith
      [mul_nonneg (sub_nonneg.mpr hrle)
        (add_nonneg hr.le ham3_r0_pos.le)]
  constructor
  · intro t ht
    have ht' : t ∈ Set.Icc ((0 : Real) - r ^ 2) 0 := by
      simpa only [B, PointedFlowData.baseFlowBall] using ht
    change t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨by linarith [ht'.1, hrsq], ht'.2⟩
  · intro t ht x _hx
    have ht' : t ∈ Set.Icc ((0 : Real) - r ^ 2) 0 := by
      simpa only [B, PointedFlowData.baseFlowBall] using ht
    let j := ham3Start (I := I) P Q hsel hwindow + i
    have htShi : t ∈ Set.Icc ham3ShiLeft 0 := by
      refine ⟨?_, ht'.2⟩
      dsimp only [ham3ShiLeft]
      linarith [ht'.1, hrsq, sq_nonneg ham3_r0]
    have hsq :=
      ham3_shi_rm (I := I) P Q hsel hwindow hrm i t htShi x
    change r ^ 4 *
        Tensor0SBundle.normSq0S (I := I)
          ((ham3RescaledSol (I := I) P Q hsel j).base.metric t) x 4
          ((ham3RescaledSol (I := I) P Q hsel j).base.rm04 t x) ≤ 1
    have hmul :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le 4)
    calc
      r ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              ((ham3RescaledSol (I := I) P Q hsel j).base.metric t) x 4
              ((ham3RescaledSol (I := I) P Q hsel j).base.rm04 t x)
          ≤ r ^ 4 * (100 : Real) ^ 2 := hmul
      _ ≤ ham3_r0 ^ 4 * (100 : Real) ^ 2 := by
        gcongr
      _ = 1 := by
        norm_num [ham3_r0]

/-- Every finite spatial chart jet of a Hamilton blow-up stage is jointly
continuous on the canonical closed window.  The proof uses the untruncated
rescaled solution as the regular ambient flow, while the CGH source term
remains the canonical closed-window restriction. -/
theorem ham3_stage_jet
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (k r : Nat) (x₀ : P₀.M) (i j : Fin (Module.finrank Real E))
    {C : Set E}
    (hCtarget : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      C ⊆ (extChartAt I x₀).target)
    (hCgrow : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      (extChartAt I x₀).symm '' C ⊆ bf.grow k) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ContinuousOn
      (fun p : Real × E =>
        iteratedFDeriv Real r
          (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
            (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j) p.2)
      (Set.Icc (-(ham3_r0 ^ 2)) 0 ×ˢ C) := by
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  change PointedCGHMaps (I := I) X P₀ subseq at Φ
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) :=
    sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  letI : T2Space ↥(targetOpen (I := I) Φ k) :=
    targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k))
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) :=
    targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) :=
    targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) :=
    targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) :=
    targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let j₀ := ham3Start (I := I) P Q hsel hwindow + subseq k
  let Draw := DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
    (Q.time j₀) (ham3BlowupScale (I := I) P Q j₀)
    (hsel.1 j₀) (hsel.2.2.1 j₀)
  let Sraw : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := (X.term (subseq k)).M) Draw := by
    change DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) Draw
    exact ham3RescaledSol (I := I) P Q hsel j₀
  have hraw : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) Sraw := by
    change DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
      (ham3RescaledSol (I := I) P Q hsel j₀)
    exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
      P.isSmooth.isSolution (Q.time j₀)
      (ham3BlowupScale (I := I) P Q j₀)
      (hsel.1 j₀) (hsel.2.2.1 j₀)
  let S := DifferentialGeometry.PDE.RicciFlow.solutionOn_pullback (I := I)
    (solutionOn_restrictOpen (I := I) Sraw (targetOpen (I := I) Φ k))
    (sourceTargetDiff (I := I) Φ k)
  have hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S := by
    exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) Sraw (targetOpen (I := I) Φ k))
      (isSolutionOn_restrictOpen (I := I) Sraw hraw
        (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)
  have hreg : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆
      Draw.regular := by
    intro t ht
    apply ham3_shi_reg (I := I) h0omega P hD Q hsel hwindow (subseq k)
    refine ⟨?_, ht.2⟩
    dsimp only [ham3ShiLeft]
    have htleft := ht.1
    nlinarith [sq_pos_of_pos ham3_r0_pos]
  apply ConvOut.gSeqJet_of_soln (Φ := Φ) (R := R) (bf := bf)
    (hsrc := hsrc) (htgt := htgt) k S hS hreg
  · intro t x v w
    rfl
  · exact hCtarget
  · exact hCgrow

/-- Every finite spatial chart jet of the Hamilton limit metric is jointly
continuous on the canonical closed window. -/
theorem ham3_limit_jets
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(ham3_r0 ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ∀ (r : Nat) (x₀ : P₀.M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × E =>
          iteratedFDeriv Real r
            (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE
              (I := I) (co.gInf p.1) x₀ i j) p.2)
        (Set.Icc (-(ham3_r0 ^ 2)) 0 ×ˢ
          interior (extChartAt I x₀).target) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  apply ConvOut.gramJets_of_stage (I := I) (Φ := Φ) co
  intro r x₀ i j C hCc hCtgt
  let K : Set P₀.M := (extChartAt I x₀).symm '' C
  have hKc : IsCompact K := by
    dsimp only [K]
    exact hCc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) x₀).mono hCtgt)
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hKc
  filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
  apply ham3_stage_jet (I := I) h0omega P hD Q hsel hwindow Φ
    (co.φ k) r x₀ i j hCtgt
  simpa only [K] using hkgrow (co.φ k) (hk.trans (co.hφ.id_le k))

/-- The Hamilton limit chart-Gram entries are jointly smooth on the full
canonical closed time window. -/
theorem ham3_gram_smooth
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(ham3_r0 ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    ∀ (x₀ : P₀.M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × P₀.M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix
            (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Icc (-(ham3_r0 ^ 2)) 0 ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  apply ConvOut.gramSmoothIcc (I := I) (Φ := Φ)
    (neg_lt_zero.mpr (sq_pos_of_pos ham3_r0_pos))
  · exact Set.Subset.rfl
  · exact Set.Subset.rfl
  · exact ham3_limit_jets (I := I) h0omega P hD Q hsel hwindow Φ co

/-- The Hamilton CGH limit metric is a genuine Ricci-flow solution on the full
canonical closed common window. -/
theorem ham3_limit_soln
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    {R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (co : ConvOut (I := I) Φ R bf hsrc htgt (-(ham3_r0 ^ 2)) 0) :
    letI : TopologicalSpace P₀.M := P₀.topology
    letI : ChartedSpace H P₀.M := P₀.charted
    letI : T2Space P₀.M := P₀.t2
    letI : IsManifold I ∞ P₀.M := P₀.smooth
    letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
    DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
      ({ base := { metric := co.gInf } } :
        DifferentialGeometry.PDE.RicciFlow.SolutionOn
          (I := I) (M := P₀.M)
          (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D) := by
  letI : TopologicalSpace P₀.M := P₀.topology
  letI : ChartedSpace H P₀.M := P₀.charted
  letI : T2Space P₀.M := P₀.t2
  letI : IsManifold I ∞ P₀.M := P₀.smooth
  letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
  let J : Set Real := Set.Icc (-(ham3_r0 ^ 2)) 0
  have hJlt : -(ham3_r0 ^ 2) < (0 : Real) :=
    neg_lt_zero.mpr (sq_pos_of_pos ham3_r0_pos)
  have hJ : UniqueDiffOn Real J := by
    simpa only [J] using uniqueDiffOn_Icc hJlt
  have hcarrier :
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier = J := by
    simpa only [J] using sourceSeq_carrier (I := I) h0omega P hD Q hsel hwindow
  have hcarrierSub :
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier ⊆ J := by
    simpa only [hcarrier] using (Set.Subset.rfl : J ⊆ J)
  have hjoint := ham3_gram_smooth (I := I) h0omega P hD Q hsel hwindow Φ co
  have hsmooth :=
    ConvOut.metricSmooth (I := I) (Φ := Φ) hcarrier co
  have hpde : ∀ t ∈
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.regular,
      ∀ (x : P₀.M) (v w : TangentSpace I x),
        HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
          ((-2 : Real) *
            DifferentialGeometry.Integral.Connection.ricciTensor
              (I := I) (co.gInf t) x v w) t := by
    intro t ht x v w
    exact ConvOut.metricPDE_regular (I := I) (Φ := Φ)
      hcarrierSub co ht x v w
  have hscalarCont :
      ContinuousOn
        (fun q : Real × P₀.M =>
          DifferentialGeometry.Integral.Connection.metricScalarAt
            (I := I) (co.gInf q.1) q.2)
        ((ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier ×ˢ
          (Set.univ : Set P₀.M)) := by
    simpa only [hcarrier, J] using
      DifferentialGeometry.PDE.RicciFlow.scalarCont_of_joint
        (I := I) co.gInf J hJ hjoint
  have hscalarTime : ∀ t ∈
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier,
      ∀ x : P₀.M,
        DifferentiableWithinAt Real
          (fun s : Real =>
            DifferentialGeometry.Integral.Connection.metricScalarAt
              (I := I) (co.gInf s) x)
          (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier t := by
    intro t ht x
    have htJ : t ∈ J := hcarrier ▸ ht
    have htime :=
      DifferentialGeometry.PDE.RicciFlow.scalarTime_of_joint
        (I := I) co.gInf J hJ hjoint t htJ x
    simpa only [hcarrier] using htime
  have hricciCont := DifferentialGeometry.PDE.RicciFlow.ricciCont_of_joint
    (I := I) co.gInf J hJ hjoint
  have hrm04Cont := DifferentialGeometry.PDE.RicciFlow.rm04Cont_of_joint
    (I := I) co.gInf J hJ hjoint
  apply DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_reg
    (I := I) co.gInf hsmooth hpde hscalarCont hscalarTime
  · simpa only [hcarrier] using hricciCont
  · simpa only [hcarrier] using hrm04Cont

/-- Reindexing a solution candidate in time does not change its intrinsic
curvature-derivative norm. -/
private theorem nablaK_restrict
    {D D' : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn
      (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
        (I := I) (S.timeRestrict D') k t x =
      DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
        (I := I) S k t x := by
  have hfield :
      DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field
          (I := I) (S.timeRestrict D') t k =
        DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field
          (I := I) S t k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_succ,
          DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_succ, ih]
        simp only [
          DifferentialGeometry.PDE.RicciFlow.SolutionOn.family_connection,
          DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base]
  unfold DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
  rw [hfield]
  simp only [
    DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_base]

/-- The compact buffered Shi estimate supplies the derivative input for the
canonical closed-window Hamilton source. -/
noncomputable def source_deriv
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    FlowDerivativeInput (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) := by
  classical
  letI : CompactSpace M := hcompact
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  let Cderiv : Nat -> Real := fun k =>
    Real.sqrt
      (DifferentialGeometry.PDE.RicciFlow.rmSlabConst
        ((100 : Real) ^ 2) ham3ShiLeft (-(ham3_r0 ^ 2)) 0 k k)
  have halphaBeta : ham3ShiLeft < -(ham3_r0 ^ 2) := by
    dsimp only [ham3ShiLeft]
    nlinarith [sq_pos_of_pos ham3_r0_pos]
  have hbetaZero : -(ham3_r0 ^ 2) <= (0 : Real) :=
    neg_nonpos.mpr (sq_nonneg ham3_r0)
  have hsp : FlowDerivBounds (I := I) X := by
    refine
      { C := Cderiv
        nonneg := fun k => Real.sqrt_nonneg _
        bound := ?_ }
    intro i k
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    unfold HasSpacetimeCurvDerivBound
    intro t ht x
    have ht' : t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 := by
      change t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 at ht
      exact ht
    let j := ham3Start (I := I) P Q hsel hwindow + i
    have hsol :
        DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
          (ham3RescaledSol (I := I) P Q hsel j) := by
      exact DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
        P.isSmooth.isSolution (Q.time j)
        (ham3BlowupScale (I := I) P Q j)
        (hsel.1 j) (hsel.2.2.1 j)
    have hsq :=
      DifferentialGeometry.PDE.RicciFlow.movingRmOn (I := I)
        (S := ham3RescaledSol (I := I) P Q hsel j)
        halphaBeta hbetaZero
        (ham3_shi_car (I := I) h0omega P hD Q hsel hwindow i)
        (ham3_shi_reg (I := I) h0omega P hD Q hsel hwindow i)
        (by norm_num : (0 : Real) <= (100 : Real) ^ 2)
        (ham3_shi_rm (I := I) P Q hsel hwindow hrm i)
        hdim hsol k k le_rfl t ht' x
    unfold curvDerivNorm Cderiv
    change
      Real.sqrt
          (curvDerivNormSq k ((X.term i).S.base.metric t) x) <=
        Real.sqrt
          (DifferentialGeometry.PDE.RicciFlow.rmSlabConst
            ((100 : Real) ^ 2) ham3ShiLeft (-(ham3_r0 ^ 2)) 0 k k)
    rw [curvNormSq_eq (S := (X.term i).S)]
    apply Real.sqrt_le_sqrt
    change
      DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic
          (I := I)
          ((ham3RescaledSol (I := I) P Q hsel j).timeRestrict ham3CommonD)
          k t x <=
        DifferentialGeometry.PDE.RicciFlow.rmSlabConst
          ((100 : Real) ^ 2) ham3ShiLeft (-(ham3_r0 ^ 2)) 0 k k
    rw [nablaK_restrict]
    exact hsq
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨hbetaZero, le_rfl⟩
  exact
    { spacetime := hsp
      at_zero_geom := hsp.at_time hzero }

/-- The buffered untruncated Hamilton rescalings provide the regular source
flows needed to run the constants-first covariant/Lipschitz engine on the full
closed common window. -/
theorem ham3_src_covlip
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    {P₀ : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) P₀ subseq)
    (R : letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      SmoothRiemannianMetric I P₀.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (Bmax : Real) (hBmax : 1 ≤ Bmax)
    (hequiv :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : Real, t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
          MetricUniformEquivalentOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
            (srcMetric (I := I) Φ hsrc htgt k t) Bmax)
    (hShi :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          MovingShiBoundOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (-(ham3_r0 ^ 2)) 0
            (fun _ t ↦ srcMetric (I := I) Φ hsrc htgt k t) N KShi)
    (hinit :
      letI : TopologicalSpace P₀.M := P₀.topology
      letI : ChartedSpace H P₀.M := P₀.charted
      letI : T2Space P₀.M := P₀.t2
      letI : IsManifold I ∞ P₀.M := P₀.smooth
      letI : SigmaCompactSpace P₀.M := P₀.sigmaCompact
      ∀ q : Nat, ∃ Cq : Real, 0 ≤ Cq ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k 0)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) :
    SrcCovLipData (I := I) Φ R hsrc htgt (-(ham3_r0 ^ 2)) 0 := by
  refine srcCovLip_of_flow (I := I)
    (β := -(ham3_r0 ^ 2)) (ψ := 0) (t₀ := 0)
    Φ R hsrc htgt
    (fun k ↦
      DifferentialGeometry.PDE.RicciFlow.paraInterval P.D
        (Q.time (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (hsel.2.2.1
          (ham3Start (I := I) P Q hsel hwindow + subseq k)))
    (fun k ↦ sourceFlowOf (I := I) Φ k (hsrc k) (htgt k)
      (ham3RescaledSol (I := I) P Q hsel
        (ham3Start (I := I) P Q hsel hwindow + subseq k)))
    (fun k ↦ isSoln_sourceFlowOf (I := I) Φ k (hsrc k) (htgt k)
      (ham3RescaledSol (I := I) P Q hsel
        (ham3Start (I := I) P Q hsel hwindow + subseq k))
      (DifferentialGeometry.PDE.RicciFlow.paraSol (I := I) P.S
        P.isSmooth.isSolution
        (Q.time (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (ham3BlowupScale (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (hsel.1 (ham3Start (I := I) P Q hsel hwindow + subseq k))
        (hsel.2.2.1
          (ham3Start (I := I) P Q hsel hwindow + subseq k))))
    ?_ ?_ ?_ ?_ Bmax hBmax hequiv hShi hinit
  · intro k r
    rfl
  · exact neg_nonpos.mpr (sq_nonneg ham3_r0)
  · exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  · intro k s hs
    apply ham3_shi_reg (I := I) h0omega P hD Q hsel hwindow (subseq k)
    refine ⟨?_, hs.2⟩
    dsimp only [ham3ShiLeft]
    nlinarith [sq_pos_of_pos ham3_r0_pos, hs.1]

/-- Assemble the canonical closed-window Hamilton flow upgrade and prove
completeness of every limit time slice. -/
theorem ham3_closed_upg
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (canon : StepDCanonData (I := I)
      ((ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).atZero
        (I := I))) :
    ∃ d : FlowUpgradeData (I := I)
        (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) canon.mc,
      ∀ t : Real,
        t ∈ (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D.carrier →
          MetricComplete (I := I) (d.data.L.atTime (I := I) t) := by
  classical
  letI : CompactSpace M := hcompact
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  let mc := canon.mc
  let Phi := pointedCGHMaps_of_manifold (I := I) X
    mc.limit mc.subseq mc.maps
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact

  have hsrc : SrcSigma (I := I) Phi := by
    intro k
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.source_open (I := I) Phi k)
  have htgt : TgtSigma (I := I) Phi := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.target_open (I := I) Phi k)
  let bf := Classical.choice (nonempty_bumpFamily (I := I) Phi)

  let gRefT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I (X.term (mc.subseq k)).M :=
    fun k =>
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      (X.term (mc.subseq k)).S.family.metric 0

  have hcanonRel := StepDCanonData.canon_rel (I := I) canon hsrc htgt
  dsimp only at hcanonRel
  obtain ⟨Crel, hCrel, hrelZero⟩ := hcanonRel
  have hsrcZero (k : Nat) :
      tgtRefSrc (I := I) Phi gRefT hsrc htgt k =
        srcMetric (I := I) Phi hsrc htgt k 0 := by
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    rfl
  have hrel : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Phi k))
        (refRes (I := I) Phi mc.limit.metric hsrc k)
        (tgtRefSrc (I := I) Phi gRefT hsrc htgt k) Crel := by
    intro k
    rw [hsrcZero k]
    exact hrelZero k
  have hinit := StepDCanonData.canon_init (I := I) canon hsrc htgt
  dsimp only at hinit
  have hcp := StepDCanonData.canon_cp (I := I) canon hsrc htgt
  dsimp only at hcp

  obtain ⟨A, Bmax, hA, hBmax, hBmajor, hwindowRaw⟩ :=
    ham3_win_equiv (I := I) h0omega P hD Q hsel hwindow hrm
  let B : Real → Real := fun t => metricEquivalenceFactor 1 A t 0
  have hequivT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Phi.target k)
        (-(ham3_r0 ^ 2)) 0 (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    have hall := hwindowRaw (mc.subseq k)
    have hall' : MetricUniformEquivalentOnWindow (I := I) Set.univ
        (-(ham3_r0 ^ 2)) 0 (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B := by
      simpa only [X, ham3SourceSeq,
        DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric,
        gRefT, B] using hall
    intro i t ht
    refine ⟨(hall' i t ht).1, ?_⟩
    intro x _hx v
    exact (hall' i t ht).2 x (Set.mem_univ x) v

  have hShiT : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Phi.target k)
          (-(ham3_r0 ^ 2)) 0
          (fun _ t => (X.term (mc.subseq k)).S.family.metric t) N KShi := by
    intro N
    obtain ⟨KShi, hKShi, hShiAll⟩ :=
      ham3_win_shi (I := I) h0omega hcompact P hD Q hsel hwindow hrm N
    refine ⟨KShi, hKShi, ?_⟩
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    intro s hs i t ht x _hx
    simpa only [X, ham3SourceSeq,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.timeRestrict_metric] using
      hShiAll (mc.subseq k) s hs i t ht x (Set.mem_univ x)
  have hShiSrc : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
          sourceDomTop (I := I) Phi k
        letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
          sourceDomCharted (I := I) Phi k
        letI : T2Space (SourceDomain (I := I) Phi k) :=
          sourceDomT2 (I := I) Phi k
        letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
          sourceDomSmooth (I := I) Phi k
        letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
          sourceDomSigmaOf (I := I) Phi k (hsrc k)
        MovingShiBoundOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (-(ham3_r0 ^ 2)) 0
          (fun _ t => srcMetric (I := I) Phi hsrc htgt k t) N KShi := by
    intro N
    obtain ⟨KShi, hKShi, hShi⟩ := hShiT N
    exact ⟨KShi, hKShi, fun k =>
      srcShi (I := I) Phi hsrc htgt (-(ham3_r0 ^ 2)) 0
        N KShi hShi k⟩

  have hBsrc : 1 ≤ Crel * Bmax :=
    one_le_mul_of_one_le_of_one_le hCrel hBmax
  have hequivSrc : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
        sourceDomSigmaOf (I := I) Phi k (hsrc k)
      ∀ t : Real, t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (refRes (I := I) Phi mc.limit.metric hsrc k)
          (srcMetric (I := I) Phi hsrc htgt k t) (Crel * Bmax) := by
    intro k t ht
    letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
      sourceDomTop (I := I) Phi k
    letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
      sourceDomCharted (I := I) Phi k
    letI : T2Space (SourceDomain (I := I) Phi k) :=
      sourceDomT2 (I := I) Phi k
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
      sourceDomSmooth (I := I) Phi k
    letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
      sourceDomSigmaOf (I := I) Phi k (hsrc k)
    have hEq := srcEquivOn (I := I) Phi mc.limit.metric hsrc htgt
      (-(ham3_r0 ^ 2)) 0 gRefT B Crel hequivT hrel k t ht
    exact metricUniformEquivalentOn_of_le (I := I) hEq
      (mul_le_mul_of_nonneg_left (hBmajor t ht)
        (zero_le_one.trans hCrel))
  have srcData : SrcCovLipData (I := I) Phi mc.limit.metric hsrc htgt
      (-(ham3_r0 ^ 2)) 0 :=
    ham3_src_covlip (I := I) h0omega P hD Q hsel hwindow
      Phi mc.limit.metric hsrc htgt (Crel * Bmax) hBsrc
      hequivSrc hShiSrc hinit
  let cLow : Real := (Crel * Bmax)⁻¹
  have hcLow : 0 < cLow :=
    inv_pos.mpr (zero_lt_one.trans_le hBsrc)
  have hbound :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
                sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * mc.limit.metric.inner (y : mc.limit.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hsrc htgt k t).inner y v v := by
    intro k t ht y v
    simpa only [cLow] using
      ((hequivSrc k t ht).2 y (Set.mem_univ y) v).1
  have hcovTail :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
        t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
          ∀ z : mc.limit.M, z ∈ bf.grow k →
            metricCovDerivNorm (I := I) q
              (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
              mc.limit.metric z ≤ C := by
    have hcovSrc : ∀ q : Nat, ∃ C : Real, 0 ≤ C ∧
        ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
          ∀ y : SourceDomain (I := I) Phi k,
            (y : mc.limit.M) ∈ bf.grow k →
              letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
              letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
                sourceDomCharted (I := I) Phi k
              letI : T2Space (SourceDomain (I := I) Phi k) :=
                sourceDomT2 (I := I) Phi k
              letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
                sourceDomSmooth (I := I) Phi k
              letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
                sourceDomSigmaOf (I := I) Phi k (hsrc k)
              metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Phi hsrc htgt k t)
                (refRes (I := I) Phi mc.limit.metric hsrc k) y ≤ C := by
      intro q
      obtain ⟨C, hC, hcov⟩ := srcData.cov q
      exact ⟨C, hC, fun k t ht y _hy => hcov k t ht y⟩
    exact covTail_of_bounds (I := I) Phi mc.limit.metric bf hsrc htgt
      (-(ham3_r0 ^ 2)) 0 hcovSrc
  let co := convOut_of_src (I := I) Phi mc.limit.metric bf hsrc htgt
    (neg_nonpos.mpr (sq_nonneg ham3_r0)) hBsrc hequivSrc srcData
  have hcarrier : X.D.carrier ⊆ Set.Icc (-(ham3_r0 ^ 2)) 0 := by
    intro t ht
    change t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 at ht
    exact ht
  have hzeroMem : (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 :=
    ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  have hzero : co.gInf 0 = mc.limit.metric :=
    gInf_zero_eq (I := I) Phi mc.limit.metric bf hsrc htgt
      (-(ham3_r0 ^ 2)) 0 co hzeroMem mc.limit.metric
      (conv0_of_cp (I := I) Phi mc.limit.metric hsrc htgt
        mc.limit.metric hcp)
  have hsol :=
    ham3_limit_soln (I := I) h0omega P hD Q hsel hwindow Phi co
  let L := flowOfMetric (I := I) X.D mc.limit co.gInf hsol
  have hL0 : L.atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  have hscalarRaw := ConvOut.scalar_conv (I := I) (Φ := Phi)
    mc.limit.metric bf hsrc htgt (-(ham3_r0 ^ 2)) 0 cLow hcLow
    hbound hcovTail co hcarrier
  have hricRaw := ConvOut.ricNorm_conv (I := I) (Φ := Phi)
    mc.limit.metric bf hsrc htgt (-(ham3_r0 ^ 2)) 0 cLow hcLow
    hbound hcovTail co hcarrier
  have map_cast {P₁ P₂ : PointedRiemannianManifold (I := I)}
      {s : Nat → Nat} (h : P₁ = P₂)
      (maps : PointedCGHMaps (I := I) X P₂ s)
      (k : Nat) (x : P₁.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) X P₁ s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)).map k x =
        (Phi.compSubseq co.φ co.hφ).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun Q₀ : PointedRiemannianManifold (I := I) => Q₀.M) hL0) x)
    exact
      (eq_of_heq (map_cast hL0 (Phi.compSubseq co.φ co.hφ) k x)).trans
        (congrArg (fun y => (Phi.compSubseq co.φ co.hφ).map k y) hx)
  have scalar : ScalarPullbackTendsto (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold ScalarPullbackTendsto FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (DifferentialGeometry.Integral.Connection.metricScalarAt
        (I := I) (co.gInf t) x))
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun k => ?_)) (hscalarRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => (X.term ((mc.subseq ∘ co.φ) k)).S.scalar t y)
      (hmap k x).symm
  have ricciNorm : RicNormPullback (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold RicNormPullback FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (Tensor0SBundle.normSq0S (I := I) (co.gInf t) x 2
        (DifferentialGeometry.Integral.Connection.metricRicci
          (I := I) (co.gInf t) x)))
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun k => ?_)) (hricRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => DifferentialGeometry.PDE.RicciFlow.ricciNorm
        (I := I) (X.term ((mc.subseq ∘ co.φ) k)).S t y)
      (hmap k x).symm
  let d := flowUpgrade_of_maps (I := I) (X := X) mc L mc.limit rfl hL0
    Phi mc.limit.metric bf hsrc htgt (-(ham3_r0 ^ 2)) 0 hcarrier co
    (fun _ _ => HEq.rfl) scalar ricciNorm
  refine ⟨d, ?_⟩
  intro t ht
  have htWindow : t ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 := hcarrier ht
  have hseq : ∀ (k : Nat) (s : Real),
      s ∈ Set.Icc (-(ham3_r0 ^ 2)) 0 →
        ∀ (x : mc.limit.M) (v : TangentSpace I x),
          min cLow 1 * mc.limit.metric.inner x v v ≤
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt
              (co.φ k) s).inner x v v := by
    intro k s hs x v
    exact gSeqExt_lower (I := I) Phi mc.limit.metric bf hsrc htgt
      cLow (-(ham3_r0 ^ 2)) 0 hcLow hbound (co.φ k) s hs x v
  have hcomplete := ConvOut.complete_at (I := I) Phi mc.limit_complete co
    (lt_min hcLow one_pos) hseq htWindow
  have hdL : d.data.L = L := by
    exact flowUpgrade_maps_L (I := I) (X := X) mc L mc.limit rfl hL0
      Phi mc.limit.metric bf hsrc htgt (-(ham3_r0 ^ 2)) 0 hcarrier co
      (fun _ _ => HEq.rfl) scalar ricciNorm
  rw [hdL]
  change MetricComplete (I := I)
    ({ mc.limit with metric := co.gInf t } :
      PointedRiemannianManifold (I := I))
  exact hcomplete

/-- The canonical time-zero Step-D data produce a genuine smooth
closed-window CGH limit with complete time slices. -/
theorem ham3_closed_cgh
    {omega : Real} (h0omega : 0 < omega)
    (hcompact : CompactSpace M)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (canon : StepDCanonData (I := I)
      ((ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).atZero
        (I := I))) :
    ∃ L : PointedFlowData.{u, uE, uH} (I := I)
        (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).D,
      ∃ subseq : Nat → Nat,
        StrictMono subseq ∧
          Nonempty (SmoothCGHConverges (I := I)
            (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow)
            L subseq) ∧
          ∀ t : Real,
            t ∈ (ham3SourceSeq
              (I := I) h0omega P hD Q hsel hwindow).D.carrier →
              MetricComplete (I := I) (L.atTime (I := I) t) := by
  obtain ⟨d, hcomplete⟩ :=
    ham3_closed_upg (I := I) h0omega hcompact P hD Q hsel hrm
      hwindow canon
  let mc := canon.mc.compSubseq d.φ d.hφ
  exact
    ⟨d.data.L, mc.subseq, mc.strictMono, d.data.converges, hcomplete⟩

/-- Retain a genuine smooth-CGH limit, its comparison maps, its original
Hamilton indexing, source identifications, and limit completeness in the
Section 12 data record. -/
def cghToHam3
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (origIndex : Nat -> Nat) (horig : StrictMono origIndex)
    (toOrig : forall i : Nat,
      letI : TopologicalSpace (X.term i).M := (X.term i).topology
      letI : ChartedSpace H (X.term i).M := (X.term i).charted
      (X.term i).M ≃ₘ⟮I, I⟯ M)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3CGHLimitData (I := I) M where
  N := L.M
  topology := L.topology
  charted := L.charted
  smooth := L.smooth
  smooth_plus := by
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    change IsManifold I ∞ L.M
    infer_instance
  sigmaCompact := L.sigmaCompact
  t2 := L.t2
  t2TangentBundle := L.t2TangentBundle
  basepoint := L.basepoint
  D := X.D
  S := L.S
  isSolution := L.isSolution
  sourceTerm := X.term
  origIndex := origIndex
  origStrict := horig
  cghSubseq := subseq
  cghStrict := hsubseq
  cgh := hconv
  sourceToOrig := toOrig
  limitComplete := hcomplete

/-- Concrete data identifying a common-window pointed-flow sequence with the
selected Hamilton parabolic rescalings. -/
structure Ham3SourceLink
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  origIndex : Nat -> Nat
  strictMono : StrictMono origIndex
  toOrig : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    (X.term i).M ≃ₘ⟮I, I⟯ M
  time_mem : forall (i : Nat) (t : Real), t ∈ X.D.carrier ->
    t ∈ (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D (Q.time (origIndex i))
      (ham3BlowupScale (I := I) P Q (origIndex i))
      (hsel.1 (origIndex i)) (hsel.2.2.1 (origIndex i))).carrier
  basepoint_map : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    toOrig i (X.term i).basepoint = Q.point (origIndex i)
  metric_eq : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    forall t : Real, t ∈ X.D.carrier ->
      (X.term i).S.base.metric t =
        Diffeomorph.pullbackMetricCross
          ((ham3RescaledSol (I := I) P Q hsel (origIndex i)).base.metric t)
          (toOrig i)
  baseScalar : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.scalar 0 (X.term i).basepoint =
      ham3RescaledScalar (I := I) P Q (origIndex i) 0 (Q.point (origIndex i))

/-- The concrete source-identification data for the common-window Hamilton
parabolic-rescaling tail, using the identity maps back to the original
manifold. -/
noncomputable def ham3SourceLink
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    Ham3SourceLink (I := I) (M := M) P Q hsel
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow) := by
  refine
    { origIndex := fun i => ham3Start (I := I) P Q hsel hwindow + i
      strictMono := ?_
      toOrig := fun _ => _root_.Diffeomorph.refl I M ∞
      time_mem := ?_
      basepoint_map := ?_
      metric_eq := ?_
      baseScalar := ?_ }
  · intro i j hij
    exact Nat.add_lt_add_left hij (ham3Start (I := I) P Q hsel hwindow)
  · intro i t ht
    exact ham3_car_subset (I := I) h0omega P hD Q hsel hwindow i ht
  · intro i
    rfl
  · intro i t _ht
    change
      (ham3RescaledSol (I := I) P Q hsel
          (ham3Start (I := I) P Q hsel hwindow + i)).base.metric t =
        Diffeomorph.pullbackMetricCross
          ((ham3RescaledSol (I := I) P Q hsel
            (ham3Start (I := I) P Q hsel hwindow + i)).base.metric t)
          (_root_.Diffeomorph.refl I M ∞)
    apply srm_eq_of_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    have hmfd :
        mfderiv I I
            (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x =
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      have h1 :
          mfderiv I I
              (fun y : M =>
                (_root_.Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) y) x =
            mfderiv I I (id : M → M) x := rfl
      rw [h1]
      exact mfderiv_id
    rw [hmfd]
    rfl
  · intro i
    change
      (ham3RescaledSol (I := I) P Q hsel
        (ham3Start (I := I) P Q hsel hwindow + i)).scalar 0
          (Q.point (ham3Start (I := I) P Q hsel hwindow + i)) =
        ham3RescaledScalar (I := I) P Q
          (ham3Start (I := I) P Q hsel hwindow + i) 0
          (Q.point (ham3Start (I := I) P Q hsel hwindow + i))
    simp only [ham3RescaledSol,
      DifferentialGeometry.PDE.RicciFlow.paraSolution_scalar,
      DifferentialGeometry.PDE.RicciFlow.paraTime,
      ham3RescaledScalar, ham3RescaledTime, ham3Scalar, ham3Solution]

/-- A concrete source link realizes the source fields of the corresponding
Hamilton limit-data record. -/
theorem Ham3SourceLink.realizes
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3SourceRealizes (I := I) (M := M) P Q hsel
      (cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  refine
    { time_mem := ?_
      basepoint_map := ?_
      metric_eq := ?_ }
  · intro i t ht
    exact hsource.time_mem i t ht
  · intro i
    simpa [cghToHam3] using hsource.basepoint_map i
  · intro i t ht
    simpa [cghToHam3] using hsource.metric_eq i t ht

/-- Hamilton-specific compactness conclusion whose tensor-transfer evidence is
bound to the actual smooth-CGH witness rather than quantified over arbitrary
limit records. -/
def HamCGHConclusion
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D,
    exists subseq : Nat -> Nat,
    exists hsubseq : StrictMono subseq,
    exists hconv : SmoothCGHConverges (I := I) X L subseq,
    exists hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t),
      (letI : TopologicalSpace L.M := L.topology
       ConnectedSpace L.M) /\
      (let Lh := cghToHam3 (I := I) (M := M) X hsource.origIndex
        hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
       Ham3RicNonnegTransfer (I := I) (M := M) P Q hsel Lh /\
         LimitScalarPos (I := I) (M := M) Lh /\
         Ham3PinchTransfer (I := I) (M := M) P Q hsel Lh)

/-- Scalar pullback convergence plus basepoint preservation gives the
Hamilton basepoint scalar-convergence datum.  Scalar pullback convergence is
quantified over carrier times, so time `0` must lie on the common flow
interval (`h0`); in the Section 12 setup this follows from the window
hypothesis `Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier`. -/
theorem baseScalarConv_of_smoothCGH
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3LimitBaseScalarConv (I := I) (M := M) P Q
      (cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  classical
  have hscalar := hconv.scalar_converges 0 h0 L.basepoint
  refine hscalar.congr' ?_
  filter_upwards with k
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  calc
    (X.term (subseq k)).S.scalar 0 (hconv.spatial.maps.map k (L.atTime 0).basepoint)
        = (X.term (subseq k)).S.scalar 0 (X.term (subseq k)).basepoint := by
          simp [PointedCGHMaps.map, hconv.spatial.maps.basepoint_map k]
    _ = ham3RescaledScalar (I := I) P Q (hsource.origIndex (subseq k)) 0
        (Q.point (hsource.origIndex (subseq k))) := by
          simpa using hsource.baseScalar (subseq k)

/-- Smooth CGH convergence transfers the time-zero improved-pinching decay to
the limit trace-free Ricci norm. -/
theorem tf_decay0_of_cgh
    {omega : Real} (h0omega : 0 < omega)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (L : Ham3CGHLimitData (I := I) M)
    (h0 : (0 : Real) ∈ L.D.carrier)
    (hreal : Ham3SourceRealizes (I := I) (M := M) P Q hsel L) :
    LimitTfDecayAt (I := I) L 0 := by
  classical
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  rcases ham3_tf_bound0 (I := I) P Q hsel hscalar hpinch with
    ⟨epsilon, C, hepsilon, _hepsilon1, _hC, hbound⟩
  have hconv :
      FunctionPullbackTendsto (I := I) L.cgh.spatial.maps
        (fun k _t x =>
          letI : TopologicalSpace (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).topology
          letI : ChartedSpace H (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).charted
          letI : IsManifold I ∞ (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).smooth
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
              (L.sourceTerm (L.cghSubseq k)).M := by
            change IsManifold I ∞ (L.sourceTerm (L.cghSubseq k)).M
            infer_instance
          letI : SigmaCompactSpace (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).sigmaCompact
          letI : T2Space (L.sourceTerm (L.cghSubseq k)).M :=
            (L.sourceTerm (L.cghSubseq k)).t2
          DifferentialGeometry.PDE.RicciFlow.tfRicNormSq
            (L.sourceTerm (L.cghSubseq k)).S.scalar
            (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
              (L.sourceTerm (L.cghSubseq k)).S) 0 x)
        (fun _t x =>
          DifferentialGeometry.PDE.RicciFlow.tfRicNormSq
            L.S.scalar
            (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S)
            0 x) := by
    intro _t _ht x
    have hsc := L.cgh.scalar_converges 0 h0 x
    have hric := L.cgh.ricciNorm_converges 0 h0 x
    simpa only [
      DifferentialGeometry.PDE.RicciFlow.tfRicNormSq,
      DifferentialGeometry.PDE.RicciFlow.tracefreeRicciNormSqOf,
      DifferentialGeometry.PDE.RicciFlow.tracefreeRicciNormSqAtOf] using
      hric.sub ((hsc.pow 2).div_const 3)
  have hdecay :=
    ham3_scale_decay (I := I) h0omega P hD Q hsel L
      (C := C) hepsilon
  have hsmall :=
    FunctionPullbackTendsto.le_of_bound0 (I := I) hconv
      (fun _t _x k =>
        C * ham3BlowupScale (I := I) P Q (L.subseq k) ^ (-epsilon))
      (by
        intro _t x
        refine ⟨hdecay, Filter.Eventually.of_forall ?_⟩
        intro k
        let i : Nat := L.cghSubseq k
        letI : TopologicalSpace (L.sourceTerm i).M :=
          (L.sourceTerm i).topology
        letI : ChartedSpace H (L.sourceTerm i).M :=
          (L.sourceTerm i).charted
        letI : IsManifold I ∞ (L.sourceTerm i).M :=
          (L.sourceTerm i).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (L.sourceTerm i).M := by
          change IsManifold I ∞ (L.sourceTerm i).M
          infer_instance
        letI : SigmaCompactSpace (L.sourceTerm i).M :=
          (L.sourceTerm i).sigmaCompact
        letI : T2Space (L.sourceTerm i).M :=
          (L.sourceTerm i).t2
        have hcross :
            DifferentialGeometry.PDE.RicciFlow.tfRicNormSq
                (L.sourceTerm i).S.scalar
                (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                  (L.sourceTerm i).S)
                0 (L.cgh.spatial.maps.map k x) =
              DifferentialGeometry.PDE.RicciFlow.tfRicNormSq
                (ham3RescaledSol (I := I) P Q hsel (L.origIndex i)).scalar
                (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
                (ham3RescaledSol (I := I) P Q hsel (L.origIndex i)))
                0
                (L.sourceToOrig i (L.cgh.spatial.maps.map k x)) := by
          simp only [
            DifferentialGeometry.PDE.RicciFlow.tfRicNormSq,
            DifferentialGeometry.PDE.RicciFlow.tracefreeRicciNormSqOf,
            DifferentialGeometry.PDE.RicciFlow.ricciNorm,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricci,
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.family_metric,
            DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
            DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricci]
          rw [hreal.metric_eq i 0 h0]
          exact
            tfRicNormSq_cross (I := I) (J := I)
              ((ham3RescaledSol (I := I) P Q hsel
                (L.origIndex i)).base.metric 0)
              (L.sourceToOrig i) (L.cgh.spatial.maps.map k x)
        rw [hcross]
        simpa [i, Ham3CGHLimitData.subseq] using
          hbound (L.origIndex i)
            (L.sourceToOrig i (L.cgh.spatial.maps.map k x)))
  exact hsmall 0 h0

/-- The genuine time-zero smooth-CGH scalar and Ricci-norm convergence,
Hamilton's improved pinching estimate, and the basepoint normalization make
the retained limit slice a positive constant-curvature metric. -/
theorem round0_of_cgh
    {omega : Real} (h0omega : 0 < omega)
    (hdim : Module.finrank Real E = 3)
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t))
    (hconnected :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M) :
    let Lh := cghToHam3 (I := I) (M := M) X hsource.origIndex
      hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
    LimitRoundAt (I := I) (M := M) Lh 0 := by
  classical
  let Lh := cghToHam3 (I := I) (M := M) X hsource.origIndex
    hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
  have h0h : (0 : Real) ∈ Lh.D.carrier := by
    simpa [Lh, cghToHam3] using h0
  have hreal : Ham3SourceRealizes (I := I) (M := M) P Q hsel Lh := by
    simpa [Lh] using
      (Ham3SourceLink.realizes (I := I) (M := M) P Q hsel hsource
        L subseq hsubseq hconv hcomplete)
  have hdecay : LimitTfDecayAt (I := I) (M := M) Lh 0 :=
    tf_decay0_of_cgh (I := I) (M := M) h0omega P hD Q hsel hscalar
      hpinch Lh h0h hreal
  have htf : LimitTfZeroAt (I := I) (M := M) Lh 0 :=
    tf_zero_of_decay (I := I) (M := M) hdim hdecay
  have heinstein : LimitEinsteinAt (I := I) (M := M) Lh 0 :=
    limitEinstein_of_tf0 (I := I) (M := M) hdim htf
  have hbaseConv : Ham3LimitBaseScalarConv (I := I) (M := M) P Q Lh := by
    simpa [Lh] using
      (baseScalarConv_of_smoothCGH (I := I) (M := M) P Q hsel hsource
        h0 hsubseq hconv hcomplete)
  have hbaseOne : LimitBaseScalarOne (I := I) (M := M) Lh :=
    limit_base_scalar_one (I := I) (M := M) P Q hsel hbaseConv
  -- `Lh` is `let`-bound, so its instance-implicit structure fields are not picked
  -- up by synthesis; install them explicitly for the evaluations below.
  letI : TopologicalSpace Lh.N := Lh.topology
  letI : ChartedSpace H Lh.N := Lh.charted
  letI : IsManifold I ∞ Lh.N := Lh.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) Lh.N := Lh.smooth_plus
  letI : SigmaCompactSpace Lh.N := Lh.sigmaCompact
  letI : T2Space Lh.N := Lh.t2
  letI : T2Space (TangentBundle I Lh.N) := Lh.t2TangentBundle
  have hbaseEq : Lh.S.scalar 0 Lh.basepoint = 1 := by
    simpa [LimitBaseScalarOne] using hbaseOne
  have hbasePos : 0 < Lh.S.scalar 0 Lh.basepoint := by
    rw [hbaseEq]
    exact one_pos
  have hconn : Ham3LimitConnected (I := I) (M := M) Lh := by
    simpa [Lh, cghToHam3, Ham3LimitConnected] using hconnected
  have hbdry : Ham3LimitBoundaryless (I := I) (M := M) Lh := by
    simpa [Lh, cghToHam3, Ham3LimitBoundaryless] using
      (inferInstance : I.Boundaryless)
  exact limit_round_base (I := I) (M := M) hdim hconn hbdry
    hbasePos heinstein

/-- The genuine time-zero smooth-CGH data transfer the round limit metric back
to a constant-positive-sectional-curvature metric on the original manifold. -/
theorem const0_of_cgh
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hscalar :
      forall t : Real, t ∈ P.D.carrier ->
        forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t))
    (hconnected :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M) :
    AdmitsConstPosSec (I := I) (M := M) := by
  let Lh := cghToHam3 (I := I) (M := M) X hsource.origIndex
    hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
  have hround : LimitRoundAt (I := I) (M := M) Lh 0 := by
    simpa only [Lh] using
      (round0_of_cgh (I := I) (M := M) h0omega hM.2.2.2 P hD Q hsel
        hscalar hpinch hsource h0 L subseq hsubseq hconv hcomplete hconnected)
  have h0h : (0 : Real) ∈ Lh.D.carrier := by
    change (0 : Real) ∈ X.D.carrier
    exact h0
  have hconn : Ham3LimitConnected (I := I) (M := M) Lh := by
    change (letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    exact hconnected
  simpa only [AdmitsConstPosSec] using
    (limit_to_orig (I := I) (M := M) hM h0h hconn hround)

/-- A uniform time-zero injectivity bound feeds the Hamilton source through the
provider-native H6 compactness route and produces a constant-positive-
sectional-curvature metric on the original manifold. -/
theorem ham3_const_of_inj
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hscalar : forall t : Real, t ∈ P.D.carrier →
      forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (hinj : FlowBaseInjBound (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow)) :
    AdmitsConstPosSec (I := I) (M := M) := by
  classical
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  change FlowBaseInjBound (I := I) X at hinj
  have hcpl : SeqMetricComplete (I := I) (X.atZero (I := I)) := by
    refine ⟨?_⟩
    intro k
    change MetricComplete (I := I) ((X.term k).atTime (I := I) 0)
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact (X.term k).M ?_ ?_
    simpa only [X, ham3SourceSeq] using hM.1
  have hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    change @ConnectedSpace (X.term k).M (X.term k).topology
    simpa only [X, ham3SourceSeq] using hM.2.1
  let hderiv : FlowDerivativeInput (I := I) X :=
    source_deriv (I := I) h0omega hM.1 hM.2.2.2 P hD Q hsel hrm hwindow
  let seed : MetricCompactSeed (I := I) (X.atZero (I := I)) :=
    metricSeedOfBG (I := I) (X.atZero (I := I))
      hcpl hderiv.at_zero_geom hinj hconn
  have hd : Nonempty (H6NormalData (I := I) (X.atZero (I := I)) seed.decay) :=
    exists_h6NormalData (I := I) (X.atZero (I := I))
      hcpl hconn hderiv.at_zero_geom seed.decay seed.realizes
  let canon : StepDCanonData (I := I) (X.atZero (I := I)) :=
    seed.metricCanonH6 (Classical.choice hd) hcpl hconn
  have hcanonConn :
      letI : TopologicalSpace canon.mc.limit.M := canon.mc.limit.topology
      ConnectedSpace canon.mc.limit.M := by
    simpa only [canon] using
      seed.metricCanonH6_conn (Classical.choice hd) hcpl hconn
  obtain ⟨d, hlimCpl⟩ :=
    ham3_closed_upg (I := I) h0omega hM.1 P hD Q hsel hrm
      hwindow canon
  have hlimitConn :
      letI : TopologicalSpace d.data.L.M := d.data.L.topology
      ConnectedSpace d.data.L.M :=
    d.limit_conn hcanonConn
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  let mc := canon.mc.compSubseq d.φ d.hφ
  exact const0_of_cgh
    (I := I) (M := M) h0omega hM P hD Q hsel hscalar hpinch
    (ham3SourceLink (I := I) h0omega P hD Q hsel hwindow)
    hzero d.data.L mc.subseq mc.strictMono
    (Classical.choice d.data.converges) hlimCpl hlimitConn

/-- Perelman's no-local-collapsing theorem supplies one fixed radius and one
fixed positive volume ratio for every member of the canonical Hamilton
source. -/
theorem exists_ham3_vol
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0) :
    ∃ V : FlowBaseVolData (I := I)
        (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow),
      IsFlowBaseVolBound (I := I) V := by
  classical
  letI : CompactSpace M := hM.1
  letI : ConnectedSpace M := hM.2.1
  letI : I.Boundaryless := hM.2.2.1
  have hsol : PDE.RicciFlow.IsSolutionOn (I := I) P.S :=
    P.isSmooth.isSolution
  have hnlc :
      PDE.RicciFlow.Perelman.NoLocalCollapsing P.S ham3_r0 := by
    have htransport :
        ∀ (D : DifferentialGeometry.Integral.Connection.RealTimeInterval)
          (hD' : D =
            DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
              0 omega h0omega)
          (S : PDE.RicciFlow.SolutionOn (I := I) (M := M) D),
          PDE.RicciFlow.IsSolutionOn (I := I) S →
            PDE.RicciFlow.Perelman.NoLocalCollapsing S ham3_r0 := by
      intro D hD' S hS
      subst D
      exact PDE.RicciFlow.Perelman.no_local_open
        (I := I) (M := M) h0omega S hS hM.2.2.2 ham3_r0_pos
    exact htransport P.D hD P.S hsol
  rcases hnlc with ⟨kappa, hkappa, hbelow⟩
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  let c : Real := (2 * ham3_r0 ^ 2) / omega
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos
      (mul_pos (by norm_num) (sq_pos_of_pos ham3_r0_pos)) h0omega
  let r : Real := min ham3_r0 (Real.sqrt c * ham3_r0)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min ham3_r0_pos
      (mul_pos (Real.sqrt_pos.2 hc) ham3_r0_pos)
  have hrle : r ≤ ham3_r0 := by
    exact min_le_left _ _
  let V : FlowBaseVolData (I := I) X :=
    { zero_mem := hzero
      kappa := kappa
      kappa_pos := hkappa
      radius := r
      radius_pos := hr }
  refine ⟨V, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i
    simpa only [V, X] using
      (ham3_src_rm (I := I) h0omega P hD Q hsel hwindow hrm
        hr hrle i)
  · intro i
    let j := ham3Start (I := I) P Q hsel hwindow + i
    have hj : ham3Start (I := I) P Q hsel hwindow ≤ j := by
      simpa only [j] using
        Nat.le_add_right (ham3Start (I := I) P Q hsel hwindow) i
    have hbuf := ham3Buf_spec (I := I) P Q hsel hwindow j hj
    have hscale : 0 < ham3BlowupScale (I := I) P Q j := hsel.1 j
    have htime := hsel.2.2.1 j
    rw [hD] at htime
    have hcscale : c ≤ ham3BlowupScale (I := I) P Q j := by
      apply (div_le_iff₀ h0omega).2
      have hlt :
          ham3BlowupScale (I := I) P Q j * Q.time j <
            ham3BlowupScale (I := I) P Q j * omega :=
        mul_lt_mul_of_pos_left htime.2 hscale
      linarith
    have hsqrt :
        Real.sqrt c ≤
          Real.sqrt (ham3BlowupScale (I := I) P Q j) :=
      Real.sqrt_le_sqrt hcscale
    have hradius :
        r ≤ Real.sqrt (ham3BlowupScale (I := I) P Q j) * ham3_r0 := by
      exact (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_right hsqrt ham3_r0_pos.le)
    let B := ham3RescaledBall (I := I) P Q hsel j r hr
    have hRmB : B.IsRmControlled := by
      simpa only [B, j] using
        (ham3_ball_rm (I := I) h0omega P hD Q hsel hwindow hrm
          hr hrle i)
    have hbelow_i :=
      PDE.RicciFlow.Perelman.para_noncollapse
        (I := I) P.S (Q.time j)
        (ham3BlowupScale (I := I) P Q j) hscale (hsel.2.2.1 j)
        kappa ham3_r0 hbelow
    have hkB : B.IsKappaNoncollapsed kappa :=
      hbelow_i.2 (ham3RescaledZero (I := I) P Q hsel j) B
        hradius hRmB
    simpa only [V, X, B, j, ham3SourceSeq,
      PointedFlowData.baseFlowBall, ham3RescaledBall,
      PDE.RicciFlow.Perelman.FlowMetricBall.IsKappaNoncollapsed,
      PDE.RicciFlow.Perelman.FlowMetricBall.volume,
      PDE.RicciFlow.Perelman.FlowMetricBall.set,
      PDE.RicciFlow.Perelman.FlowMetricBall.setAt,
      PDE.RicciFlow.SolutionOn.timeRestrict_metric] using hkB

/-- Genuine curvature-controlled time-zero base-ball volume bounds feed the
pointwise CGT producer and then the provider-native Hamilton compactness
consumer. -/
theorem ham3_const_of_vol
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hscalar : forall t : Real, t ∈ P.D.carrier →
      forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (V : FlowBaseVolData (I := I)
      (ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow))
    (hvol : IsFlowBaseVolBound (I := I) V) :
    AdmitsConstPosSec (I := I) (M := M) := by
  classical
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  change FlowBaseVolData (I := I) X at V
  change IsFlowBaseVolBound (I := I) V at hvol
  have hcpl : SeqMetricComplete (I := I) (X.atZero (I := I)) := by
    refine ⟨?_⟩
    intro k
    change MetricComplete (I := I) ((X.term k).atTime (I := I) 0)
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact (X.term k).M ?_ ?_
    simpa only [X, ham3SourceSeq] using hM.1
  have hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    change @ConnectedSpace (X.term k).M (X.term k).topology
    simpa only [X, ham3SourceSeq] using hM.2.1
  let hderiv : FlowDerivativeInput (I := I) X :=
    source_deriv (I := I) h0omega hM.1 hM.2.2.2 P hD Q hsel hrm hwindow
  have hinj : FlowBaseInjBound (I := I) X :=
    flowInj_of_vol (I := I) X hcpl hconn hderiv.at_zero_geom V hvol
  exact ham3_const_of_inj
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch hinj

/-- The Hamilton blow-up data, raw curvature bound, and fixed backward window
produce a constant-positive-sectional-curvature metric on the original closed
connected three-manifold. -/
theorem ham3_const
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hscalar : ∀ t : Real, t ∈ P.D.carrier →
      ∀ x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P) :
    AdmitsConstPosSec (I := I) (M := M) := by
  obtain ⟨V, hV⟩ :=
    exists_ham3_vol (I := I) h0omega hM P hD Q hsel hrm hwindow
  exact ham3_const_of_vol
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch V hV

/-- The provider-native HCG route proves Hamilton's constant-curvature
conclusion directly from a positive-Ricci metric on a closed connected
three-manifold, without using the legacy `ham3_cgh_limit` black box. -/
theorem ham3_const_hcg
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) := by
  rcases hpos with ⟨g0, hg0⟩
  rcases ham3_flow_exists_normalized (I := I) (M := M) hM g0 hg0 with
    ⟨omega, h0omega, P, hD⟩
  have hfinite_core :
      ∃ c0 : Real, 0 < c0 ∧ omega ≤ 3 / (2 * c0) :=
    ham3_finite_time (I := I) (M := M) h0omega hM g0 hg0 P hD
  have hfinite :
      ∃ omega c0 : Real, ∃ h0omega : 0 < omega,
        P.D =
            DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
              0 omega h0omega ∧
          0 < c0 ∧ omega ≤ 3 / (2 * c0) := by
    rcases hfinite_core with ⟨c0, hc0, hbound⟩
    exact ⟨omega, c0, h0omega, hD, hc0, hbound⟩
  have hnonneg9 : Ham3Section9RicNonneg (I := I) P omega :=
    ham3_ric_nonneg9 (I := I) (M := M) h0omega hM hg0 P hD
  have hscalarBlow : Ham3ScalarBlowup (I := I) P :=
    ham3_scalar_blowup (I := I) (M := M) h0omega hM P hD hnonneg9
  rcases ham3_point_select (I := I) (M := M) hM g0 hg0 P hfinite
      hscalarBlow with
    ⟨Q, hsel⟩
  have hric : Ham3RescaledRicNonneg (I := I) P Q :=
    ham3_rescaled_ric_nonneg
      (I := I) (M := M) h0omega hM g0 hg0 P hD Q hsel
  have hsec9 : Ham3Section9Pinch (I := I) P omega :=
    ham3_pinch9 (I := I) (M := M) h0omega hM hg0 P hD
  have hpinch : Ham3PinchEstimate (I := I) P :=
    ham3_pinch_imp_can
      (I := I) (M := M) h0omega hM g0 hg0 P hD Q hsel hric hsec9
  have hrm : Ham3RmBound (I := I) P Q :=
    ham3_rm_bound (I := I) (M := M) hM g0 hg0 P Q hsel hric
  have hwindow : Ham3Window (I := I) P Q ham3_r0 :=
    ham3_r0_window (I := I) P Q hsel
  have hscalar :
      ∀ t : Real, t ∈ P.D.carrier → ∀ x : M, 0 < P.S.scalar t x :=
    ham3_scalar_pos (I := I) (M := M) h0omega hM g0 hg0 P hD
  exact ham3_const
    (I := I) (M := M) h0omega hM P hD Q hsel hrm hwindow
    hscalar hpinch

/-- Hamilton's positive-Ricci theorem through the provider-native HCG route.
Connectedness is part of the explicit `Closed3Manifold` hypothesis. -/
theorem ham3_main_hcg
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) ∧
      SphericalSpaceForm (I := I) (M := M) := by
  have hconst : AdmitsConstPosSec (I := I) (M := M) :=
    ham3_const_hcg (I := I) (M := M) hM hpos
  exact ⟨hconst, (ham3_equiv (I := I) (M := M) hM).1 hconst⟩

/-- A metric-compactness base for the Hamilton time-zero source yields a
constant-positive-sectional-curvature metric on the original manifold. -/
theorem ham3_const_of_base
    {omega : Real} (h0omega : 0 < omega)
    (hM : Closed3Manifold (I := I) (M := M))
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (hD : P.D =
      DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen
        0 omega h0omega)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    (hrm : Ham3RmBound (I := I) P Q)
    (hwindow : Ham3Window (I := I) P Q ham3_r0)
    (hscalar : forall t : Real, t ∈ P.D.carrier →
      forall x : M, 0 < P.S.scalar t x)
    (hpinch : Ham3PinchEstimate (I := I) P)
    (b : MetricCompactBase (I := I)
      ((ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow).atZero
        (I := I))) :
    AdmitsConstPosSec (I := I) (M := M) := by
  classical
  let X := ham3SourceSeq (I := I) h0omega P hD Q hsel hwindow
  change MetricCompactBase (I := I) (X.atZero (I := I)) at b
  have hcpl : SeqMetricComplete (I := I) (X.atZero (I := I)) := by
    refine ⟨?_⟩
    intro k
    change MetricComplete (I := I) ((X.term k).atTime (I := I) 0)
    dsimp only [MetricComplete, PointedFlowData.atTime]
    refine @complete_of_compact (X.term k).M ?_ ?_
    simpa only [X, ham3SourceSeq] using hM.1
  have hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M := by
    intro k
    change @ConnectedSpace (X.term k).M (X.term k).topology
    simpa only [X, ham3SourceSeq] using hM.2.1
  let canon : StepDCanonData (I := I) (X.atZero (I := I)) :=
    b.metricCanon hcpl hconn
  have hcanonConn :
      letI : TopologicalSpace canon.mc.limit.M := canon.mc.limit.topology
      ConnectedSpace canon.mc.limit.M := by
    simpa only [canon] using b.metricCanon_conn hcpl hconn
  obtain ⟨d, hlimCpl⟩ :=
    ham3_closed_upg (I := I) h0omega hM.1 P hD Q hsel hrm
      hwindow canon
  have hlimitConn :
      letI : TopologicalSpace d.data.L.M := d.data.L.topology
      ConnectedSpace d.data.L.M :=
    d.limit_conn hcanonConn
  have hzero : (0 : Real) ∈ X.D.carrier := by
    change (0 : Real) ∈ Set.Icc (-(ham3_r0 ^ 2)) 0
    exact ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_rfl⟩
  let mc := canon.mc.compSubseq d.φ d.hφ
  exact const0_of_cgh
    (I := I) (M := M) h0omega hM P hD Q hsel hscalar hpinch
    (ham3SourceLink (I := I) h0omega P hD Q hsel hwindow)
    hzero d.data.L mc.subseq mc.strictMono
    (Classical.choice d.data.converges) hlimCpl hlimitConn

/-- A compactness conclusion from the new HCG interface supplies the old
Hamilton Section 12 black-box conclusion. -/
theorem toHam3Exists
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hwindow : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier)
    (hreg : Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ X.D.regular)
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (hcompact : HamCGHConclusion (I := I) (M := M) P Q hsel X hsource) :
    Ham3CGHLimitExists (I := I) P Q hsel := by
  rcases hcompact with
    ⟨L, subseq, hsubseq, hconv, hcomplete, hconnected, htransfers⟩
  let Lh : Ham3CGHLimitData (I := I) M :=
    cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
      hsource.toOrig L subseq hsubseq hconv hcomplete
  change Ham3RicNonnegTransfer (I := I) (M := M) P Q hsel Lh /\
    LimitScalarPos (I := I) (M := M) Lh /\
    Ham3PinchTransfer (I := I) (M := M) P Q hsel Lh at htransfers
  rcases htransfers with ⟨hricTransfer, hscalarPos, hpinchTransfer⟩
  have hreal : Ham3SourceRealizes (I := I) (M := M) P Q hsel Lh :=
    Ham3SourceLink.realizes (I := I) (M := M) P Q hsel hsource L subseq
      hsubseq hconv hcomplete
  have hconnHam :
      Ham3LimitConnected (I := I) (M := M) Lh := by
    simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitConnected,
      cghToHam3] using
      hconnected
  have hbdHam :
      Ham3LimitBoundaryless (I := I) (M := M) Lh := by
    simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitBoundaryless,
      cghToHam3] using (inferInstance : I.Boundaryless)
  refine
    ⟨Lh, hreal, Lh.subseq_strict,
      hwindow, hreg, hconnHam, hbdHam, ?_,
      hricTransfer,
      baseScalarConv_of_smoothCGH (I := I) (M := M) P Q hsel hsource
        (hwindow (Set.mem_Icc.mpr ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_refl 0⟩))
        hsubseq hconv hcomplete,
      ⟨hscalarPos, hpinchTransfer⟩⟩
  simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitFlow,
    cghToHam3] using
    L.isSolution

end HCGCompactness
end DifferentialGeometry
