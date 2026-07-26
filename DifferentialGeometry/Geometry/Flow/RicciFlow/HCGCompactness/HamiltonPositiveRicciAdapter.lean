import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFlowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CurvTowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonPositiveRicci
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

open scoped Manifold ContDiff
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
