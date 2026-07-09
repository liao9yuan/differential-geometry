import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.HamiltonCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonPositiveRicci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Adapter To The Hamilton Positive Ricci Endpoint

This file does not change `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.lean`.  It only explains how a
new HCG compactness conclusion supplies the existing `Ham3CGHLimitExists`
black-box output used by `ham3_cgh_limit`.
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

/-- Forget the new HCG convergence fields down to the current Section 12 limit
data record. -/
def pointedFlowToHam3
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (L : PointedFlowData.{u, uE, uH} (I := I) D) (subseq : Nat -> Nat) :
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
  basepoint := L.basepoint
  D := D
  S := L.S
  subseq := subseq

/-- Hamilton-specific compactness conclusion.

This strengthens the generic `CompactnessConclusion` with the global topology
facts needed by Hamilton Section 12.  These facts belong to the compactness
construction/source-topology transfer layer, not to the final Hamilton adapter
as per-limit ad hoc assumptions. -/
def HamCGHConclusion (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D, exists subseq : Nat -> Nat,
    StrictMono subseq /\
      Nonempty.{max (max uE uH) u + 1}
        (SmoothCGHConverges (I := I) X L subseq) /\
      (letI : TopologicalSpace L.M := L.topology
       ConnectedSpace L.M) /\
      (letI : TopologicalSpace L.M := L.topology
       letI : ChartedSpace H L.M := L.charted
       letI : IsManifold I ∞ L.M := L.smooth
       I.Boundaryless)

/-- Upstream topology transfer package for Hamilton compactness.  The adapter
only consumes this package; its producer belongs to the CGH construction layer. -/
structure HamCGHTopology (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  lift : CompactnessConclusion (I := I) X -> HamCGHConclusion (I := I) X

/-- The source pointed-flow sequence realizes the Hamilton rescaled scalar
curvature at its time-zero basepoints.

This is a source-realization input, not a convergence assumption: it identifies
the basepoint scalar functions of the generic HCG sequence `X` with the
Hamilton rescaled quantities built from `(P,Q)`. -/
def Ham3BaseScalarSeq
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.scalar 0 (X.term i).basepoint =
      ham3RescaledScalar (I := I) P Q i 0 (Q.point i)

/-- Hamilton's geometric noncollapsing package supplies the legacy HCG
`NoncollapseInput` volume slot. -/
noncomputable def noncollapseInput_of_ham3
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {kappa r : Real}
    (hdim : Module.finrank Real E = 3)
    (h : Ham3Noncollapse (I := I) (M := M) P Q kappa r) :
    NoncollapseInput (I := I) X := by
  classical
  let hunitEx :=
    DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3Noncollapse.unitVolLower
      (I := I) (M := M) h
  let unitVolume : Nat -> Real := Classical.choose hunitEx
  let hNEx :
      ∃ N : Nat, ∀ i : Nat, N <= i -> kappa * r ^ 3 <= unitVolume i :=
    Classical.choose_spec hunitEx
  let N : Nat := Classical.choose hNEx
  have hunit : ∀ i : Nat, N <= i -> kappa * r ^ 3 <= unitVolume i :=
    Classical.choose_spec hNEx
  let volumeAtBase : Nat -> Real :=
    fun i : Nat => if N <= i then unitVolume i else kappa * r ^ 3
  refine
    { kappa := kappa
      radius := r
      volumeAtBase := volumeAtBase
      kappa_pos := h.1
      radius_pos := h.2.1
      volume_lower := ?_ }
  intro i
  by_cases hi : N <= i
  · have hvol : kappa * r ^ 3 <= volumeAtBase i := by
      dsimp [volumeAtBase]
      simp [hi, hunit i hi]
    simpa [hdim] using hvol
  · dsimp [volumeAtBase]
    simp [hi, hdim]

/-- Scalar pullback convergence plus basepoint preservation gives the
Hamilton basepoint scalar-convergence datum.  Scalar pullback convergence is
quantified over carrier times, so time `0` must lie on the common flow
interval (`h0`); in the Section 12 setup this follows from the window
hypothesis `Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier`. -/
theorem baseScalarConv_of_smoothCGH
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (hseq : Ham3BaseScalarSeq (I := I) (M := M) P Q X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (hconv : SmoothCGHConverges (I := I) X L subseq) :
    Ham3LimitBaseScalarConv (I := I) (M := M) P Q
      (pointedFlowToHam3 (I := I) (M := M) L subseq) := by
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
    _ = ham3RescaledScalar (I := I) P Q (subseq k) 0
        (Q.point (subseq k)) := by
          simpa using hseq (subseq k)

/-- A compactness conclusion from the new HCG interface supplies the old
Hamilton Section 12 black-box conclusion. -/
theorem toHam3Exists
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hwindow : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier)
    (hreg : Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ X.D.regular)
    (hbaseSeq : Ham3BaseScalarSeq (I := I) (M := M) P Q X)
    (hricTransfer :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        Ham3RicNonnegTransfer (I := I) (M := M) P Q
          (pointedFlowToHam3 (I := I) (M := M) L subseq))
    (hpinchTransfer :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        Ham3PinchTransfer (I := I) (M := M) P Q
          (pointedFlowToHam3 (I := I) (M := M) L subseq))
    (hscalarPos :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        LimitScalarPos (I := I) (M := M)
          (pointedFlowToHam3 (I := I) (M := M) L subseq))
    (hcompact : HamCGHConclusion (I := I) X) :
    Ham3CGHLimitExists (I := I) P Q := by
  rcases hcompact with ⟨L, subseq, hsubseq, hconv, hconnected, hboundaryless⟩
  rcases hconv with ⟨hconv⟩
  have hconnHam :
      Ham3LimitConnected (I := I) (M := M)
        (pointedFlowToHam3 (I := I) (M := M) L subseq) := by
    simpa [DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitConnected, pointedFlowToHam3] using
      hconnected
  have hbdHam :
      Ham3LimitBoundaryless (I := I) (M := M)
        (pointedFlowToHam3 (I := I) (M := M) L subseq) := by
    simpa [DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitBoundaryless, pointedFlowToHam3] using
      hboundaryless
  refine
    ⟨pointedFlowToHam3 (I := I) (M := M) L subseq, hsubseq,
      hwindow, hreg, hconnHam, hbdHam, ?_,
      hricTransfer L subseq,
      baseScalarConv_of_smoothCGH (I := I) (M := M) P Q hbaseSeq
        (hwindow (Set.mem_Icc.mpr ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_refl 0⟩))
        hconv,
      ⟨hscalarPos L subseq, hpinchTransfer L subseq⟩⟩
  simpa [DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitFlow, pointedFlowToHam3] using
    L.isSolution

/-- The Hamilton Section 12 CGH output follows from the Theorem 3.10
injectivity-radius compactness interface plus the Hamilton-specific transfer
producers. -/
theorem ham3OfCompactSol
    [I.Boundaryless]
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X)
    (hinj : InjInput (I := I) X)
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hflowCurv : SpacetimeCurvBound (I := I) X)
    (hflowInj : FlowBaseInjBound (I := I) X)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : SmoothFlowLimitInput (I := I) X)
    (htop : HamCGHTopology (I := I) X)
    (hwindow : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier)
    (hreg : Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ X.D.regular)
    (hbaseSeq : Ham3BaseScalarSeq (I := I) (M := M) P Q X)
    (hricTransfer :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        Ham3RicNonnegTransfer (I := I) (M := M) P Q
          (pointedFlowToHam3 (I := I) (M := M) L subseq))
    (hpinchTransfer :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        Ham3PinchTransfer (I := I) (M := M) P Q
          (pointedFlowToHam3 (I := I) (M := M) L subseq))
    (hscalarPos :
      forall (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (subseq : Nat -> Nat),
        LimitScalarPos (I := I) (M := M)
          (pointedFlowToHam3 (I := I) (M := M) L subseq)) :
    Ham3CGHLimitExists (I := I) P Q :=
  toHam3Exists (I := I) (M := M) P Q hwindow hreg
    hbaseSeq hricTransfer hpinchTransfer hscalarPos
    (htop.lift
      (compactnessSol (I := I) X hcomplete hcurv hinj
        hcomplete0 hflowCurv hflowInj hderiv hflow))

end HCGCompactness
end DifferentialGeometry
