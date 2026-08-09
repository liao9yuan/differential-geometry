import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompleteness

set_option autoImplicit false

/-!
# Completeness of fixed-window limit metrics

A positive lower bound for the selected metric sequence makes every time slice
of the fixed-window limit complete whenever the reference pointed manifold is
complete.
-/

noncomputable section

open Set Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace ConvOut

/-- A fixed-window limit slice is complete when the reference metric is
complete and the selected sequence uniformly dominates a positive multiple of
that metric. -/
theorem complete_at
    (hP : MetricComplete (I := I) P)
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ c : Real}
    (co : ConvOut (I := I) Φ P.metric bf hsrc htgt β ψ)
    (hc : 0 < c)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (x : P.M) (v : TangentSpace I x),
          c * P.metric.inner x v v ≤
            (gSeqExt (I := I) Φ P.metric bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Icc β ψ) :
    MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  exact MetricComplete.complete_of_lower P hP (co.gInf t) c hc
    (ConvOut.lower_of (I := I) (Φ := Φ) co hseq t ht)

end ConvOut
end HCGCompactness
end DifferentialGeometry

end
