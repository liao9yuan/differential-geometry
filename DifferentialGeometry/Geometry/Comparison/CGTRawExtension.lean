import DifferentialGeometry.Geometry.Comparison.CGTRawPullback
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawPullBall (E := E) R).isOpen)

private noncomputable def rawCut (R : Real) (hR : 0 < R) :
    ContDiffBump (0 : E) :=
  ⟨3 * R / 4, 7 * R / 8, by linarith, by linarith⟩

private theorem rawCut_smooth (R : Real) (hR : 0 < R) :
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (rawCut (E := E) R hR : E → Real) :=
  (rawCut (E := E) R hR).contDiff.contMDiff

private theorem rawCut_range (R : Real) (hR : 0 < R) (z : E) :
    rawCut (E := E) R hR z ∈ Set.Icc (0 : Real) 1 :=
  ⟨(rawCut (E := E) R hR).nonneg,
    (rawCut (E := E) R hR).le_one⟩

private theorem rawCut_support (R : Real) (hR : 0 < R) :
    tsupport (rawCut (E := E) R hR : E → Real) ⊆
      (rawPullBall (E := E) R : Set E) := by
  rw [(rawCut (E := E) R hR).tsupport_eq]
  change Metric.closedBall (0 : E) (7 * R / 8) ⊆
    Metric.ball (0 : E) R
  exact Metric.closedBall_subset_ball (by linarith)

private theorem rawCut_compact (R : Real) (hR : 0 < R) :
    IsCompact (tsupport (rawCut (E := E) R hR : E → Real)) := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  rw [(rawCut (E := E) R hR).tsupport_eq]
  exact isCompact_closedBall (0 : E) (7 * R / 8)

private theorem rawCut_one (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    rawCut (E := E) R hR z = 1 :=
  (rawCut (E := E) R hR).one_of_mem_closedBall hz

omit [InnerProductSpace Real E] [FiniteDimensional Real E] in
private theorem rawClosed_subset (R : Real) (hR : 0 < R) :
    Metric.closedBall (0 : E) (3 * R / 4) ⊆
      (rawPullBall (E := E) R : Set E) :=
  Metric.closedBall_subset_ball (by linarith)

/-- The inner model-space ball on which the raw pullback and its complete
extension agree. -/
def rawAgree (R : Real) : Opens (rawPullBall (E := E) R) :=
  ⟨Subtype.val ⁻¹' Metric.ball (0 : E) (3 * R / 4),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawAgree (E := E) R).isOpen)

/-- The raw framed-exponential pullback metric, extended to a complete metric
on the whole model space. -/
noncomputable def rawExtMetric
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) E :=
  (flatModelMetric E).bumpExtendOpen
    (rawPullBall (E := E) R)
    (rawPullMetric (I := I) g p hloc)
    (rawCut (E := E) R hR : E → Real)
    (rawCut_smooth (E := E) R hR)
    (rawCut_range (E := E) R hR)
    (rawCut_support (E := E) R hR)

/-- The complete extension agrees pointwise with the raw pullback metric on
the centered closed agreement ball. -/
theorem rawExt_inner
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {z : E} (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4))
    (v w : E) :
    (rawExtMetric (I := I) g p hR hloc).inner z v w =
      (rawPullMetric (I := I) g p hloc).inner
        ⟨z, rawClosed_subset (E := E) R hR hz⟩ v w := by
  simpa only [rawExtMetric] using
    bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
      (flatModelMetric E) (rawPullBall (E := E) R)
      (rawPullMetric (I := I) g p hloc)
      (rawCut (E := E) R hR : E → Real)
      (rawCut_smooth (E := E) R hR)
      (rawCut_range (E := E) R hR)
      (rawCut_support (E := E) R hR)
      (Metric.closedBall (0 : E) (3 * R / 4))
      (fun z hz => rawCut_one (E := E) R hR hz)
      (rawClosed_subset (E := E) R hR) z hz v w

/-- On the centered open agreement ball, restriction of the complete extension
is exactly restriction of the raw pullback metric. -/
theorem rawExt_restrict
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    ((rawExtMetric (I := I) g p hR hloc).restrictOpen
        (I := 𝓘(Real, E)) (rawPullBall (E := E) R)).restrictOpen
          (I := 𝓘(Real, E)) (rawAgree (E := E) R) =
      (rawPullMetric (I := I) g p hloc).restrictOpen
        (I := 𝓘(Real, E)) (rawAgree (E := E) R) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  have hz :
      ((z : rawPullBall (E := E) R) : E) ∈
        Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall z.2
  simpa only using rawExt_inner (I := I) g p hR hloc hz v w

/-- The raw pullback extension is complete because it equals the complete flat
model metric outside a compact set. -/
theorem rawExt_complete
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    RiemannianMetricComplete (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) := by
  simpa only [rawExtMetric] using
    RiemannianMetricComplete.bumpExtend_complete
      (I := 𝓘(Real, E)) (flatModelMetric E)
      (RiemannianMetricComplete.flatModel_complete (E := E))
      (rawPullBall (E := E) R)
      (rawPullMetric (I := I) g p hloc)
      (rawCut (E := E) R hR : E → Real)
      (rawCut_smooth (E := E) R hR)
      (rawCut_range (E := E) R hR)
      (rawCut_support (E := E) R hR)
      (rawCut_compact (E := E) R hR)

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
