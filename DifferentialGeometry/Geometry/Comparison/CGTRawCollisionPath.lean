import DifferentialGeometry.Geometry.Comparison.CGTRawLiftOps

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- The flat loop obtained from two raw radial paths with a common image
endpoint. -/
noncomputable def rawCollisionPath
    (g : SmoothRiemannianMetric I M) (p : M) (u v : E)
    (huDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p)
    (hvDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p v) ∈ expDomain (I := I) g p)
    (hcollision :
      framedExpMap (I := I) g p u = framedExpMap (I := I) g p v) :
    Path p p :=
  (rawFlatPath (I := I) g p u huDom).trans
    ((rawFlatPath (I := I) g p v hvDom).cast rfl hcollision).symm

/-- A raw collision loop is C1 and constant near both endpoints. -/
theorem rawCollision_flat
    (g : SmoothRiemannianMetric I M) (p : M) (u v : E)
    (huDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p)
    (hvDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p v) ∈ expDomain (I := I) g p)
    (hcollision :
      framedExpMap (I := I) g p u = framedExpMap (I := I) g p v) :
    IsFlatC1Path (I := I)
      (rawCollisionPath (I := I) g p u v huDom hvDom hcollision) := by
  let pu := rawFlatPath (I := I) g p u huDom
  let pv : Path p (framedExpMap (I := I) g p u) :=
    (rawFlatPath (I := I) g p v hvDom).cast rfl hcollision
  have hpu : IsFlatC1Path (I := I) pu := by
    simpa only [pu] using rawFlatPath_flat (I := I) g p u huDom
  have hpv : IsFlatC1Path (I := I) pv := by
    have hflat := rawFlatPath_flat (I := I) g p v hvDom
    refine {
      c1 := ?_
      flat_zero := ?_
      flat_one := ?_ }
    · simpa only [pv, Path.extend_cast] using hflat.c1
    · simpa only [pv, Path.extend_cast] using hflat.flat_zero
    · simpa only [pv, Path.extend_cast, hcollision] using hflat.flat_one
  change IsFlatC1Path (I := I) (pu.trans pv.symm)
  exact hpu.trans hpv.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The length of a raw collision loop is the sum of the two radial endpoint
norms. -/
theorem rawCollision_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u v : E)
    (huDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p)
    (hvDom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p v) ∈ expDomain (I := I) g p)
    (hcollision :
      framedExpMap (I := I) g p u = framedExpMap (I := I) g p v) :
    pathLen (I := I)
        (rawCollisionPath (I := I) g p u v huDom hvDom hcollision) =
      ENNReal.ofReal (‖u‖ + ‖v‖) := by
  let pu := rawFlatPath (I := I) g p u huDom
  let pv : Path p (framedExpMap (I := I) g p u) :=
    (rawFlatPath (I := I) g p v hvDom).cast rfl hcollision
  have hpu : IsFlatC1Path (I := I) pu := by
    simpa only [pu] using rawFlatPath_flat (I := I) g p u huDom
  have hpv : IsFlatC1Path (I := I) pv := by
    have hflat := rawFlatPath_flat (I := I) g p v hvDom
    refine {
      c1 := ?_
      flat_zero := ?_
      flat_one := ?_ }
    · simpa only [pv, Path.extend_cast] using hflat.c1
    · simpa only [pv, Path.extend_cast] using hflat.flat_zero
    · simpa only [pv, Path.extend_cast, hcollision] using hflat.flat_one
  have hpuLen : pathLen (I := I) pu = ENNReal.ofReal ‖u‖ := by
    simpa only [pu] using rawFlatPath_len (I := I) g hEnorm p u huDom
  have hpvLen : pathLen (I := I) pv = ENNReal.ofReal ‖v‖ := by
    simpa only [pathLen, pv, Path.extend_cast] using
      rawFlatPath_len (I := I) g hEnorm p v hvDom
  change pathLen (I := I) (pu.trans pv.symm) = _
  rw [pathLen_trans hpu hpv.symm, pathLen_symm hpv, hpuLen, hpvLen,
    ENNReal.ofReal_add (norm_nonneg u) (norm_nonneg v)]

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
