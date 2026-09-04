import DifferentialGeometry.Geometry.Comparison.CGTRawTransport
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Metric Set
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
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
/-- Raw loop transport does not increase pullback distance when supplied with
a distance-realizing core path between the source points. -/
theorem rawTransport_nonexp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hR : 0 < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ u ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        u • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    {x y : rawPullBall (E := E) R}
    (hx : x ∈ rawCore (E := E) R a)
    (hy : y ∈ rawCore (E := E) R a)
    (j : Path x y)
    (hj : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 j.extend
      (Set.Icc (0 : Real) 1))
    (hjcore : ∀ u : Real, j.extend u ∈ rawCore (E := E) R a)
    (hjlen :
      letI : RiemannianBundle
          (fun z : rawPullBall (E := E) R ↦
            TangentSpace 𝓘(Real, E) z) :=
        ⟨(rawPullMetric (I := I) g p hloc).toRiemannianMetric⟩
      Manifold.pathELength 𝓘(Real, E) j.extend 0 1 =
        riemannianEDistOf (I := 𝓘(Real, E))
          (rawPullMetric (I := I) g p hloc) x y) :
    let gPull := rawPullMetric (I := I) g p hloc
    letI : RiemannianBundle
        (fun z : rawPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : rawPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (rawPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (rawPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
    dist
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen x hx)
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen y hy) ≤
      dist x y := by
  classical
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI pullNormedAdd (z : rawPullBall (E := E) R) :
      NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI pullNormed (z : rawPullBall (E := E) R) :
      NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI pullENormSmul : ∀ z : rawPullBall (E := E) R,
      ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : rawPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : ConnectedSpace (rawPullBall (E := E) R) :=
    Subtype.connectedSpace (isConnected_ball hR)
  letI : MetricSpace (rawPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
  let η : Real → rawPullBall (E := E) R :=
    fun u => rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen (j.extend u) (hjcore u)
  have hcurve := rawTransport_curve (I := I) g hEnorm p hL ha hfit
    hdom hloc c hc hcLen hj hjcore
  have hη0 :
      η 0 = rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen x hx := by
    simp only [η, Path.extend_zero]
  have hη1 :
      η 1 = rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen y hy := by
    simp only [η, Path.extend_one]
  have hedPath :
      riemannianEDist 𝓘(Real, E) (η 0) (η 1) ≤
        Manifold.pathELength 𝓘(Real, E) η 0 1 :=
    @Manifold.riemannianEDist_le_pathELength
      E _ _ E _ 𝓘(Real, E) (rawPullBall (E := E) R)
      _ _ _ pullENormSmul (η 0) (η 1) 0 1 η
      hcurve.1 rfl rfl zero_le_one
  have hed :
      riemannianEDist 𝓘(Real, E)
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen x hx)
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen y hy) ≤
        riemannianEDist 𝓘(Real, E) x y := by
    rw [← hη0, ← hη1]
    calc
      riemannianEDist 𝓘(Real, E) (η 0) (η 1) ≤
          Manifold.pathELength 𝓘(Real, E) η 0 1 := hedPath
      _ = Manifold.pathELength 𝓘(Real, E) j.extend 0 1 := hcurve.2
      _ = riemannianEDistOf (I := 𝓘(Real, E)) gPull x y := hjlen
      _ = riemannianEDist 𝓘(Real, E) x y := rfl
  have hedReal :
      (riemannianEDist 𝓘(Real, E)
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen x hx)
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen y hy)).toReal ≤
      (riemannianEDist 𝓘(Real, E) x y).toReal :=
    ENNReal.toReal_mono
      (riemannianEDist_ne_top (I := 𝓘(Real, E)) x y) hed
  calc
    dist
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen x hx)
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen y hy) =
        (riemannianEDist 𝓘(Real, E)
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen x hx)
          (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
            c hc hcLen y hy)).toReal :=
      HopfRinow.riemMetric_dist_eq
        (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R) _ _
    _ ≤ (riemannianEDist 𝓘(Real, E) x y).toReal := hedReal
    _ = dist x y :=
      (HopfRinow.riemMetric_dist_eq
        (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R) x y).symm

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
