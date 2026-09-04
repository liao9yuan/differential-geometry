import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Exponential.LiftLength
import DifferentialGeometry.Geometry.Exponential.RawFramedLocalDiffeo

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- Gauss pullback gives the radial Cauchy bound for the raw framed
exponential wherever the full radial segment stays in its domain. -/
private theorem rawFrame_radial_ne
    [NeZero (Module.finrank Real E)]
    (g : SmoothRiemannianMetric I M) (p : M) (z v : E)
    (hdom : ∀ t ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    |Inner.inner Real z v| ≤
      ‖z‖ * Real.sqrt
        (g.inner (framedExpMap (I := I) g p z)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)) := by
  have hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p := by
    simpa using hdom 1 ⟨by norm_num, le_rfl⟩
  let U : TangentSpace I (framedExpMap (I := I) g p z) :=
    mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z z
  let W : TangentSpace I (framedExpMap (I := I) g p z) :=
    mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z v
  have hpair :
      g.inner (framedExpMap (I := I) g p z) U W =
        Inner.inner Real z v := by
    simp only [U, W]
    rw [framedExpMap_apply, mfderiv_framedMap (I := I) g p hz]
    simpa only [normalFrame_inner] using
      raw_gauss_pullback (I := I) g p
        (v := normalFrame (I := I) g p z)
        (w := normalFrame (I := I) g p v) hdom
  have hspeed :
      Real.sqrt
          (g.inner (framedExpMap (I := I) g p z) U U) = ‖z‖ := by
    simp only [U]
    rw [framedExpMap_apply, mfderiv_framedMap (I := I) g p hz]
    change Real.sqrt
        (g.inner
          (expMap (I := I) g p (normalFrame (I := I) g p z))
          (mfderiv 𝓘(Real, E) I
            (fun u : E => expMap (I := I) g p
              (show TangentSpace I p from u))
            (normalFrame (I := I) g p z)
            (normalFrame (I := I) g p z))
          (mfderiv 𝓘(Real, E) I
            (fun u : E => expMap (I := I) g p
              (show TangentSpace I p from u))
            (normalFrame (I := I) g p z)
            (normalFrame (I := I) g p z))) = ‖z‖
    rw [raw_gauss_pullback (I := I) g p
      (v := normalFrame (I := I) g p z)
      (w := normalFrame (I := I) g p z) hdom]
    exact normalFrame_sqrt (I := I) g p z
  calc
    |Inner.inner Real z v| =
        |g.inner (framedExpMap (I := I) g p z) U W| := by rw [hpair]
    _ ≤ Real.sqrt
          (g.inner (framedExpMap (I := I) g p z) U U) *
        Real.sqrt
          (g.inner (framedExpMap (I := I) g p z) W W) :=
      abs_metric_inner_le_sqrt_metric_quadratic
        (I := I) (M := M) g (framedExpMap (I := I) g p z) U W
    _ = ‖z‖ * Real.sqrt
        (g.inner (framedExpMap (I := I) g p z)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)) := by
      rw [hspeed]

/-- Gauss pullback gives the radial Cauchy bound for the raw framed
exponential wherever the full radial segment stays in its domain. -/
theorem rawFrame_radial_le
    (g : SmoothRiemannianMetric I M) (p : M) (z v : E)
    (hdom : ∀ t ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    |Inner.inner Real z v| ≤
      ‖z‖ * Real.sqrt
        (g.inner (framedExpMap (I := I) g p z)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)
          (mfderiv 𝓘(Real, E) I
            (framedExpMap (I := I) g p) z v)) := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.1 hdim
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simp
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    exact rawFrame_radial_ne (I := I) g p z v hdom

/-- A path lifted through the raw framed exponential cannot have endpoint norm
larger than the Riemannian length of its image, provided each lifted radial
segment stays in the raw exponential domain. -/
theorem rawLift_norm_le
    [(x : M) → NormedAddCommGroup (TangentSpace I x)]
    [(x : M) → NormedSpace Real (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {η : Real → E} {a b : Real}
    (hab : a ≤ b) (hηa : η a = 0)
    (hη : ContDiffOn Real 1 η (Set.Icc a b))
    (hdom : ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) g p (η x)) ∈ expDomain (I := I) g p) :
    ENNReal.ofReal ‖η b‖ ≤
      Manifold.pathELength I
        ((framedExpMap (I := I) g p) ∘ η) a b := by
  letI : CompleteSpace E := FiniteDimensional.complete Real E
  apply lift_norm_le (J := I) g hEnorm
    (framedExpMap (I := I) g p) hab hηa hη
  · intro x hx
    exact (framedExp_mdiffAt (I := I) g p
      (by simpa using hdom x hx 1 ⟨by norm_num, le_rfl⟩)).of_le (by norm_num)
  · intro v
    have h0 : normalFrame (I := I) g p (0 : E) ∈
        expDomain (I := I) g p := by
      simpa using zero_mem_expDomain (I := I) g p
    have hF0 : framedExpMap (I := I) g p (0 : E) = p := by
      rw [framedExpMap_apply, map_zero]
      exact expMap_zero (I := I) g p
    have hD0 :
        mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) (0 : E) =
          (normalFrame (I := I) g p).toContinuousLinearMap := by
      rw [mfderiv_framedMap (I := I) g p h0, map_zero]
      have hraw := mfderiv_expMap_at_zero (I := I) g p
      have hcomp := congrArg
        (fun D : E →L[Real] E =>
          D.comp (normalFrame (I := I) g p).toContinuousLinearMap) hraw
      simpa only [ContinuousLinearMap.id_comp] using hcomp
    rw [hF0, hD0]
    exact normalFrame_sqrt (I := I) g p v
  · intro x hx v
    exact rawFrame_radial_le (I := I) g p (η x) v (hdom x hx)

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
