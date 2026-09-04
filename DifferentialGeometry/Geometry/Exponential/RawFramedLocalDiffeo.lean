import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

/-- The raw framed exponential is smooth at every model vector whose framed
velocity belongs to the raw exponential domain. -/
theorem framedExp_mdiffAt
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(Real, E) I ∞ (framedExpMap (I := I) g p) z := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (L : E → E) z := L.contDiff.contMDiff.contMDiffAt
  have hexp := expMap_contMDiffAt (I := I) g p hz
  simpa only [framedExpMap, L] using hexp.comp z hframe

/-- The derivative of the raw framed exponential is the raw exponential
derivative composed with the fixed normal-frame isometry. -/
theorem mfderiv_framedMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z =
      (mfderiv 𝓘(Real, E) I
        (fun u : E => expMap (I := I) g p
          (show TangentSpace I p from u))
        (normalFrame (I := I) g p z)).comp
          (normalFrame (I := I) g p).toContinuousLinearMap := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  let F : E → M := fun u =>
    expMap (I := I) g p (show TangentSpace I p from u)
  have hF : MDifferentiableAt 𝓘(Real, E) I F (L z) :=
    (expMap_contMDiffAt (I := I) g p hz).mdifferentiableAt (by decide)
  have hL : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
      (fun w : E => L w) z :=
    L.contMDiff.mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp
    (I := 𝓘(Real, E)) (I' := 𝓘(Real, E)) (I'' := I)
    z hF hL
  have hLderiv :
      mfderiv 𝓘(Real, E) 𝓘(Real, E) (fun w : E => L w) z = L := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  change mfderiv 𝓘(Real, E) I (F ∘ fun w : E => L w) z =
    (mfderiv 𝓘(Real, E) I F (L z)).comp L
  exact hchain

/-- Pointwise raw-domain membership and nonsingular framed exponential
derivatives give a local diffeomorphism on an open model-space set. -/
theorem framedExp_locdiff
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set E}
    (hU : IsOpen U)
    (hdom : ∀ z ∈ U,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p)
    (hinj : ∀ z ∈ U, Function.Injective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)) :
    IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
  have hsmooth : ContMDiffOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
    intro z hz
    exact (framedExp_mdiffAt (I := I) g p (hdom z hz)).contMDiffWithinAt
  apply DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty
    hU hsmooth
  intro z hz
  have hDinj := hinj z hz
  have hDsurj : Function.Surjective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z) :=
    LinearMap.surjective_of_injective hDinj
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)
      (LinearMap.ker_eq_bot.mpr hDinj)
      (LinearMap.range_eq_top.mpr hDsurj)
  have hDinv :
      (mfderiv 𝓘(Real, E) I
        (framedExpMap (I := I) g p) z).IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  exact DifferentialGeometry.Coordinates.written_fderiv_inv
    ((framedExp_mdiffAt (I := I) g p (hdom z hz)).mdifferentiableAt (by simp))
    hDinv

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
