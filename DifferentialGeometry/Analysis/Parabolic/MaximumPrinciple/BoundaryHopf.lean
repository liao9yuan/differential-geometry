import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Strong
import DifferentialGeometry.Geometry.Boundary.NormalDerivative

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Set
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] hI in
private theorem boundaryHopf_hasDerivAt_comp_mfderiv
    (f : M → Real) (gamma : Real → M) (t : Real)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f (gamma t))
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma t) :
    HasDerivAt (fun s => f (gamma s))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I (modelWithCornersSelf Real Real) f (gamma t)
          (mfderiv (modelWithCornersSelf Real Real) I gamma t 1))) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hcomp := hf.hasMFDerivAt.comp t hgamma.hasMFDerivAt
  have hcomp' := hcomp.hasFDerivAt
  convert hcomp' using 1
  change ContinuousLinearMap.toSpanSingleton Real
      (((mfderiv I (modelWithCornersSelf Real Real) f (gamma t)).comp
        (mfderiv (modelWithCornersSelf Real Real) I gamma t)) 1) = _
  exact ContinuousLinearMap.toSpanSingleton_apply_map_one
    (R₁ := Real) (M₂ := Real) _

theorem scalar_hopf_boundary_point_of_barrier_with_boundary
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKinterior : interior K ⊆ I.interior M)
    (u v : Real → M → Real)
    (hcont : ContinuousOn (fun q : Real × M => u q.1 q.2 - v q.1 q.2)
      (Set.Icc 0 T ×ˢ K))
    (hinit : ∀ x ∈ K, 0 ≤ u 0 x - v 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K,
      0 ≤ u t x - v t x)
    (htime : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => u s x - v s x) (Set.Icc 0 T) t)
    (hmdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I 𝓘(Real, Real) (fun y => u t y - v t y) x)
    (hgrad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t)
        (fun z => u t z - v t z) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      u t x - v t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - v s y) t x)
    {p : BoundaryManifold I M} (hp : (p : M) ∈ frontier K)
    (gamma : Real → M) {a dv : Real} (ha : 0 < a)
    (hgamma0 : gamma 0 = (p : M))
    (hgamma : Set.MapsTo gamma (Set.Icc 0 a) K)
    (heq : u T (p : M) = v T (p : M))
    (hu_mdiff : MDifferentiableAt I 𝓘(Real, Real) (u T) (p : M))
    (hgamma_mdiff : MDifferentiableAt 𝓘(Real, Real) I gamma 0)
    (hgamma_velocity : mfderiv 𝓘(Real, Real) I gamma 0 1 =
      inwardCoord (M := M) p)
    (hv_deriv : HasDerivAt (fun s => v T (gamma s)) dv 0)
    (hdv : 0 < dv)
    (hmin : IsLocalMin
      (fun q : BoundaryManifold I M => u T (q : M)) p) :
    outwardNormalDerivative (M := M) (G.metric T) (u T) p < 0 := by
  have hu_deriv : HasDerivAt (fun s => u T (gamma s))
      ((G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (u T) (p : M))
        (inwardCoord (M := M) p)) 0 := by
    have hcurve := boundaryHopf_hasDerivAt_comp_mfderiv
      (I := I) (u T) gamma 0
      (by simpa [hgamma0] using hu_mdiff) hgamma_mdiff
    rw [hgamma0] at hcurve
    convert hcurve using 1
    change (G.metric T).inner (p : M)
        (gradientFun (I := I) (G.metric T) (u T) (p : M))
        (inwardCoord (M := M) p) =
      mfderiv I 𝓘(Real, Real) (u T) (p : M)
        (mfderiv 𝓘(Real, Real) I gamma 0 1)
    rw [hgamma_velocity, inner_gradientFun]
  have hinward := scalar_hopf_boundary_point_of_barrier_of_isInteriorPoint
    (I := I) G T hT X hK hKne hKinterior u v hcont hinit hboundary
      htime hmdiff hgrad hoperator hp gamma ha hgamma0 hgamma heq
      hu_deriv hv_deriv hdv
  exact
    outwardNormalDerivative_neg_of_inner_gradient_inwardCoord_pos_at_local_min
      (M := M) (G.metric T) hmin hu_mdiff hinward

end

end DifferentialGeometry.Integral.Connection
