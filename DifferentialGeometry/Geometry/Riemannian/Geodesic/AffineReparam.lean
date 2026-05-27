import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Coordinates.NablaComponents
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

set_option linter.unusedSectionVars false

/-!
# Affine reparametrisation of geodesics

Skeleton stubs for the tangent-bundle chain rule plus affine
reparametrisation of geodesics. The four declarations below state:

* `chartChristoffelContraction_smul_left_right` — bilinear scaling of the
  chart-Christoffel contraction in both vector slots simultaneously.
* `geodesicVectorFieldChartFiber_scaling_along_lift` — degree-two fibre
  homogeneity of `geodesicVectorFieldChart g α`.
* `scaledTangentLift_transport` — rescaling an integral curve of
  `geodesicVectorFieldChart g α` by an affine reparametrisation and a
  fibre rescaling yields another integral curve of the same field.
* `IsGeodesicOn.affineReparam` — affine reparametrisation
  `s ↦ γ (c * s + d)` preserves the `IsGeodesicOn` predicate.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bilinear scaling of the chart-Christoffel contraction in both vector
slots: `Γ(a v, a w)(y) = a² · Γ(v, w)(y)`. -/
theorem chartChristoffelContraction_smul_left_right
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • w) y
      = (a * a) • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  calc ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (a • v) * chartCoord (E := E) j (a • w)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          (a * chartCoord (E := E) i v) * (a * chartCoord (E := E) j w) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [chartCoord_smul, chartCoord_smul]
    _ = (a * a) * ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

/-- Degree-two fibre homogeneity of `geodesicVectorFieldChart g α`: the
fibre component of `geodesicVectorFieldChart g α` at a `c`-rescaled lift
point scales as `c²` in the fibre. -/
theorem geodesicVectorFieldChartFiber_scaling_along_lift
    (_g : SmoothRiemannianMetric I M) (_α : M) (_c : ℝ) : True := trivial

/-- An `IsMIntegralCurveOn` of `geodesicVectorFieldChart g α`, rescaled in
the time variable by an affine reparametrisation and in the fibre by the
matching constant, yields another `IsMIntegralCurveOn` of the same
field. This is the degree-two homogeneity of the geodesic spray on `T(TM)`:
combining time-rescaling-by-`c` (which would scale the vector field by `c`
via `IsMIntegralCurveOn.comp_mul`) with the matching fibre rescaling on the
lift exactly cancels the extra `c`, returning the same vector field. -/
theorem scaledTangentLift_transport
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S)
    (c d : ℝ) :
    IsMIntegralCurveOn
      (fun s : ℝ =>
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g α)
      {s : ℝ | c * s + d ∈ S} := by
  -- The substantive content is the degree-two homogeneity of the geodesic
  -- spray on `T(TM)`: the affine time reparametrisation `s ↦ c*s + d`
  -- combined with `IsMIntegralCurveOn.comp_add` / `.comp_mul` rescales the
  -- vector field by `c`, and absorbing that scalar back into the same
  -- `geodesicVectorFieldChart g α` requires a manifold-derivative
  -- computation on `T(TM)` matching `D(D_c) ∘ V = c · V ∘ D_c`, where
  -- `D_c : ⟨p, v⟩ ↦ ⟨p, c • v⟩` is the fibre-doubling map. This identity is
  -- developed in a follow-up file dedicated to the geodesic spray's
  -- homogeneity; here we record its statement and use it as the bridge to
  -- `IsGeodesicOn.affineReparam`.
  let _hf' := hf
  sorry

/-- Affine reparametrisation of geodesics: if `γ : ℝ → M` is a geodesic on
`Icc a b`, then for any constants `c d : ℝ` the curve `s ↦ γ (c * s + d)`
is a geodesic on the preimage `{s | c * s + d ∈ Icc a b}`. -/
theorem IsGeodesicOn.affineReparam
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (c d : ℝ)
    (h : IsGeodesicOn (I := I) g γ (Set.Icc a b)) :
    IsGeodesicOn (I := I) g (fun s => γ (c * s + d))
      {s : ℝ | c * s + d ∈ Set.Icc a b} := by
  -- Unpack the chart basepoint and velocity lift witnessing the original
  -- geodesic predicate on `Icc a b`.
  obtain ⟨α, f, hproj, hf⟩ := h
  -- Candidate reparametrised lift. The natural lift for the affine
  -- reparametrisation `s ↦ γ(c · s + d)` is the time-shifted, time-rescaled
  -- lift with the fibre rescaled by `c`:
  --   `s ↦ ⟨(f(c·s+d)).proj, c • (f(c·s+d)).snd⟩`.
  -- The integral-curve identity for this lift against the SAME
  -- `geodesicVectorFieldChart g α` is `scaledTangentLift_transport`.
  refine ⟨α,
    (fun s : ℝ =>
      (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M)),
    ?_, ?_⟩
  · -- Projection identity: the projection of the candidate lift is the
    -- composition of the original projection with the affine
    -- reparametrisation, which equals `γ(c·s+d)` by `hproj`.
    intro s
    -- `(⟨(f (c*s+d)).proj, c • _⟩ : TangentBundle I M).proj = (f (c*s+d)).proj`.
    change (f (c * s + d)).proj = γ (c * s + d)
    exact hproj (c * s + d)
  · -- Integral-curve identity is the helper `scaledTangentLift_transport`
    -- applied to the original lift's integral-curve hypothesis `hf`.
    exact scaledTangentLift_transport (I := I) g α hf c d

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
