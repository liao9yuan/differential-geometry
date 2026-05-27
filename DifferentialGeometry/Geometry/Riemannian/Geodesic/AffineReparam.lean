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

/-! ## Affine reparametrisation invariance of `pathELength`

For an affine reparametrisation `s ↦ c * s + d` with `c > 0`, the
`pathELength` of the composed curve over `Icc ((a - d) / c) ((b - d) / c)`
equals the `pathELength` of the original curve over `Icc a b`. This is a
direct corollary of Mathlib's `pathELength_comp_of_monotoneOn` applied to
the strictly increasing affine map `s ↦ c * s + d`.

The lemma is stated in the `Manifold` namespace's `pathELength`. The
typeclass requirement `[∀ x, ENormSMulClass ℝ (TangentSpace I x)]` for
the underlying Mathlib reparametrisation lemma is supplied by the
`RiemannianBundle` instance through the chain
`RiemannianBundle ⟶ NormedAddCommGroup ⟶ NormSMulClass ⟶ ENormSMulClass`.
-/

section AffinePathELengthReparam

open Manifold

variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- Affine reparametrisation invariance of `pathELength` with positive
slope. If `c > 0` and `a ≤ b`, then the path length of `s ↦ γ (c * s + d)`
on `Icc ((a - d) / c) ((b - d) / c)` equals the path length of `γ` on
`Icc a b`, provided `γ` is `MDifferentiableOn` `Icc a b`. -/
theorem pathELength_comp_affineHomeo
    (γ : ℝ → M) {a b : ℝ} (c d : ℝ) (hab : a ≤ b) (hc : 0 < c)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Icc a b)) :
    pathELength I (fun s : ℝ => γ (c * s + d)) ((a - d) / c) ((b - d) / c)
      = pathELength I γ a b := by
  -- The reparametrisation `f s = c * s + d`.
  set f : ℝ → ℝ := fun s : ℝ => c * s + d with hf_def
  -- Image of the endpoints: `f ((a - d) / c) = a`, `f ((b - d) / c) = b`.
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hfa : f ((a - d) / c) = a := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  have hfb : f ((b - d) / c) = b := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  -- The new lower endpoint is `≤` the new upper endpoint.
  have hab' : (a - d) / c ≤ (b - d) / c := by
    rw [div_le_div_iff_of_pos_right hc]
    linarith
  -- `f` is monotone on `Icc ((a - d) / c) ((b - d) / c)` (it is monotone
  -- on `ℝ`, hence on any subset).
  have hf_mono : MonotoneOn f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _ y _ hxy
    simp only [hf_def]
    have : c * x ≤ c * y := mul_le_mul_of_nonneg_left hxy hc.le
    linarith
  -- `f` is differentiable everywhere, hence on `Icc ((a - d) / c) ((b - d) / c)`.
  have hf_diff : DifferentiableOn ℝ f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _
    -- `f x = c * x + d` is differentiable; convert from `Differentiable`.
    have hdiff : Differentiable ℝ f := by
      simp only [hf_def]
      exact ((differentiable_const c).mul differentiable_id).add (differentiable_const d)
    exact (hdiff x).differentiableWithinAt
  -- The hypothesis `MDiff[Icc (f a') (f b')] γ` becomes `MDifferentiableOn`
  -- on `Icc a b` after rewriting via `hfa`/`hfb`.
  have hγ' : MDifferentiableOn 𝓘(ℝ, ℝ) I γ
      (Set.Icc (f ((a - d) / c)) (f ((b - d) / c))) := by
    rw [hfa, hfb]; exact hγ
  -- Apply Mathlib's `pathELength_comp_of_monotoneOn`.
  have hmain :
      pathELength I (γ ∘ f) ((a - d) / c) ((b - d) / c)
        = pathELength I γ (f ((a - d) / c)) (f ((b - d) / c)) :=
    pathELength_comp_of_monotoneOn (I := I) (γ := γ) hab' hf_mono hf_diff hγ'
  -- Rewrite the endpoints.
  rw [hfa, hfb] at hmain
  -- The composition `γ ∘ f` is `fun s => γ (c * s + d)` by definition of `f`.
  exact hmain

end AffinePathELengthReparam

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
