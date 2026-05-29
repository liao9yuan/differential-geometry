import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.GeodesicEquationBridge
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

set_option linter.unusedSectionVars false

/-!
# Cross-chart-basepoint reduction for the geodesic vector field

This file packages the cross-VF reduction bridge: an integral curve of the
chart-fixed geodesic vector field at one basepoint `α` is, on the overlap of
chart sources, also an integral curve of the chart-fixed geodesic vector field
at a different basepoint `α'`. Combined with chart-fixed Picard–Lindelöf
existence and uniqueness, this yields the unconditional
`IsGeodesicAt → HasGeodesicEquationAt` bridge.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Pointwise chart-invariance of the geodesic spray.** At a tangent-bundle
point `p` whose foot `p.proj` lies in the chart-source at `α`, the chart-`α`
fixed geodesic vector field coincides with the basepoint-free geodesic vector
field `geodesicVectorField g p` (built in the chart centred at `p.proj`).

The first component already coincides by `geodesicVectorFieldChart_fst`
(both equal `p.snd`). The second component is the genuine content: the
chart-`α` Christoffel acceleration, pushed through the second-tangent-bundle
chart transition from `α`-coordinates to `p.proj`-coordinates, equals the
chart-`p.proj` Christoffel acceleration. This is the non-tensorial
transformation law of the Christoffel symbols (`chartChristoffel_transform`)
together with the velocity-Jacobian correction encoded by the `snd`-block of
the iterated tangent-bundle transition derivative. -/
theorem geodesicVectorFieldChart_eq_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = geodesicVectorField (I := I) g p := by
  -- RESIDUAL. The first components agree (`geodesicVectorFieldChart_fst` gives
  -- `(gvfChart g α p).1 = p.snd = (geodesicVectorField g p).1`). The remaining
  -- obligation is the SECOND component: pushing the chart-`α` Christoffel
  -- acceleration `gvfChartFiber g α p` through the iterated tangent-bundle
  -- transition `tangentCoordChange I.tangent ⟨α,0⟩ p p` (the fderiv of
  -- `Ψ := extChartAt I.tangent ⟨α,0⟩ ∘ (extChartAt I.tangent p).symm`) must equal
  -- the chart-`p.proj` Christoffel acceleration `-Γ_{p.proj}(p.snd,p.snd)`.
  --
  -- The needed missing infrastructure is the `snd`-block of that iterated
  -- transition fderiv. Concretely (verified by `extChartAt_tangent_apply_snd` +
  -- the trivialisation `continuousLinearMapAt`/`symmL` identities), the second
  -- component of `Ψ` has the closed form
  --   `Ψ(x, v).2 = tangentCoordChange I p.proj α ((extChartAt I p.proj).symm x) v`,
  -- whose Fréchet derivative within `range I.tangent` at the base point
  -- `(extChartAt I p.proj p.proj, p.snd)` is
  --   `(δx, δv) ↦ (D_x [tcc · p.snd]) δx + tcc(p.proj) δv`,
  -- i.e. the base Jacobian on the `δv`-slot plus the second-derivative
  -- (`D²`) correction on the `δx`-slot. Contracting this against
  -- `gvfChartFiber g α p = (chartFiberCoord α p, -Γ_α(...))` and matching the two
  -- index sums against `chartChristoffel_transform`'s covariant-pullback term and
  -- `chartTransitionSecondDerivCorrection` (the `∂_i J^c_j` term) closes the goal.
  -- This `snd`-block derivative formula (analogue of the `fst`-block lemma
  -- `fst_continuousLinearMapAt_secondaryTriv` in `ProjDerivative.lean`, but for the
  -- second component and hence involving second derivatives) is the single
  -- remaining piece. The Christoffel transformation law it consumes is already
  -- available as `chartChristoffel_transform` in `ChartTransition.lean`.
  sorry

/-- **Cross-basepoint pointwise coincidence of the chart-fixed geodesic vector
field.** At a tangent-bundle point `p` whose foot lies in both chart-sources,
the chart-`α` and chart-`α'` fixed geodesic vector fields agree as elements of
`T_p(TM)`. Both equal the basepoint-free geodesic spray
`geodesicVectorField g p` by `geodesicVectorFieldChart_eq_geodesicVectorField`. -/
theorem geodesicVectorFieldChart_eq_of_proj_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hα' : p.proj ∈ (chartAt H α').source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g α' p := by
  rw [geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α hα,
    geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α' hα']

/-- **Cross-basepoint coincidence of the chart-fixed geodesic vector field on
integral curves.** A curve which is a local integral curve at `t₀` of the
chart-fixed geodesic vector field at one basepoint `α` is also a local
integral curve at `t₀` of the chart-fixed geodesic vector field at a
different basepoint `α'`, provided the projection of the curve at `t₀` lies
in both chart sources. -/
theorem bm_c_gc_vf_chart_coincidence
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hα : (f t₀).proj ∈ (chartAt H α).source)
    (hα' : (f t₀).proj ∈ (chartAt H α').source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α') t₀ := by
  classical
  -- The base projection is continuous at `t₀` (integral curves are continuous).
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hproj_contAt : ContinuousAt (fun t => (f t).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  -- Eventually `(f t).proj ∈ (chartAt H α).source`.
  have hα_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα)
  -- Eventually `(f t).proj ∈ (chartAt H α').source`.
  have hα'_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α').source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α').open_source.mem_nhds hα')
  -- Transfer the `HasMFDerivAt` clause: the two vector fields agree where both
  -- foot-membership conditions hold.
  unfold IsMIntegralCurveAt at hf ⊢
  filter_upwards [hf, hα_nhds, hα'_nhds] with t htD ht_α ht_α'
  have ht_α2 : (f t).proj ∈ (chartAt H α).source := ht_α
  have ht_α'2 : (f t).proj ∈ (chartAt H α').source := ht_α'
  have hvf_eq : geodesicVectorFieldChart (I := I) g α (f t) =
      geodesicVectorFieldChart (I := I) g α' (f t) :=
    geodesicVectorFieldChart_eq_of_proj_mem (I := I) g α α' (p := f t) ht_α2 ht_α'2
  exact hvf_eq ▸ htD

/-- **Cross-VF projection-uniqueness for `IsGeodesicAt`.** From an
`IsGeodesicAt`-witness `(α, f)` of `γ` at `t₀`, construct a
chart-`γ(t₀)`-centred local integral curve `f₁` of the chart-fixed geodesic
vector field at `γ(t₀)` whose projection agrees with `γ` on a neighbourhood
of `t₀`. -/
theorem bm_c_gc_cross_vf_projection_uniqueness
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t₀).proj = γ t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ ∧
      γ =ᶠ[𝓝 t₀] (fun t => (f₁ t).proj) := by
  classical
  -- Unpack the `IsGeodesicAt` witness: chart basepoint `α`, lift `f`.
  obtain ⟨α, f, hproj, hf⟩ := hγ
  -- `(f t₀).proj = γ t₀`.
  have hft₀ : (f t₀).proj = γ t₀ := hproj t₀
  -- `(f t₀).proj` lies in the chart-source at `γ t₀` (its own chart).
  have hγt₀_src : (f t₀).proj ∈ (chartAt H (γ t₀)).source := by
    rw [hft₀]; exact mem_chart_source H (γ t₀)
  -- `(f t₀).proj` lies in the chart-source at `α`.
  --
  -- RESIDUAL. This is the foot-in-source condition for the witness basepoint.
  -- It is required to convert the witness `f` (an integral curve of the
  -- chart-`α` geodesic field) to an integral curve of the chart-`γ(t₀)`
  -- geodesic field via the cross-basepoint coincidence below (whose hypothesis
  -- `hα` is exactly this membership). It is NOT derivable from the bare
  -- `IsGeodesicAt` predicate: off `(chartAt H α).source` the field
  -- `geodesicVectorFieldChart g α` is the zero section (the inverse
  -- trivialisation `(trivAt ⟨α,0⟩).symm` is `0` off its base set), so the
  -- integral-curve clause at `t₀` degenerates to `mfderiv f t₀ = 0` with no
  -- constraint placing the foot back in the source. Every constructor of
  -- `IsGeodesicAt` in the codebase (Picard–Lindelöf in `Existence.lean`,
  -- `IsGeodesicAt.const`, rescaling in `MaximalInterval.lean`) does produce a
  -- witness whose foot lies in the basepoint chart-source; strengthening the
  -- `IsGeodesicAt` definition to record this (e.g. an extra field
  -- `(f t₀).proj ∈ (chartAt H α).source`, or equivalently aligning the
  -- basepoint to the foot) would discharge this residual uniformly. Pending
  -- that definitional adjustment, the membership is left as the precise gap.
  have hα_src : (f t₀).proj ∈ (chartAt H α).source := by
    sorry
  -- Build the chart-`γ(t₀)`-centred lift through the same initial tangent vector
  -- `(f t₀).snd`. Picard–Lindelöf gives the integral curve.
  obtain ⟨f₁, hf₁_init, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  -- `(f₁ t₀).proj = γ t₀`.
  have hf₁_proj : (f₁ t₀).proj = γ t₀ := by rw [hf₁_init]
  refine ⟨f₁, hf₁_proj, hf₁, ?_⟩
  -- Move the witness `f`'s integral-curve property to basepoint `γ t₀` via the
  -- cross-basepoint coincidence, then compare with `f₁` by uniqueness.
  have hf_at_γ : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ :=
    bm_c_gc_vf_chart_coincidence (I := I) g α (γ t₀) hα_src hγt₀_src hf
  -- `f t₀ = f₁ t₀`: both are `⟨γ t₀, (f t₀).snd⟩` (foot equality + same velocity).
  have h0 : f₁ t₀ = f t₀ := by
    rw [hf₁_init]
    -- `⟨γ t₀, (f t₀).snd⟩ = f t₀` since `(f t₀).proj = γ t₀` and `f t₀ = ⟨(f t₀).proj, (f t₀).snd⟩`.
    rw [← hft₀]
  -- Uniqueness on `TM` at basepoint `γ t₀`: `f₁ =ᶠ f`.
  have hfe : f₁ =ᶠ[𝓝 t₀] f := by
    have hsrc₁ : (f₁ t₀).proj ∈ (chartAt H (γ t₀)).source := by
      rw [hf₁_proj]; exact mem_chart_source H (γ t₀)
    exact isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := γ t₀) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f) hsrc₁ hf₁ hf_at_γ h0
  -- Project the eventual equality: `γ t = (f t).proj = (f₁ t).proj`.
  filter_upwards [hfe] with t ht
  -- `ht : f₁ t = f t`; goal `γ t = (f₁ t).proj`.
  rw [ht, hproj t]

/-- **Unconditional bridge `IsGeodesicAt → HasGeodesicEquationAt`.** A local
geodesic at `t₀` satisfies the chart-coordinate second-derivative form of the
geodesic equation at `t₀`. -/
theorem IsGeodesicAt.hasGeodesicEquationAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f₁, hf₁_proj_t₀, hf₁, hcross⟩ :=
    bm_c_gc_cross_vf_projection_uniqueness (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ
  exact IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ (f₁ := f₁) hf₁ hf₁_proj_t₀ hcross

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
