import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

set_option linter.unusedSectionVars false

/-!
# Geodesic time-rescaling: infrastructure

For a smooth Riemannian metric `g` on a smooth manifold `M` modelled on a
finite-dimensional inner-product space `E`, the classical geodesic flow
has the scaling invariance
$$\gamma_{p, a v}(t) = \gamma_{p, v}(a t).$$
On the integral-curve side this manifests as: if `f : ℝ → TangentBundle I M`
is a lifted integral curve of the chart-fixed geodesic vector field with
fibre value `v` at `t = 0`, then the rescaled lift
`f_R(s) := ⟨(f (a s)).proj, a • (f (a s)).snd⟩` is a candidate lifted
integral curve with fibre value `a • v` at `s = 0`.

The chart-fixed geodesic vector field is constructed entirely through
the trivialisation of `T M` at a fixed basepoint `α : M`; its value
depends only on the chart-fibre coordinate of the input point. Linearity
of the trivialisation in the fibre then yields a clean rescaling
identity for the chart-fibre form of the geodesic vector field:
$$V_α(R_a p) = \big(a v(p),\; -(a\cdot a)\, \Gamma_α(v(p), v(p))(x(p))\big),$$
where `v(p) := chartFiberCoord α p` and `x(p) := extChartAt I α p.proj`.

This file packages:

* `tangentBundleFiberSmul a : TangentBundle I M → TangentBundle I M` —
  the fibre-rescaling map `⟨b, w⟩ ↦ ⟨b, a • w⟩` on the tangent bundle.

* `chartFiberCoord_tangentBundleFiberSmul` — linearity of the chart-fibre
  coordinate of `tangentBundleFiberSmul a` in `a`: the chart-fibre is
  `a • chartFiberCoord α p`.

* `geodesicVectorFieldChartFiber_tangentBundleFiberSmul` — explicit
  rescaling of the chart-fibre form of the geodesic vector field at
  `tangentBundleFiberSmul a p`.

* `tangentBundleFiberSmul_zero_section` — the zero section is fixed
  pointwise under fibre rescaling.

These are the algebraic identities required by any downstream
manifold-level geodesic rescaling argument.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Fibre-rescaling map on the tangent bundle

The map `⟨b, w⟩ ↦ ⟨b, a • w⟩` on `TangentBundle I M`. It does not require
boundarylessness; the definition is structural on the Sigma type. -/

section FibreScale

/-- The fibre-rescaling map on `TangentBundle I M`: keep the base point,
multiply the fibre vector by the scalar `a`. -/
def tangentBundleFiberSmul (a : ℝ) (p : TangentBundle I M) : TangentBundle I M :=
  ⟨p.proj, a • p.snd⟩

@[simp] lemma tangentBundleFiberSmul_proj (a : ℝ) (p : TangentBundle I M) :
    (tangentBundleFiberSmul (I := I) (M := M) a p).proj = p.proj := rfl

@[simp] lemma tangentBundleFiberSmul_snd (a : ℝ) (p : TangentBundle I M) :
    (tangentBundleFiberSmul (I := I) (M := M) a p).snd = a • p.snd := rfl

@[simp] lemma tangentBundleFiberSmul_mk (a : ℝ) (b : M) (w : TangentSpace I b) :
    tangentBundleFiberSmul (I := I) (M := M) a (⟨b, w⟩ : TangentBundle I M) =
      ⟨b, a • w⟩ := rfl

/-- At the zero section, fibre rescaling is the identity. -/
@[simp] lemma tangentBundleFiberSmul_zero_section (a : ℝ) (b : M) :
    tangentBundleFiberSmul (I := I) (M := M) a
        (⟨b, (0 : E)⟩ : TangentBundle I M) =
      (⟨b, (0 : E)⟩ : TangentBundle I M) := by
  change (⟨b, a • (0 : E)⟩ : TangentBundle I M) = ⟨b, (0 : E)⟩
  rw [smul_zero]

/-- Fibre rescaling at `a = 1` is the identity. -/
@[simp] lemma tangentBundleFiberSmul_one (p : TangentBundle I M) :
    tangentBundleFiberSmul (I := I) (M := M) (1 : ℝ) p = p := by
  change (⟨p.proj, (1 : ℝ) • p.snd⟩ : TangentBundle I M) = p
  rw [one_smul]

/-- Fibre rescaling at `a = 0` projects to the zero section. -/
@[simp] lemma tangentBundleFiberSmul_zero (p : TangentBundle I M) :
    tangentBundleFiberSmul (I := I) (M := M) (0 : ℝ) p =
      (⟨p.proj, (0 : E)⟩ : TangentBundle I M) := by
  change (⟨p.proj, (0 : ℝ) • p.snd⟩ : TangentBundle I M) =
    ⟨p.proj, (0 : E)⟩
  congr 1
  exact zero_smul _ _

/-- Composition rule. -/
lemma tangentBundleFiberSmul_comp (a b : ℝ) (p : TangentBundle I M) :
    tangentBundleFiberSmul (I := I) (M := M) a
        (tangentBundleFiberSmul (I := I) (M := M) b p) =
      tangentBundleFiberSmul (I := I) (M := M) (a * b) p := by
  change (⟨p.proj, a • b • p.snd⟩ : TangentBundle I M) =
    ⟨p.proj, (a * b) • p.snd⟩
  rw [smul_smul]

end FibreScale

/-! ## Trivialisation-side description

The trivialisation `e := trivializationAt E (TangentSpace I) α` at a
fixed basepoint sends `p ∈ e.source` to `(p.proj, chartFiberCoord α p)`.
Because the trivialisation is linear in the fibre, fibre rescaling
commutes with the chart-fibre coordinate:
`chartFiberCoord α (tangentBundleFiberSmul a p) = a • chartFiberCoord α p`.
-/

section TrivialisationSide

/-- The chart-fibre coordinate of the fibre-rescaled point, expressed via
linearity of the trivialisation in the fibre. -/
lemma chartFiberCoord_tangentBundleFiberSmul (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α
        (tangentBundleFiberSmul (I := I) (M := M) a p) =
      a • chartFiberCoord (I := I) α p := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he_def
  have hb : p.proj ∈ e.baseSet := by
    rw [he_def, TangentBundle.trivializationAt_baseSet (I := I)]; exact hp
  -- Use `e.continuousLinearMapAt ℝ p.proj` which is `R`-linear on the
  -- fibre. Its action on `y : E` agrees with `(e ⟨p.proj, y⟩).2` when
  -- `p.proj ∈ e.baseSet`.
  have hCLM_eq_orig :
      e.continuousLinearMapAt ℝ p.proj p.snd = (e p).2 := by
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := p.proj) hb
    -- `hcoe : ⇑(e.linearMapAt ℝ p.proj) = fun y => (e ⟨p.proj, y⟩).2`.
    have hCLM : e.continuousLinearMapAt ℝ p.proj p.snd =
        e.linearMapAt ℝ p.proj p.snd := rfl
    rw [hCLM, congrFun hcoe p.snd]
  have hCLM_eq_smul :
      e.continuousLinearMapAt ℝ p.proj (a • p.snd) =
        (e (tangentBundleFiberSmul (I := I) (M := M) a p)).2 := by
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := p.proj) hb
    have hCLM : e.continuousLinearMapAt ℝ p.proj (a • p.snd) =
        e.linearMapAt ℝ p.proj (a • p.snd) := rfl
    rw [hCLM, congrFun hcoe (a • p.snd)]
    rfl
  -- Linearity: e.continuousLinearMapAt ℝ p.proj (a • p.snd) = a • e.CLM p.snd
  have hsmul := (e.continuousLinearMapAt ℝ p.proj).map_smul a p.snd
  -- Combine.
  change (e (tangentBundleFiberSmul (I := I) (M := M) a p)).2 = a • (e p).2
  rw [← hCLM_eq_smul, hsmul, hCLM_eq_orig]

end TrivialisationSide

/-! ## Vector field at the rescaled point

Using the chart-fibre rescaling identity, we read off the value of
`geodesicVectorFieldChartFiber g α` at the fibre-rescaled point. -/

section VFAtRescaled

variable [I.Boundaryless]

/-- The chart-fibre form of the geodesic vector field at the
fibre-rescaled point. The first slot becomes `a • v` (where `v` is the
chart-fibre at `p`) by linearity of the trivialisation; the second slot
becomes `-(a*a) • Γ(v, v)` by quadratic homogeneity of the Christoffel
contraction (`chartChristoffelContraction_smul_smul`). -/
lemma geodesicVectorFieldChartFiber_tangentBundleFiberSmul
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p) =
      (a • chartFiberCoord (I := I) α p,
        -(a * a) •
          chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α p)
            (chartFiberCoord (I := I) α p)
            (extChartAt I α p.proj)) := by
  classical
  have hcf : chartFiberCoord (I := I) α
      (tangentBundleFiberSmul (I := I) (M := M) a p) =
      a • chartFiberCoord (I := I) α p :=
    chartFiberCoord_tangentBundleFiberSmul (I := I) α a hp
  have hproj :
      (tangentBundleFiberSmul (I := I) (M := M) a p).proj = p.proj := rfl
  unfold geodesicVectorFieldChartFiber
  simp only [hcf, hproj]
  refine Prod.ext rfl ?_
  have h := chartChristoffelContraction_smul_smul (I := I) g α a
    (chartFiberCoord (I := I) α p) (extChartAt I α p.proj)
  change -chartChristoffelContraction (I := I) g α
      (a • chartFiberCoord (I := I) α p)
      (a • chartFiberCoord (I := I) α p)
      (extChartAt I α p.proj) =
    -(a * a) • chartChristoffelContraction (I := I) g α
      (chartFiberCoord (I := I) α p)
      (chartFiberCoord (I := I) α p)
      (extChartAt I α p.proj)
  rw [h, neg_smul]

/-- Compatibility with the second coordinate of the chart-fibre form
when read off through the trivialisation at the same basepoint. -/
lemma geodesicVectorFieldChartFiber_tangentBundleFiberSmul_fst
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p)).1 =
      a • chartFiberCoord (I := I) α p := by
  rw [geodesicVectorFieldChartFiber_tangentBundleFiberSmul (I := I)
    g α a hp]

lemma geodesicVectorFieldChartFiber_tangentBundleFiberSmul_snd
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a p)).2 =
      -(a * a) •
        chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj) := by
  rw [geodesicVectorFieldChartFiber_tangentBundleFiberSmul (I := I)
    g α a hp]

/-- The chart-domain (preimage of the chart source under projection on
`TM`) is invariant under fibre rescaling: the projection is unchanged. -/
lemma tangentBundleFiberSmul_mem_geodesicChartDomain (α : M) (a : ℝ)
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    tangentBundleFiberSmul (I := I) (M := M) a p ∈
      geodesicChartDomain (I := I) α := by
  -- `geodesicChartDomain α = π⁻¹ (chartAt H α).source`, and the
  -- projection of the rescaled point is the same.
  change (tangentBundleFiberSmul (I := I) (M := M) a p).proj ∈
    (chartAt H α).source
  exact hp

end VFAtRescaled

/-! ## Constant-curve rescaling

If `γ ≡ p` is the stationary geodesic, then `s ↦ γ(a · s) = p` is the
same stationary geodesic. This is the trivial case of the geodesic
time-rescaling. -/

section ConstantRescaling

/-- The stationary geodesic is preserved under any time rescaling.
The composition `(fun _ => p) ∘ (· * a)` is again the constant curve
at `p`, which is a geodesic by `isGeodesic_const`. -/
theorem isGeodesic_const_comp_mul
    (g : SmoothRiemannianMetric I M) (p : M) (a : ℝ) :
    IsGeodesic (I := I) g (fun s : ℝ => (fun _ : ℝ => p) (a * s)) :=
  isGeodesic_const (I := I) g p

end ConstantRescaling

/-! ## Local rescaling at the integral-curve level

We package the algebraic core of the geodesic time-rescaling: if `f` is
a lifted integral curve of the chart-fixed geodesic vector field
`V_α := geodesicVectorFieldChart g α`, then the candidate rescaled lift
`f_R(s) := tangentBundleFiberSmul a (f (a · s))` has the property that
its chart-fibre image rescales by `a` and the corresponding chart-fibre
form of `V_α` at `f_R(s)` is `(a v, -(a*a) Γ(v, v))` with `v` the chart
fibre of `f(a s)`.

The statements below are the **algebraic-rescaling building blocks**.
The conversion to a full `IsMIntegralCurve f_R V_α` requires the
manifold-derivative chain rule through the (smooth) fibre-rescaling map
on the tangent bundle; that derivative-level step is left to the
downstream caller. -/

section LiftLevelRescaling

variable [I.Boundaryless]

/-- The chart-fibre coordinate of the rescaled lift at time `s`, in the
chart at `α`, equals `a • chartFiberCoord α (f (a s))`, provided the
underlying projection at time `a s` is in the chart source. -/
lemma chartFiberCoord_rescaledLift
    (α : M) (a : ℝ) (f : ℝ → TangentBundle I M) (s : ℝ)
    (hs : (f (a * s)).proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α
        (tangentBundleFiberSmul (I := I) (M := M) a (f (a * s))) =
      a • chartFiberCoord (I := I) α (f (a * s)) :=
  chartFiberCoord_tangentBundleFiberSmul (I := I) α a hs

/-- The chart-fibre form of the geodesic vector field at the rescaled
lift's value, in the chart at `α`. -/
lemma geodesicVectorFieldChartFiber_rescaledLift
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ)
    (f : ℝ → TangentBundle I M) (s : ℝ)
    (hs : (f (a * s)).proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α
        (tangentBundleFiberSmul (I := I) (M := M) a (f (a * s))) =
      (a • chartFiberCoord (I := I) α (f (a * s)),
        -(a * a) •
          chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α (f (a * s)))
            (chartFiberCoord (I := I) α (f (a * s)))
            (extChartAt I α (f (a * s)).proj)) :=
  geodesicVectorFieldChartFiber_tangentBundleFiberSmul (I := I) g α a hs

end LiftLevelRescaling

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
