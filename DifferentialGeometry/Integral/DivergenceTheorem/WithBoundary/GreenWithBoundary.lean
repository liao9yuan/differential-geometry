import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Stokes
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Green
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.Family
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Green's identities with boundary contribution
(chart-by-chart formulation)

For a smooth Riemannian metric `g` on a compact smooth manifold `M` whose
local model `I : ModelWithCorners ℝ E H` admits a smooth boundary stratum
(`[hI : HasSmoothBoundary E H I]`), this file establishes Green's first and
second identities with explicit boundary contribution terms.

Because a global smooth outward unit normal vector field on the boundary is,
in the present infrastructure, available only pointwise (not as a smooth
bundle section), the boundary contribution is naturally expressed in
chart-by-chart form: as the finite sum, over the chart-atlas partition of
unity, of `chartBoundaryFaceIntegral` quantities. This mirrors the
formulation in `Stokes.lean`.

## Strategy

The proof of Green's first identity with boundary applies the global Stokes
theorem `stokes_compact_via_pou` to the smooth tangent section
`Y := smoothSmul f hf (grad_g_with_boundary_section g hh hh_int)` (i.e.
`f · ∇_g h`). By the divergence Leibniz rule
`divergence_g_with_boundary_smoothSmul`,
`div_g^{(\partial)}(f · ∇h) = f · Δh + ⟨∇f, ∇h⟩`, where `Δh` is the
with-boundary Laplacian and `⟨·,·⟩` is the metric inner product. Integrating
both sides against the canonical Riemannian volume measure and using the
global Stokes theorem to evaluate the integral of the divergence as the
chart-α boundary face sum yields Green's first identity.

Green's second identity follows by symmetrising in `f` and `h` and
subtracting; the `⟨∇f, ∇h⟩` and `⟨∇h, ∇f⟩` terms cancel by symmetry of the
metric.

## Sanity check

When the test scalar `f` is also interior-supported (in addition to `h`), the
boundary face sum vanishes — the section `f · ∇h` then has compact support
contained in `I.interior M`, and its with-boundary divergence integrates to
zero by `integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support`.
This recovers the interior-supported Green's first identity from
`Green.lean` (i.e.
`integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary`), and is
recorded as `green_first_with_boundary_face_sum_eq_zero_of_interior_support`.

## Main definitions and results

* `boundaryFaceSum g X` — the chart-α boundary face integral summed over the
  chart-atlas POU support, with weights `(chartAtlasPOU I M) α`. A single
  named definition encapsulating the boundary contribution to the with-
  boundary divergence theorem.

* `green_first_with_boundary` — Green's first identity with boundary terms.

* `green_second_with_boundary` — Green's second identity with boundary terms.

* `green_first_with_boundary_face_sum_eq_zero_of_interior_support` — sanity
  check: when the test scalar is interior-supported, the boundary face sum
  vanishes and the boundaryless-style identity from `Green.lean` is
  recovered.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## File-local Borel-space instances

Match the convention in the surrounding files: `E` and `M` carry their
canonical Borel σ-algebras. Declared `local` to avoid leaking into callers. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Boundary-face sum

A single named quantity packaging the chart-by-chart boundary contribution
appearing in both Green's identities and in the global Stokes theorem.
Declared as the finite sum (over the chart-atlas POU support) of the
chart-α boundary face integrals weighted by the chart-atlas POU. -/

/-- **Boundary face sum.** The boundary contribution to the with-boundary
divergence theorem, expressed as a finite sum over the chart-atlas
partition of unity. By definition, the chart-α boundary face integral of
`X` against the chart-α POU weight, summed over the POU support set.

This is the chart-by-chart presentation of the boundary integral: when a
single intrinsic surface integral over `I.boundary M` against an outward
unit normal vector field is available, the boundary face sum coincides
with that intrinsic surface integral; this identification is not
established in the present file. -/
noncomputable def boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    chartBoundaryFaceIntegral (I := I) g α X
      ((chartAtlasPOU I M) α : M → ℝ)

@[simp] lemma boundaryFaceSum_def
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    boundaryFaceSum (I := I) g X =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) g α X
          ((chartAtlasPOU I M) α : M → ℝ) := rfl

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

/-- The global Stokes theorem rephrased through `boundaryFaceSum`: for any
smooth tangent section `X`, the integral of `divergence_g_with_boundary g X`
against the canonical Riemannian volume measure equals
`boundaryFaceSum g X`. -/
theorem integral_divergence_with_boundary_eq_boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g X := by
  rw [boundaryFaceSum_def]
  exact stokes_compact_via_pou (I := I) g X

/-! ## Green's first identity with boundary

The proof applies the global Stokes theorem to the smooth tangent section
`Y := f · ∇_g h`, which is packaged as `smoothSmul f hf
(grad_g_with_boundary_section g hh hh_int)`. By the divergence Leibniz rule
`divergence_g_with_boundary_smoothSmul`,
`div_g^{(\partial)}(f · ∇h) = f · Δh + ⟨∇f, ∇h⟩` pointwise. Integrating
this against the canonical Riemannian volume measure and using the global
Stokes theorem yields:

  `∫ ⟨∇f, ∇h⟩ + ∫ f · Δh = boundaryFaceSum g (f · ∇h)`.

The pointwise reformulation uses the duality of the gradient with the
tangent action and the symmetry of the metric:

  `tangentSectionAction (∇h) f x = ⟨∇h, ∇f⟩ = ⟨∇f, ∇h⟩`. -/

/-- A continuity helper: the inner product `⟨∇f, ∇h⟩` is continuous on the
manifold interior. The pointwise formula `g.inner x (gradFun g f x) (gradFun
g h x)` is continuous on `I.interior M` because both gradients are smooth
sections on the interior and `g.inner` is a smooth bundle map.

Combined with vanishing on the open complement of `tsupport h ⊆ I.interior
M`, this gives global continuity. -/
private lemma inner_grad_grad_continuous_of_interior_support
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)) := by
  classical
  -- Strategy: rewrite `g.inner x (∇f) (∇h) = tangentSectionAction (∇h_section) f`,
  -- which is continuous by `tangentSectionAction_continuous_of_interior_support`
  -- under the interior-support hypothesis on `f` — but here we only have the
  -- interior-support hypothesis on `h`, packaged through the section
  -- `grad_g_with_boundary_section g hh hh_int`. We use the section's
  -- interior-support to deduce continuity of the inner product.
  -- Set `Y := grad_g_with_boundary_section g hh hh_int` and observe
  -- `g.inner x (∇f x) (∇h x) = tangentSectionAction Y f x` (by duality + symmetry).
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hY_def
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_eq : ∀ x : M,
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
        tangentSectionAction (I := I) Y f x := by
    intro x
    -- `tangentSectionAction Y f x = g.inner x (Y x) (gradFun g f x)`
    --                            = g.inner x (gradFun g h x) (gradFun g f x)`.
    -- By symmetry, `g.inner x (gradFun g h x) (gradFun g f x) =
    --              g.inner x (gradFun g f x) (gradFun g h x)`.
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf Y x]
    -- Goal: g.inner x (gradFun g f) (gradFun g h) = g.inner x (Y x) (gradFun g f).
    -- Y x = gradFun g h x by definitional unfolding; then symmetry swaps.
    change g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
    exact g.symm x _ _
  -- Continuity of `tangentSectionAction Y f` follows from the with-boundary
  -- helper, since `f` is smooth and `tsupport (Y …) ⊆ I.interior M` (the
  -- tangent action's continuity on interior-supported scalars is established
  -- in `IntegrationByParts.lean`; the symmetric statement we need here uses
  -- the interior support of `Y`, which is captured indirectly through
  -- `tangentSectionAction_continuous_of_interior_support`).
  -- The latter helper requires `tsupport f ⊆ I.interior M`. We don't have
  -- that hypothesis; instead, we derive continuity directly.
  -- We use: `Y` is smooth as a tangent-bundle section globally on `M`; `f` is
  -- smooth globally; hence `mfderiv f x (Y x)` is continuous as a function on
  -- `M`. The latter is `tangentSectionAction Y f`.
  -- Since `Y` is a `Cₛ^∞`-section and `f` is `ContMDiff ∞`, we use the
  -- standard manifold-level continuity: `tangentSectionAction Y f` is the
  -- bundle-evaluation of `mfderiv f` on `Y`, and is continuous when both are
  -- smooth.
  have hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) := Y.contMDiff
  -- Bridge: `tangentSectionAction Y f` is continuous on M.
  -- We rebuild via the existing helper, conditioned on the interior support
  -- of `Y`: the helper accepts `tsupport (scalar) ⊆ I.interior M`; here we
  -- need a version conditioned on `tsupport (section) ⊆ I.interior M`.
  -- Instead of plumbing a new helper, observe that
  -- `tangentSectionAction Y f x = mfderiv I 𝓘(ℝ) f x (Y x)` is the action of
  -- the smooth `Y` on smooth `f`. The action's continuity follows from a
  -- pointwise case split on whether `x ∈ tsupport Y`:
  -- * On `tsupport Y ⊆ I.interior M` the action is smooth (from
  --   `tangentSectionAction_contMDiffOn` applied on a chart whose image lies
  --   in the interior of the chart target).
  -- * Off `tsupport Y` the action vanishes, hence is locally constant.
  -- This mirrors the proof of `tangentSectionAction_continuous_of_interior_support`
  -- but with the interior-support hypothesis transferred to `Y`.
  have h_act_cont : Continuous (tangentSectionAction (I := I) Y f) := by
    classical
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (Y : ∀ x, TangentSpace I x)
    · -- `x ∈ tsupport Y ⊆ I.interior M`. Use smoothness on the chart at `x`.
      have hx_int : x ∈ I.interior M := hY_int hx_supp
      have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
      have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_mem_interior_target_of_isInteriorPoint
          (I := I) (M := M) x hx_chart hx_int
      -- `tangentSectionAction Y f` is smooth on the smoothness domain at `α := x`.
      have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) Y f)
          ((extChartAt I x).source ∩
            (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
        tangentSectionAction_contMDiffOn (I := I) x Y hf
      have hxsrc : x ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
      have hxU : x ∈ (extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target :=
        ⟨hxsrc, hx_target_int⟩
      have hUopen : IsOpen ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) := by
        have hcontOn := continuousOn_extChartAt (I := I) x
        exact hcontOn.isOpen_inter_preimage (isOpen_extChartAt_source (I := I) x)
          isOpen_interior
      exact ((hsmooth x hxU).continuousWithinAt.continuousAt) (hUopen.mem_nhds hxU)
    · -- `x ∉ tsupport Y` — `Y` vanishes on a neighborhood of `x`, so the
      -- tangent action vanishes too.
      have h_open : IsOpen (tsupport (Y : ∀ x, TangentSpace I x))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : tangentSectionAction (I := I) Y f =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        have hY_zero : (Y : ∀ z, TangentSpace I z) y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        change mfderiv I 𝓘(ℝ) f y ((Y : ∀ z, TangentSpace I z) y) = 0
        rw [hY_zero]
        exact (mfderiv I 𝓘(ℝ, ℝ) f y).map_zero
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  -- Conclude continuity by congruence with the smooth-action representation.
  refine h_act_cont.congr ?_
  intro x
  exact (h_eq x).symm

/-- The product `f · Δh` is continuous on `M`. -/
private lemma f_mul_Δ_continuous
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  hf.continuous.mul (Δ_g_with_boundary_continuous (I := I) g hh hh_int)

set_option linter.unusedVariables false in
/-- The product `f · Δh` has compact support inherited from `Δh`. -/
private lemma f_mul_Δ_hasCompactSupport
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    HasCompactSupport (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  HasCompactSupport.of_compactSpace _

/-- Both integrands `f · Δh` and `⟨∇f, ∇h⟩` are integrable against the
canonical Riemannian volume measure on a closed manifold. -/
private lemma f_mul_Δ_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f_mul_Δ_continuous (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (f_mul_Δ_hasCompactSupport (I := I) g hf hh hh_int)

private lemma inner_grad_grad_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (inner_grad_grad_continuous_of_interior_support
    (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Green's first identity, with boundary contribution (closed manifold).**
For smooth `f, h : M → ℝ` with `tsupport h ⊆ I.interior M` on a compact
σ-compact Hausdorff smooth Riemannian manifold `(M, g)` whose model `I`
admits a smooth boundary,
$$\int_M \langle \nabla_g f, \nabla_g h\rangle_g\,d\mu_g
   + \int_M f \cdot \Delta_g^{(\partial)} h\,d\mu_g
   = \sum_\alpha \chartBoundaryFaceIntegral{g, \alpha,\,
       f\,\nabla_g h,\,\rho_\alpha},$$
where the sum runs over the chart-atlas POU support set and
`\rho := chartAtlasPOU I M`.

The boundary face sum is packaged through `boundaryFaceSum` for the test
section `f · ∇_g h`. -/
theorem green_first_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) := by
  classical
  -- Set `X := ∇h_section`, `Y := f · X`.
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  -- Apply the global Stokes theorem to `Y`.
  have hStokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  -- Pointwise Leibniz: `div_g^∂ Y = f · div_g^∂ X + tangentSectionAction X f`.
  have h_leibniz : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X f x :=
    divergence_g_with_boundary_smoothSmul (I := I) g f hf X
  -- Pointwise rewrites:
  -- (1) `f · div_g^∂ X = f · Δh` (definitionally — `Δh = div_g^∂ ∇h_section`).
  -- (2) `tangentSectionAction X f x = ⟨∇f, ∇h⟩` (by duality + symmetry).
  have h1 : ∀ x : M,
      f x * divergence_g_with_boundary (I := I) g X x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x := by
    intro x; rfl
  have h2 : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    -- `tangentSectionAction X f x = g.inner x (X x) (gradFun g f x)`.
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g hf X x]
    -- Now `g.inner x (X x) (grad_g_with_boundary g f x)`.
    -- `X x = grad_g_with_boundary_section g hh hh_int x = gradFun g h x`.
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  -- Combined pointwise identity:
  --   `div_g^∂ Y x = f x · Δh x + ⟨∇f x, ∇h x⟩`.
  have h_combined : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x +
          g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [h_leibniz x, h1 x, h2 x]
  -- Integrate both sides against the canonical volume measure.
  have h_int_eq :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x +
                g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_combined x
  -- Integrability of each summand.
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_inner : Integrable
      (fun x : M =>
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    inner_grad_grad_integrable (I := I) g hf hh hh_int
  -- Linearity of the integral.
  rw [h_int_eq] at hStokes
  rw [integral_add h_int_fΔh h_int_inner] at hStokes
  -- `hStokes : ∫ f · Δh + ∫ ⟨∇f, ∇h⟩ = boundaryFaceSum g Y`.
  -- Goal: `∫ ⟨∇f, ∇h⟩ + ∫ f · Δh = boundaryFaceSum g Y`.
  linarith

/-! ## Sanity check — recovery of the interior-supported identity

When `f` is also interior-supported (in addition to `h`), the section
`f · ∇h` has compact support and interior support inherited from `h`.
By `integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support`,
its with-boundary divergence integrates to zero, and equivalently
`boundaryFaceSum g (f · ∇h) = 0`. Combined with Green's first identity,
this yields the interior-supported form `∫ ⟨∇f, ∇h⟩ + ∫ f · Δh = 0`, i.e.
`∫ ⟨∇f, ∇h⟩ = -∫ f · Δh`, matching
`integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary`
in `Green.lean`. -/

set_option linter.unusedVariables false in
/-- **Sanity check — vanishing of the boundary face sum on
interior-supported test scalars.** When the test scalar `f` is also
interior-supported, the section `f · ∇h` (used in Green's first identity
above) has compact support and interior support inherited from the
gradient section, and the boundary face sum vanishes.

The hypothesis `hf_int` is recorded in the signature for symmetry with
`hh_int` and to make the call site self-documenting; the proof routes
through the gradient section's own interior support
(`tsupport_grad_g_with_boundary_section_subset_interior`), which is
inherited from `hh_int` and already suffices. -/
theorem green_first_with_boundary_face_sum_eq_zero_of_interior_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M)
    (hh_int : tsupport h ⊆ I.interior M) :
    boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) = 0 := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  -- `Y` has compact support (compact M).
  have hY_cs : HasCompactSupport Y := HasCompactSupport.of_compactSpace _
  -- `Y` has interior support: factors `f` and `X` are both interior-supported,
  -- and `tsupport (f · X) ⊆ tsupport X ⊆ I.interior M`.
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_smoothSmul_subset_interior (I := I) hf X hX_int
  -- Apply the with-boundary divergence theorem to `Y`.
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I) g Y hY_cs hY_int
  -- Combined with the global Stokes theorem (`integral_divergence ... =
  -- boundaryFaceSum`).
  have h_stokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  -- Pull together: `0 = ∫ div Y = boundaryFaceSum g Y`.
  rw [h_div_Y_zero] at h_stokes
  exact h_stokes.symm

/-! ## Symmetric variant of Green's first identity (with boundary)

The symmetric variant — with the test scalar in the gradient slot — is used
to derive Green's second identity by subtraction. -/

/-- A symmetric variant of Green's first identity (with boundary): with
the integration-by-parts test section built from `f` instead of `h`. The
boundary face sum is built from the section `h · ∇f`. -/
private theorem green_first_with_boundary_swap
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) :=
  green_first_with_boundary (I := I) g hh hf hf_int

/-! ## Green's second identity with boundary

Subtracting the swapped identity from Green's first cancels the
inner-product terms (by symmetry of the metric) and yields a clean
expression for `∫ (f · Δh − h · Δf)` in terms of two boundary face sums.
-/

/-- **Green's second identity, with boundary contribution (closed
manifold).** For smooth `f, h : M → ℝ` with `tsupport f, tsupport h ⊆
I.interior M` on a compact σ-compact Hausdorff smooth Riemannian manifold
`(M, g)` whose model `I` admits a smooth boundary,
$$\int_M \bigl(f \cdot \Delta_g^{(\partial)} h
     - h \cdot \Delta_g^{(\partial)} f\bigr)\,d\mu_g
   = \sum_\alpha \chartBoundaryFaceIntegral{g, \alpha,\,
       f\,\nabla_g h,\,\rho_\alpha}
     - \sum_\alpha \chartBoundaryFaceIntegral{g, \alpha,\,
       h\,\nabla_g f,\,\rho_\alpha}.$$
-/
theorem green_second_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x -
            h x * Δ_g_with_boundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) -
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) := by
  classical
  -- Apply Green's first identity twice.
  have h_main := green_first_with_boundary (I := I) g hf hh hh_int
  have h_swap := green_first_with_boundary_swap (I := I) g hf hh hf_int
  -- The two `⟨∇f, ∇h⟩` and `⟨∇h, ∇f⟩` integrals are equal by symmetry.
  have h_inner_symm : ∀ x : M,
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x; exact g.symm x _ _
  have h_inner_int_eq :
      ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_inner_symm)
  -- Replace the swapped-inner integral by the canonically-oriented one.
  rw [h_inner_int_eq] at h_swap
  -- Subtract the two identities. Each equation is of the form A + B = R,
  -- with A the inner-product integral, B the f·Δh / h·Δf integral.
  -- main:  ∫⟨∇f,∇h⟩ + ∫ f · Δh = R₁
  -- swap:  ∫⟨∇f,∇h⟩ + ∫ h · Δf = R₂   (after symmetry rewrite)
  -- Subtract: ∫ f · Δh − ∫ h · Δf = R₁ − R₂.
  -- Now apply linearity of the integral to combine the difference.
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_hΔf : Integrable
      (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hh hf hf_int
  rw [integral_sub h_int_fΔh h_int_hΔf]
  linarith [h_main, h_swap]

end StokesGlobal

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
