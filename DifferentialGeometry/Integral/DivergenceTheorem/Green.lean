import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Integral.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Integral.DivergenceTheorem.Closed
import DifferentialGeometry.Integral.DivergenceTheorem.Proper
import DifferentialGeometry.Integral.Measure.Properties

/-!
# Green's identities on a Riemannian manifold

For a smooth Riemannian metric `g` on a smooth manifold `M` (without boundary),
the integration-by-parts machinery established in `IntegrationByParts.lean`
combines with the gradient and Laplacian to yield Green's identities.

## Main results

* `green_first_integral_inner_grad_eq_neg_integral_smul_laplacian` (**Green's first identity**):
  for smooth `f, h : M → ℝ` with `h` having compact support,
  $$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g = -\int_M f \cdot \Delta_g h\,d\mu_g.$$

* `green_second_integral_smul_laplacian_sub_eq_zero` (**Green's second identity**):
  on a closed manifold, for any smooth `f, h : M → ℝ`,
  $$\int_M (f \cdot \Delta_g h - h \cdot \Delta_g f)\,d\mu_g = 0.$$
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## File-local Borel-space instances

Match the convention in the surrounding files: `E` and `M` carry their canonical
Borel σ-algebras. Declared `local` to avoid leaking into callers. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Green's first identity

For smooth `f, h : M → ℝ` with at least one compactly supported, the gradient
of `h` is a compactly-supported smooth tangent section, and we can apply the
basic integration-by-parts identity from `IntegrationByParts.lean` with this
section. The duality `tangentSectionAction X f x = g.inner x (X x) (grad_g f x)`
(provided by `tangentSectionAction_eq_inner_grad_g`) and the symmetry of the
metric yield the integrand `g.inner x (grad_g f x) (grad_g h x)`.

Because the divergence of `grad_g h` equals the Laplacian `Δ_g h`, the right-
hand side of the IBP identity becomes the integral of `f · Δ_g h`. -/

/-- **Green's first identity.** For smooth `f, h : M → ℝ` on a σ-compact
Hausdorff smooth Riemannian manifold `(M, g)` without boundary, with `h`
compactly supported,
$$\int_M g(\nabla_g f, \nabla_g h)\,d\mu_g = -\int_M f \cdot \Delta_g h\,d\mu_g,$$
where the integrals are taken against the Riemannian volume measure `μ_g`.
Only `h` is required to have compact support; `f` is an arbitrary smooth
function. -/
theorem green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Set X := grad_g g hh, which is a smooth tangent section with compact support.
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hh with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hh hh_supp
  -- Apply identity (a) of `IntegrationByParts.lean` with this `X` and `f`.
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  -- LHS of `h_ibp`: ∫ tangentSectionAction X f.
  -- By duality `tangentSectionAction X f x = g.inner x (X x) (grad_g g hf x)`
  -- (where `X = grad_g g hh`), this equals `g.inner x (grad_g g hh x) (grad_g g hf x)`.
  -- By symmetry of the metric, equals `g.inner x (grad_g g hf x) (grad_g g hh x)`.
  -- RHS of `h_ibp`: -∫ f x * divergence_g g X x = -∫ f x * Δ_g g hh x.
  -- Hence the result.
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hf X x]
    -- `tangentSectionAction_eq_inner_grad_g` gives:
    -- `tangentSectionAction X f x = g.inner x (X x) (grad_g g hf x)`.
    -- Now with `X = grad_g g hh`, this is `g.inner x (grad_g g hh x) (grad_g g hf x)`.
    -- Apply symmetry to swap.
    change g.inner x (X x) ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g (I := I) g X x = f x * Δ_g (I := I) g hh x := by
    intro x
    -- Δ_g g hh x = divergence_g g (grad_g g hh) x = divergence_g g X x by `hX_def`.
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-! ## Green's second identity

On a closed manifold, both `f` and `h` automatically have compact support (since
the manifold is compact). Applying Green's first identity twice — once with `h`
compactly supported and once with `f` compactly supported — gives
$\int g(\nabla f, \nabla h) = -\int f \Delta h = -\int h \Delta f$, so the
integrand `f \Delta h - h \Delta f` integrates to zero.

We provide the symmetric variant of Green's first identity (with `f` having
compact support instead of `h`) as a corollary, then combine. -/

/-- A symmetric variant of Green's first identity, with the compact-support
hypothesis on `f` instead of `h`. -/
private theorem integral_inner_grad_eq_neg_integral_smul_laplacian'
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Apply the IBP identity with `X = grad_g g hf` (compactly supported) and the scalar `h`.
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hf hf_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hh X hX_cs
  -- LHS: ∫ tangentSectionAction X h x = ∫ g.inner x (X x) (grad_g g hh x)
  --      = ∫ g.inner x (grad_g g hf x) (grad_g g hh x).
  -- RHS: -∫ h x * divergence_g g X x = -∫ h x * Δ_g g hf x.
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hh X x]
  have hRHS_eq : ∀ x : M,
      h x * divergence_g (I := I) g X x = h x * Δ_g (I := I) g hf x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

/-- **Green's second identity.** For smooth `f, h : M → ℝ` on a closed (compact,
Hausdorff and boundaryless) smooth Riemannian manifold `(M, g)`,
$$\int_M (f \cdot \Delta_g h - h \cdot \Delta_g f)\,d\mu_g = 0,$$
where the integral is taken against the Riemannian volume measure `μ_g`. On a
compact manifold every smooth function is compactly supported, so this follows
by applying Green's first identity once in each argument. -/
theorem green_second_integral_smul_laplacian_sub_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∫ x, (f x * Δ_g (I := I) g hh x - h x * Δ_g (I := I) g hf x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  -- On compact M, every continuous (or smooth) function has compact support.
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  -- Green's first with `h` compactly supported.
  have h1 := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hh hh_cs
  -- Symmetric variant with `f` compactly supported.
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian' (I := I) g hf hh hf_cs
  -- From `h1` and `h2`: -∫ f * Δh = -∫ h * Δf, so ∫ f * Δh = ∫ h * Δf.
  have h_eq : ∫ x, f x * Δ_g (I := I) g hh x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    -- Use h1.symm and h2 to relate both sides.
    have : -∫ x, f x * Δ_g (I := I) g hh x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g (I := I) g hf x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  -- Now expand the integral of the difference.
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  -- Both `f * Δh` and `h * Δf` are continuous on compact `M`, hence integrable.
  have hΔh_cont : Continuous (Δ_g (I := I) g hh) :=
    (Δ_g_contMDiff (I := I) g hh).continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) :=
    (Δ_g_contMDiff (I := I) g hf).continuous
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g (I := I) g hh x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g (I := I) g hh x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g (I := I) g hf x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g (I := I) g hf x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

end DivergenceTheorem
end Integral
end DifferentialGeometry
