import DifferentialGeometry.Analysis.Laplacian.DirichletForm
import DifferentialGeometry.Analysis.Laplacian.MetricBounds

/-!
# Bilinear-form structure of the Dirichlet form and shifted form

For an `H¹` element `u : H1Intrinsic g`, the Dirichlet form is
$$Q(u, v) = \int_M g(\nabla u, \nabla v)\, d\mu_g.$$
The shifted form is
$$B(u, v) = Q(u, v) + \int_M u\, v\, d\mu_g.$$

This file packages bilinearity of `dirichletForm` and `shiftedForm` as
`LinearMap`-valued constructions:
$$Q : H^1(M, g) \to_\ell H^1(M, g) \to_\ell \mathbb R$$
and similarly for `B`. The continuous-linear-map version (`→L[ℝ]` instead
of `→ₗ[ℝ]`) requires a uniform metric upper bound on `g.inner` over the
compact manifold, which is established in `MetricBounds.lean` (or a
dedicated downstream file when needed).

## Main definitions

* `dirichletFormLM g : H1Intrinsic g →ₗ[ℝ] H1Intrinsic g →ₗ[ℝ] ℝ` —
  the Dirichlet form as a bilinear map.
* `shiftedFormLM g : H1Intrinsic g →ₗ[ℝ] H1Intrinsic g →ₗ[ℝ] ℝ` —
  the shifted form as a bilinear map.

## Main results

* Bilinearity (additivity, scalar homogeneity) in both slots.
* Symmetry: `dirichletFormLM g u v = dirichletFormLM g v u`.
* Symmetry of `shiftedFormLM`.
* Diagonal non-negativity: `0 ≤ dirichletFormLM g u u`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

/-! ## Bilinearity of the Dirichlet form

The Dirichlet form is bilinear in both slots. Bilinearity follows from the
bilinearity of the integrand (via the linearity of `gradL2 g` in `u` and the
bilinearity of `g.inner b`) combined with the additivity of the Bochner
integral. -/

/-- Pointwise bilinear expansion: `g.inner b (G_{u₁+u₂}(b)) (G_v(b)) =
g.inner b (G_{u₁}(b)) (G_v(b)) + g.inner b (G_{u₂}(b)) (G_v(b))` (a.e.). -/
private lemma dirichletForm_integrand_add_left
    (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g u₁ : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) +
        g.inner x ((gradL2 (I := I) (M := M) g u₂ : M → E) x)
          ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  -- gradL2 is linear: gradL2 (u₁ + u₂) = gradL2 u₁ + gradL2 u₂.
  have hgrad_add : (gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      gradL2 (I := I) (M := M) g u₁ + gradL2 (I := I) (M := M) g u₂ :=
    map_add (gradL2 (I := I) (M := M) g) u₁ u₂
  -- Transfer to the function-level via Lp.coeFn_add.
  have hfn_add : (fun x : M => ((gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((gradL2 (I := I) (M := M) g u₁ :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x +
        ((gradL2 (I := I) (M := M) g u₂ :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_add]
    filter_upwards [Lp.coeFn_add (gradL2 (I := I) (M := M) g u₁)
      (gradL2 (I := I) (M := M) g u₂)] with x hx
    exact hx
  -- Apply the bilinearity of g.inner pointwise.
  filter_upwards [hfn_add] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  -- Split the sum in the first argument: g.inner x (a+b) c = g.inner x a c + g.inner x b c.
  calc g.inner x ((gradL2 g (u₁ + u₂) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x ((gradL2 g u₁ : M → E) x + (gradL2 g u₂ : M → E) x)
          ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (g.inner x ((gradL2 g u₁ : M → E) x) + g.inner x ((gradL2 g u₂ : M → E) x))
          ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_add (g.inner x) _ _
    _ = g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x) +
          g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x) := by
          rw [ContinuousLinearMap.add_apply]

private lemma dirichletForm_integrand_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_smul : (gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      c • gradL2 (I := I) (M := M) g u :=
    map_smul (gradL2 (I := I) (M := M) g) c u
  have hfn_smul : (fun x : M => ((gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c • ((gradL2 (I := I) (M := M) g u :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_smul]
    filter_upwards [Lp.coeFn_smul c (gradL2 (I := I) (M := M) g u)] with x hx
    exact hx
  filter_upwards [hfn_smul] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (c • u) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x (c • (gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (c • g.inner x ((gradL2 g u : M → E) x)) ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_smul (g.inner x) c _
    _ = c * g.inner x ((gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Additivity of the Dirichlet form in the left argument. -/
theorem dirichletForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (u₁ + u₂) v =
      dirichletForm (I := I) (M := M) g u₁ v +
        dirichletForm (I := I) (M := M) g u₂ v := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold dirichletForm
  rw [integral_congr_ae (dirichletForm_integrand_add_left
    (I := I) (M := M) g u₁ u₂ v)]
  -- Use that each summand is integrable.
  rw [integral_add ?_ ?_]
  -- Integrability: from the IsH1Pair MemLp 2 of metric g-norm + Cauchy-Schwarz.
  · -- First integrand integrable: g.inner x G_{u₁} G_v ∈ L¹.
    have hL2_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    -- |g.inner x G G'| ≤ √g(G,G) · √g(G',G') (pointwise CS), and √g(G,G), √g(G',G') ∈ L².
    -- Hence |g.inner x G G'| ∈ L¹ by Cauchy-Schwarz in L².
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g u₁ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₁ hL2_v
    · -- AESM of `g.inner x G_{u₁} G_v`. Bake into IsH1Pair with PairAEMeasurable.
      have hpair_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₁ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]
  · -- Second integrand: similar.
    have hL2_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g u₂ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₂ hL2_v
    · have hpair_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₂ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]

/-- Scalar homogeneity of the Dirichlet form in the left argument. -/
theorem dirichletForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (c • u) v =
      c * dirichletForm (I := I) (M := M) g u v := by
  unfold dirichletForm
  rw [integral_congr_ae (dirichletForm_integrand_smul_left
    (I := I) (M := M) g c u v)]
  rw [integral_const_mul]

/-- Additivity in the right argument (via symmetry). -/
theorem dirichletForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (v₁ + v₂) =
      dirichletForm (I := I) (M := M) g u v₁ +
        dirichletForm (I := I) (M := M) g u v₂ := by
  rw [dirichletForm_symm (I := I) (M := M) g u (v₁ + v₂),
    dirichletForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [dirichletForm_symm (I := I) (M := M) g v₁ u,
    dirichletForm_symm (I := I) (M := M) g v₂ u]

/-- Scalar homogeneity in the right argument (via symmetry). -/
theorem dirichletForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (c • v) =
      c * dirichletForm (I := I) (M := M) g u v := by
  rw [dirichletForm_symm (I := I) (M := M) g u (c • v),
    dirichletForm_smul_left (I := I) (M := M) g c v u,
    dirichletForm_symm (I := I) (M := M) g v u]

/-! ## The Dirichlet form as a bilinear `LinearMap`-valued map -/

/-- The Dirichlet form `Q : H¹(M, g) →ₗ[ℝ] H¹(M, g) →ₗ[ℝ] ℝ`. -/
def dirichletFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => dirichletForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => dirichletForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change dirichletForm (I := I) (M := M) g u (c • v) = _
        rw [dirichletForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change dirichletForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change dirichletForm (I := I) (M := M) g (c • u) v = _
    rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
    rfl

@[simp] lemma dirichletFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletFormLM (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g u v := rfl

/-! ## Bilinearity of the shifted form

The shifted form `B(u, v) = Q(u, v) + ⟨u, v⟩_{L²}` is bilinear because both
summands are bilinear. -/

/-- Additivity of the shifted form in the left argument. -/
theorem shiftedForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (u₁ + u₂) v =
      shiftedForm (I := I) (M := M) g u₁ v +
        shiftedForm (I := I) (M := M) g u₂ v := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold shiftedForm
  rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
  -- L² inner product: (toLp (u₁+u₂)) v = (toLp u₁) v + (toLp u₂) v.
  have h_to_add : (toLp (I := I) (M := M) g (u₁ + u₂) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      toLp (I := I) (M := M) g u₁ + toLp (I := I) (M := M) g u₂ :=
    map_add (toLp (I := I) (M := M) g) u₁ u₂
  have h_fn_add : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((toLp (I := I) (M := M) g u₁ :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x +
        ((toLp (I := I) (M := M) g u₂ :
          Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_add]
    filter_upwards [Lp.coeFn_add (toLp (I := I) (M := M) g u₁)
      (toLp (I := I) (M := M) g u₂)] with x hx
    exact hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      ∫ x : M, ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) +
      ∫ x : M, ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x) +
          ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) := by
      filter_upwards [h_fn_add] with x hx
      rw [hx, add_mul]
    rw [integral_congr_ae h_ae]
    refine integral_add ?_ ?_
    · -- Integrability: |u₁ * v| ≤ ‖u₁‖_{L²} · ‖v‖_{L²} (pointwise * Cauchy-Schwarz, finite).
      exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
    · exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
  rw [h_int_eq]
  ring

/-- Scalar homogeneity of the shifted form in the left argument. -/
theorem shiftedForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (c • u) v =
      c * shiftedForm (I := I) (M := M) g u v := by
  unfold shiftedForm
  rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
  -- L² inner product: (toLp (c•u)) * (toLp v) = c * (toLp u) * (toLp v).
  have h_to_smul : (toLp (I := I) (M := M) g (c • u) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      c • toLp (I := I) (M := M) g u :=
    map_smul (toLp (I := I) (M := M) g) c u
  have h_fn_smul : (fun x : M => ((toLp (I := I) (M := M) g (c • u) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * ((toLp (I := I) (M := M) g u :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_smul]
    filter_upwards [Lp.coeFn_smul c (toLp (I := I) (M := M) g u)] with x hx
    simpa using hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      c * ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c * (((toLp (I := I) (M := M) g u : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x))) := by
      filter_upwards [h_fn_smul] with x hx
      rw [hx]; ring
    rw [integral_congr_ae h_ae, integral_const_mul]
  rw [h_int_eq]; ring

/-- Additivity in the right argument (via symmetry). -/
theorem shiftedForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (v₁ + v₂) =
      shiftedForm (I := I) (M := M) g u v₁ +
        shiftedForm (I := I) (M := M) g u v₂ := by
  rw [shiftedForm_symm (I := I) (M := M) g u (v₁ + v₂),
    shiftedForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [shiftedForm_symm (I := I) (M := M) g v₁ u,
    shiftedForm_symm (I := I) (M := M) g v₂ u]

/-- Scalar homogeneity in the right argument (via symmetry). -/
theorem shiftedForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (c • v) =
      c * shiftedForm (I := I) (M := M) g u v := by
  rw [shiftedForm_symm (I := I) (M := M) g u (c • v),
    shiftedForm_smul_left (I := I) (M := M) g c v u,
    shiftedForm_symm (I := I) (M := M) g v u]

/-! ## The shifted form as a bilinear `LinearMap`-valued map -/

/-- The shifted form `B : H¹(M, g) →ₗ[ℝ] H¹(M, g) →ₗ[ℝ] ℝ`. -/
def shiftedFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => shiftedForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => shiftedForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change shiftedForm (I := I) (M := M) g u (c • v) = _
        rw [shiftedForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change shiftedForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [shiftedForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change shiftedForm (I := I) (M := M) g (c • u) v = _
    rw [shiftedForm_smul_left (I := I) (M := M) g c u v]
    rfl

@[simp] lemma shiftedFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedFormLM (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g u v := rfl

end H1Intrinsic

end Laplacian
end Analysis
end DifferentialGeometry

end
