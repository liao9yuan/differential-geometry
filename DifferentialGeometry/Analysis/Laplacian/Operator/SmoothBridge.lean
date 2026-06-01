import DifferentialGeometry.Analysis.Laplacian.Operator.DirichletForm
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Analysis.Laplacian.Operator.Variational

/-!
# Smooth-function inclusion into the intrinsic `H¹` space

For a smooth function `f : M → ℝ` on a closed Riemannian manifold `(M, g)`,
the gradient `gradFun g f` is a smooth tangent section. This file packages
the L² class of `f` together with the L² class of `gradFun g f` as an
element of the intrinsic `H¹` space `H1Intrinsic g`.

The construction is delivered via `smoothInclude`: given `f` and a smoothness
hypothesis, it produces an `H¹` element whose `toLp` equals the L² class of
`f` and whose `gradL2` equals the L² class of `gradFun g f`.

The verification of the joint AESM pairing clause `PairAEMeasurable` for the
smooth witness is performed at this point. We use the fact that for smooth
functions, the gradient is continuous and so the pairing
`x ↦ g.inner x (gradFun g f x) (V x)` against any AESM `V` reduces — via a
chart-by-chart bilinear-form decomposition — to AESM operations on AESM
inputs.

## Main definitions

* (forthcoming) `smoothInclude g f hf` : the `H¹` element associated to a
  smooth function.

This file lays the groundwork for the smooth bridge; the full construction
including the joint AESM verification depends on chart-localized
infrastructure that is beyond the immediate scope.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Completion bridge

This section connects the variational Laplacian via Lax-Milgram (`resolvent`)
to the classical Laplace-Beltrami operator (`Δ_g`) on smooth functions, on a
closed Riemannian manifold `(M, g)`.

The bridge identity is Green's first identity. For smooth `u, v : M → ℝ`,

  B(smooth-lift u, smooth-lift v)
    = ∫ u · v dμ_g + ∫ g(grad_g u, grad_g v) dμ_g
    = ∫ u · v dμ_g - ∫ v · Δ_g u dμ_g     (by Green's first identity)
    = ∫ (u - Δ_g u) · v dμ_g
    = ⟨L²-class of (u - Δ_g u), L²-class of v⟩_{L²}.

By density of smooth scalars in `H1Compl g`, this characterises the smooth lift
of `u` as the unique solution to the variational equation
`B(·, v) = ⟨L²-class of (u - Δ_g u), v⟩` for every test `v ∈ H1Compl g`,
i.e. the resolvent of `(1 - Δ_g)` applied to the L² class of `(u - Δ_g u)`. -/

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ### The classical "(1 - Δ_g) u" as a smooth scalar -/

/-- For a smooth scalar `u`, the classical `(1 - Δ_g) u := u - Δ_g u` is again
a smooth scalar. -/
noncomputable def SmoothScalar.oneSubLapClassical {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) : SmoothScalar g where
  toFun := u.toFun - Δ_g (I := I) g u.smooth
  smooth := u.smooth.sub (Δ_g_contMDiff (I := I) g u.smooth)

@[simp] lemma SmoothScalar.oneSubLapClassical_toFun
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    (u.oneSubLapClassical).toFun =
      u.toFun - Δ_g (I := I) g u.smooth := rfl

/-! ### Identity from Green's first identity

For smooth `u` and a smooth test `v` with both compactly supported (which is
automatic on a closed `M`), Green's first identity gives

  ∫ g(grad u, grad v) = -∫ v · Δ_g u.

Hence

  ⟨u, v⟩_{H1-pre} = ∫ u·v + ∫ g(grad u, grad v) = ∫ (u - Δ_g u) · v.
-/

/-- The Green-identity computation: the H¹ inner product equals an L²
inner product against `(u - Δ_g u)`. -/
theorem smoothScalarH1Inner_eq_integral_oneSubLap_mul
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ∫ x, (u.toFun x - Δ_g (I := I) g u.smooth x) * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold smoothScalarH1Inner
  -- Apply Green's first identity to swap the gradient term for `-∫ v · Δ_g u`.
  -- `green_first_integral_inner_grad_eq_neg_integral_smul_laplacian`:
  --   `∫ g(grad u, grad v) = -∫ u · Δ_g v` (when v is compactly supported).
  -- For the symmetric variant putting Δ on u, use the result with roles of u, v swapped:
  --   `∫ g(grad v, grad u) = -∫ v · Δ_g u`.
  -- Then `∫ g(grad u, grad v) = ∫ g(grad v, grad u)` by symmetry of g.
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hv_cs : HasCompactSupport v.toFun := HasCompactSupport.of_compactSpace _
  have hu_cs : HasCompactSupport u.toFun := HasCompactSupport.of_compactSpace _
  -- Green's first identity with `(f, h) = (v, u)` and `u` compactly supported:
  --   `∫ g(grad v, grad u) = -∫ v · Δ_g u`.
  have hgreen :
      ∫ x, g.inner x ((grad_g (I := I) g v.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g u.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, v.toFun x * Δ_g (I := I) g u.smooth x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g v.smooth u.smooth hu_cs
  -- Symmetry of g: `∫ g(grad u, grad v) = ∫ g(grad v, grad u)`.
  have hsymm :
      (∫ x, g.inner x ((grad_g (I := I) g u.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g v.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, g.inner x ((grad_g (I := I) g v.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g u.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _
  rw [hsymm, hgreen]
  -- Now combine: `∫ u·v + (-∫ v · Δu) = ∫ (u - Δu) · v`.
  have hΔu_cont : Continuous (Δ_g (I := I) g u.smooth) :=
    (Δ_g_contMDiff (I := I) g u.smooth).continuous
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  -- Both `u·v` and `v · Δu` are integrable.
  have h_uv : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu : Integrable (fun x : M => v.toFun x * Δ_g (I := I) g u.smooth x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Pointwise: `(u x - Δu x) * v x = u x * v x - v x * Δu x`.
  have hpt : ∀ x : M,
      (u.toFun x - Δ_g (I := I) g u.smooth x) * v.toFun x =
        u.toFun x * v.toFun x - v.toFun x * Δ_g (I := I) g u.smooth x := by
    intro x; ring
  rw [show (fun x : M =>
      (u.toFun x - Δ_g (I := I) g u.smooth x) * v.toFun x) =
      (fun x : M =>
        u.toFun x * v.toFun x - v.toFun x * Δ_g (I := I) g u.smooth x) from
      funext hpt]
  rw [integral_sub h_uv h_vΔu]
  ring

/-- Reformulation of the H¹ inner product on smooth scalars as a Riemannian
L² inner product against `(u - Δ_g u)`. -/
theorem smoothScalarH1Inner_eq_lpInner_oneSubLap
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ⟪smoothToLp (I := I) (M := M) g u.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g v⟫_ℝ := by
  rw [smoothScalarH1Inner_eq_integral_oneSubLap_mul]
  -- L² inner product on Lp ℝ 2 of (u - Δu).toLp · v.toLp.
  rw [L2.inner_def
    (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
    (smoothToLp (I := I) (M := M) g v)]
  -- a.e.-rewrite the L² integrand to the pointwise integrand.
  have hae_lhs : (smoothToLp (I := I) (M := M) g u.oneSubLapClassical :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      u.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp u.oneSubLapClassical.memLp_two
  have hae_rhs : (smoothToLp (I := I) (M := M) g v :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  -- `⟨a, b⟩_ℝ = b * a` for ℝ.
  -- LHS: `(u.toFun x - Δ_g g u.smooth x) * v.toFun x`.
  -- RHS: `⟨u.oneSubLapClassical.toFun x, v.toFun x⟩_ℝ = v.toFun x * (u.toFun x - Δ_g g u.smooth x)`.
  rw [SmoothScalar.oneSubLapClassical_toFun]
  -- Now LHS : `(u.toFun x - Δ_g …) * v.toFun x`,
  -- RHS : `⟨(u.toFun - Δ_g … ) x, v.toFun x⟩_ℝ`.
  change (u.toFun x - Δ_g (I := I) g u.smooth x) * v.toFun x =
    @inner ℝ _ _ ((u.toFun - Δ_g (I := I) g u.smooth) x) (v.toFun x)
  rw [Pi.sub_apply]
  -- `⟨a, b⟩_ℝ = b * a` (by RCLike.inner_apply, conj_trivial).
  rw [show @inner ℝ _ _ (u.toFun x - Δ_g (I := I) g u.smooth x) (v.toFun x) =
      v.toFun x * (u.toFun x - Δ_g (I := I) g u.smooth x) from
      RCLike.inner_apply _ _]
  ring

/-! ### Variational identity for smooth lifts

Translating the H¹-inner-product identity through the smooth-inclusion into
`H1Compl g` gives the variational identity for smooth lifts. -/

/-- Inner product on `H1Compl g` of two smooth lifts equals the smooth
H¹-inner-product. -/
@[simp] lemma inner_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl (I := I) (M := M) g v⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  -- `smoothToH1Compl = toComplL` and `inner` on `Completion` extends `inner` on the
  -- pre-Hilbert; for the embedding `inner_coe`.
  unfold smoothToH1Compl
  -- `toComplL u = (u : Completion _)` definitionally.
  change ⟪((u : H1Compl g) : H1Compl g),
        ((v : H1Compl g) : H1Compl g)⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v
  -- `H1Compl g = Completion (SmoothScalar g)`. `inner_coe : ⟨↑a, ↑b⟩ = ⟨a, b⟩`.
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

/-- For smooth lifts `u, v ∈ SmoothScalar g`, the bilinear form on the H¹
completion at `(smooth-lift u, smooth-lift v)` agrees with the smooth-scalar
H¹ inner product. -/
@[simp] lemma H1ComplBilin_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  rw [H1ComplBilin_apply]
  exact inner_smoothToH1Compl_smoothToH1Compl u v

/-- The variational identity at smooth test functions. -/
theorem smoothScalar_bilin_eq_lpFunctional_smooth
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
        (smoothToH1Compl (I := I) (M := M) g v) := by
  rw [H1ComplBilin_smoothToH1Compl_smoothToH1Compl,
    smoothScalarH1Inner_eq_lpInner_oneSubLap]
  rw [lpFunctionalCLM_apply, H1ComplToLp_smoothToH1Compl]
  -- Both sides are inner products in `Lp` of `(smoothToLp v)` and `(smoothToLp (u-Δu))`;
  -- the order on the LHS is `⟨smoothToLp (u-Δu), smoothToLp v⟩` and on the RHS is reversed.
  exact real_inner_comm _ _

/-! ### Density of `smoothToH1Compl` in `H1Compl` -/

/-- The image of `smoothToH1Compl` in `H1Compl g` is dense. -/
theorem denseRange_smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-! ### Smooth bridge: smooth lifts solve the variational equation -/

/-- For any smooth scalar `u`, its lift into `H1Compl g` solves the variational
equation `B(u, v) = ⟨smoothToLp (u - Δ_g u), H1ComplToLp v⟩` for every test
`v ∈ H1Compl g`. -/
theorem smoothToH1Compl_bilin_eq_lpFunctional
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) (w : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u) w =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w := by
  -- The equation is closed under taking limits in `w` (both sides continuous in `w`).
  -- It holds for `w = smoothToH1Compl v` for any `v ∈ SmoothScalar g`.
  -- By density of `smoothToH1Compl`, it holds for all `w`.
  let L : H1Compl g → ℝ := fun w =>
    H1ComplBilin (I := I) (M := M) g (smoothToH1Compl (I := I) (M := M) g u) w
  let R : H1Compl g → ℝ := fun w =>
    lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w
  change L w = R w
  -- `L` and `R` are continuous in `w`.
  have hL_cont : Continuous L :=
    (H1ComplBilin (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)).continuous
  -- `L = R` on the range of `smoothToH1Compl`.
  have hLR_smooth :
      L ∘ (smoothToH1Compl (I := I) (M := M) g) =
        R ∘ (smoothToH1Compl (I := I) (M := M) g) := by
    funext v
    -- `L (smoothToH1Compl v) = R (smoothToH1Compl v)` is the smooth-test variational identity.
    exact smoothScalar_bilin_eq_lpFunctional_smooth u v
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

/-- **Smooth bridge.** The lift of a smooth scalar `u` to `H1Compl g` is the
resolvent of `(1 - Δ_g)` applied to the L² class of `(u - Δ_g u)`. -/
theorem smoothToH1Compl_eq_resolvent_oneSubLap
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) := by
  -- Two elements of a Hilbert space are equal iff they have the same inner product
  -- against every test vector. We apply `ext_inner_right` after rewriting using
  -- the variational identity satisfied by both sides.
  apply ext_inner_right ℝ
  intro w
  -- LHS: ⟨smoothToH1Compl u, w⟩ = B(smoothToH1Compl u, w)
  --                              = ⟨smoothToLp (u - Δu), H1ComplToLp w⟩_{Lp}
  rw [show ⟪smoothToH1Compl (I := I) (M := M) g u, w⟫_ℝ =
        H1ComplBilin (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g u) w from rfl]
  rw [smoothToH1Compl_bilin_eq_lpFunctional u w]
  -- RHS: ⟨resolvent g (smoothToLp (u - Δu)), w⟩ = lpFunctional g (smoothToLp (u - Δu)) w
  --                                            (by definition of resolvent)
  rw [resolvent_inner_eq_lpFunctional]
  rw [lpFunctionalCLM_apply]

/-! ### A diagnostic statement of the smooth bridge

Restated in terms of `(u, hu)` for an explicit smooth scalar function. -/

/-- **Smooth bridge, function-level form.** For a smooth real-valued function
`u : M → ℝ` on a closed Riemannian manifold `(M, g)` (with smoothness witness
`hu`), wrap into `SmoothScalar g`. Then `smoothToH1Compl u` is the resolvent
of `(1 - Δ_g)` applied to the L² class of `(u - Δ_g u)`. -/
theorem smoothToH1Compl_eq_resolvent_oneSubLap_of_function
    (g : SmoothRiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    smoothToH1Compl (I := I) (M := M) g
        ⟨u, hu⟩ =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (⟨u, hu⟩ : SmoothScalar g).oneSubLapClassical) :=
  smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) ⟨u, hu⟩

/-! ### Compatibility with the classical Laplacian

For a smooth scalar `u`, `(1 - Δ_g) u` (the classical Laplacian applied to `u`,
shifted by the identity) is itself smooth, and the variational identity reads

  resolvent g (smoothToLp ((1 - Δ_g) u)) = smoothToH1Compl u.

In particular, the resolvent restricted to the image of smooth scalars under
`smoothToLp ∘ oneSubLapClassical` recovers the smooth lift to `H1Compl`. -/

/-- Classical-Laplacian compatibility: for a smooth scalar `u`, the smooth
`H1Compl`-lift of `u` solves the variational equation `(1 - Δ_g) u = (u - Δu)`
in the L²-distributional sense. -/
theorem resolvent_smoothToLp_oneSubLapClassical
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) =
      smoothToH1Compl (I := I) (M := M) g u :=
  (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u).symm

end Laplacian
end Analysis
end DifferentialGeometry

end
