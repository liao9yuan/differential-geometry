import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerLaplacianM32SmoothFullUnconditional
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerLaplacianM32DensityExtension

/-!
# Integral-form variational identity for `gradInnerCLM g φ u_h`

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and an element `u_h ∈ laplacianDomainPow g 2`, this module
states and proves the **integral-form variational identity**

```
∫ g(∇φ, ∇u_h)(x) · ((1 - Δ_g) w)(x) dμ_g(x) = ∫ F(x) · w(x) dμ_g(x)
```

valid for every smooth test scalar `w : SmoothScalar g`. Here:

* `g(∇φ, ∇u_h)` is the `Lp 2 μ_g` class `gradInnerCLM g φ u_h`.
* `w` is the underlying smooth function and `Δ_g w` is its classical Laplacian.
* `F : Lp ℝ 2 μ_g` is an explicit Lp 2 class playing the role of the
  resolvent-side Bochner cross-term, namely
  `laplacianDomain.preimage ⟨w_lift, hw_lift⟩`, where
  `w_lift ∈ laplacianDomain g` is the H¹Compl-lift of `gradInnerCLM g φ u_h`.

## Mathematical content

The identity is the **weak-Laplacian formulation** of `(1 - Δ_g) A = F`, where
`A := gradInnerCLM g φ u_h`. Equivalently, `A` is the `H1ComplToLp` image of
`resolvent g F` (i.e., the variational identity at the H¹Compl level).

The integral form follows from the abstract Lax–Milgram variational identity
`resolvent_inner_eq_lpFunctional` combined with the smooth bridge
`smoothToH1Compl u = resolvent g (smoothToLp u.oneSubLapClassical)`.

## Strategy

For `u_h ∈ H1Compl g`, assume there exists `w_lift ∈ laplacianDomain g` with
`H1ComplToLp w_lift = gradInnerCLM g φ u_h` (this is the M3.2 image-membership
form, conditional in general on the Bochner discharge hypotheses, but
unconditional in the smooth case).

The integral identity follows from two evaluations of the abstract
inner-product identity:

1. `⟨w_lift, smoothToH1Compl w⟩_{H1Compl}` evaluated as
   `⟨gradInnerCLM g φ u_h, smoothToLp w.oneSubLapClassical⟩_{Lp}`
   (via the smooth bridge for `smoothToH1Compl`).

2. `⟨w_lift, smoothToH1Compl w⟩_{H1Compl}` evaluated as
   `⟨smoothToLp w, F⟩_{Lp}`
   (via `resolvent_inner_eq_lpFunctional` applied with `f := F`).

Equating the two and unfolding `L2.inner_def` gives the integral-form
identity. For ℝ-valued Lp the inner product is `⟪a, b⟫_ℝ = b * a` pointwise,
producing the asserted integral.

## Main results

* `lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage` — the
  Lp-class formulation:
  `⟨gradInnerCLM g φ u_h, smoothToLp w.oneSubLapClassical⟩_{Lp} =
   ⟨smoothToLp w, F⟩_{Lp}`
  for any `u_h ∈ H1Compl g` with an H1Compl-lift in `laplacianDomain g`.

* `integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth` — the
  integral form, manifold-side:
  `∫ A · (1 - Δ_g) w dμ_g = ∫ F · w dμ_g`.

* `integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth_smoothCase`
  — the integral identity for smooth `v : SmoothScalar g` with
  `u_h := smoothToH1Compl v`, conditional on the Christoffel discharge
  hypothesis from `HessianChartAlphaChristoffelDischarge`.

* `integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth_density` —
  the integral identity for `u_h ∈ laplacianDomainPow g 2` under the density
  hypotheses from `GradInnerLaplacianM32DensityExtension`.

## Connection to the Bochner cross-term identity

The integral-form identity is the **weak content** of the polarised
Bochner–Weitzenböck identity at the `Lp` level. The smooth-case form makes
this manifest: `F = (1 - Δ_g)(g(∇φ, ∇v))` (as a smooth scalar, in classical
form), and the identity asserts the weak-Laplacian transfer:

```
∫ g(∇φ, ∇v) · (1 - Δ_g) w = ∫ (1 - Δ_g)(g(∇φ, ∇v)) · w
```

which, after manipulation, is the standard integration-by-parts identity
(`Δ_g` is symmetric under the L² inner product).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerVariationalIntegralForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32SmoothFull
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32SmoothFullUnconditional
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32DensityExtension

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Section A — Abstract variational identity in Lp-inner-product form

For `A ∈ Lp 2 μ_g` with a Hilbert lift `w_lift ∈ laplacianDomain g`
(i.e. `H1ComplToLp w_lift = A`), the abstract Lax–Milgram identity gives a
canonical evaluation of `⟨A, smoothToLp w.oneSubLapClassical⟩_{Lp}` for any
smooth `w : SmoothScalar g`. -/

/-- **Abstract variational identity in Lp inner-product form.** For
`w_lift ∈ laplacianDomain g` and smooth `w : SmoothScalar g`,

```
⟨H1ComplToLp w_lift, smoothToLp w.oneSubLapClassical⟩_{Lp} =
  ⟨smoothToLp w, laplacianDomain.preimage ⟨w_lift, hw_lift⟩⟩_{Lp}.
```

This is the integral-pairing form of the resolvent variational identity. -/
theorem lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  classical
  -- Strategy: show both sides equal ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}.
  -- LHS = ⟨H1ComplToLp w_lift, smoothToLp w.oneSubLap⟩_{Lp}
  --     = ⟨smoothToLp w.oneSubLap, H1ComplToLp w_lift⟩_{Lp}  (real symmetry)
  --     = ⟨smoothToLp w.oneSubLap, H1ComplToLp w_lift⟩_{Lp}
  --   ↑ apply resolvent_inner_eq_lpFunctional in reverse:
  --     ⟨H1ComplToLp v, f⟩_{Lp} = ⟨resolvent f, v⟩_{H1Compl}
  --   with f := smoothToLp w.oneSubLap, v := w_lift:
  --     ⟨resolvent (smoothToLp w.oneSubLap), w_lift⟩_{H1Compl}
  --     = ⟨smoothToH1Compl w, w_lift⟩_{H1Compl}                  (smooth bridge)
  --     = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}                 (real symmetry).
  -- RHS = ⟨smoothToLp w, preimage⟨w_lift⟩⟩_{Lp}
  --     = ⟨H1ComplToLp(smoothToH1Compl w), preimage⟨w_lift⟩⟩_{Lp}    (H1ComplToLp ∘ smoothToH1Compl = smoothToLp)
  --     = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}                 (variational id at preimage⟨w_lift⟩).
  -- Both sides equal ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}, hence equal.
  -- Use two variational identities: one for smoothToH1Compl w (via the smooth
  -- bridge to resolvent), and one for the resolvent of preimage⟨w_lift⟩.
  -- The H1Compl inner ⟨w_lift, smoothToH1Compl w⟩ unifies both sides.
  --
  -- LHS = ⟨H1ComplToLp w_lift, smoothToLp w.oneSubLap⟩_{Lp}
  --     = (since smoothToH1Compl w = resolvent (smoothToLp w.oneSubLap))
  --       ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}  (via real_inner_comm + resolvent ↔ Lp).
  -- RHS = ⟨smoothToLp w, preimage⟨w_lift⟩⟩_{Lp}
  --     = ⟨H1ComplToLp(smoothToH1Compl w), preimage⟨w_lift⟩⟩_{Lp}
  --     = ⟨resolvent(preimage⟨w_lift⟩), smoothToH1Compl w⟩_{H1Compl}  (variational identity)
  --     = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}  (since resolvent ∘ preimage = id).
  --
  -- Concretely, h_LHS: LHS = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}.
  -- h_RHS: RHS = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}.
  -- Conclude LHS = RHS by transitivity.
  have h_LHS : ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    -- ⟨H1ComplToLp w_lift, smoothToLp w.oneSubLap⟩_{Lp}
    --   = ⟨resolvent (smoothToLp w.oneSubLap), w_lift⟩_{H1Compl}  (variational id reversed)
    --   = ⟨smoothToH1Compl w, w_lift⟩_{H1Compl}  (smooth bridge)
    --   = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}  (real_inner_comm).
    -- Swap RHS first: ⟪w_lift, smoothToH1Compl w⟫ = ⟪smoothToH1Compl w, w_lift⟫.
    rw [show ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
        ⟪smoothToH1Compl (I := I) (M := M) g w, w_lift⟫_ℝ from
      real_inner_comm _ _]
    rw [show smoothToH1Compl (I := I) (M := M) g w =
        resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) from
      smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) w]
    exact (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) w_lift).symm
  have h_RHS : ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    -- ⟨smoothToLp w, preimage⟨w_lift⟩⟩_{Lp}
    --   = ⟨H1ComplToLp(smoothToH1Compl w), preimage⟨w_lift⟩⟩_{Lp}
    --   = ⟨resolvent (preimage⟨w_lift⟩), smoothToH1Compl w⟩_{H1Compl}  (variational id)
    --   = ⟨w_lift, smoothToH1Compl w⟩_{H1Compl}  (since resolvent ∘ preimage = ↑·).
    rw [show smoothToLp (I := I) (M := M) g w =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g w) from
      (H1ComplToLp_smoothToH1Compl (I := I) (M := M) g w).symm]
    have h_var := (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩)
      (smoothToH1Compl (I := I) (M := M) g w)).symm
    -- h_var: ⟨H1ComplToLp(smoothToH1Compl w), preimage⟨w_lift⟩⟩_{Lp}
    --      = ⟨resolvent (preimage⟨w_lift⟩), smoothToH1Compl w⟩_{H1Compl}.
    rw [h_var]
    -- Goal: ⟨resolvent (preimage⟨w_lift⟩), smoothToH1Compl w⟩ = ⟨w_lift, smoothToH1Compl w⟩.
    -- Since resolvent (preimage⟨w_lift⟩) = ↑⟨w_lift, hw_lift⟩ = w_lift (cast).
    congr 1
    exact resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w_lift, hw_lift⟩
  rw [h_LHS, h_RHS]

/-! ## Section B — Specialisation to `gradInnerCLM g φ u_h`

When the M3.2 hypothesis holds — i.e., when `gradInnerCLM g φ u_h ∈
H1ComplToLp '' laplacianDomain g` — the abstract identity above specialises
to give the variational identity for `gradInnerCLM g φ u_h`. -/

/-- **Variational identity for `gradInnerCLM g φ u_h` in Lp inner-product form,
hypothesis-bearing**. Given `w_lift ∈ laplacianDomain g` with
`H1ComplToLp w_lift = gradInnerCLM g φ u_h`, for every smooth `w : SmoothScalar g`,

```
⟨gradInnerCLM g φ u_h, smoothToLp w.oneSubLapClassical⟩_{Lp} =
  ⟨smoothToLp w, laplacianDomain.preimage ⟨w_lift, hw_lift⟩⟩_{Lp}.
```
-/
theorem lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ⟪gradInnerCLM (I := I) (M := M) g φ u_h,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  rw [← h_witness]
  exact lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w

/-! ## Section C — Integral form (manifold side)

Unfolding `L2.inner_def`, the Lp inner product becomes a manifold integral.
For ℝ-valued Lp functions, `⟪f, h⟫_ℝ` corresponds to `∫ h · f dμ_g`. -/

/-- **Integral-form variational identity for `H1ComplToLp w_lift`**. For
`w_lift ∈ laplacianDomain g` and any smooth `w : SmoothScalar g`,

```
∫ (H1ComplToLp w_lift)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · (laplacianDomain.preimage ⟨w_lift, hw_lift⟩)(x) dμ_g(x).
```

The left-hand side is the action of `H1ComplToLp w_lift` against `(1-Δ_g) w`
in the L² pairing; the right-hand side is the action of the preimage against
`w`. -/
theorem integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Start from the abstract Lp-inner identity.
  have h_abs := lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w
  -- Unfold both Lp inner products via L2.inner_def.
  rw [L2.inner_def, L2.inner_def] at h_abs
  -- LHS_inner = ∫ ⟪H1ComplToLp w_lift, smoothToLp w.oneSubLap⟫_ℝ
  --           = ∫ (smoothToLp w.oneSubLap)(x) * (H1ComplToLp w_lift)(x)
  -- RHS_inner = ∫ ⟪smoothToLp w, preimage⟨w_lift⟩⟫_ℝ
  --           = ∫ (preimage⟨w_lift⟩)(x) * (smoothToLp w)(x)
  -- Bridge to the asserted form using ae coeFn unfolding for smoothToLp.
  -- We rewrite each side as integrals over the manifold via ae-equality.
  have h_LHS_coe :
      ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x - Δ_g (I := I) g w.smooth x) := by
    -- smoothToLp g w.oneSubLapClassical = w.oneSubLapClassical.memLp_two.toLp ...
    -- by smoothToLp_apply. Its coeFn coincides with w.oneSubLapClassical.toFun a.e.
    have h := MemLp.coeFn_toLp w.oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    -- hx : (w.oneSubLapClassical.memLp_two.toLp w.oneSubLapClassical.toFun) x = w.oneSubLapClassical.toFun x.
    -- We want: (smoothToLp g w.oneSubLapClassical) x = w.toFun x - Δ_g w x.
    -- (smoothToLp g w.oneSubLapClassical) x = (w.oneSubLapClassical.memLp_two.toLp ...) x = w.oneSubLapClassical.toFun x
    -- = w.toFun x - Δ_g w x by oneSubLapClassical_toFun.
    change ((w.oneSubLapClassical.memLp_two.toLp _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x = _
    rw [hx]
    rfl
  have h_RHS_coe :
      ((smoothToLp (I := I) (M := M) g w :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x) := MemLp.coeFn_toLp w.memLp_two
  -- Now apply integral_congr_ae.
  -- The LHS integrand is ⟪H1ComplToLp w_lift x, smoothToLp w.oneSubLap x⟫_ℝ
  --   = smoothToLp w.oneSubLap x * H1ComplToLp w_lift x  (RCLike inner on ℝ).
  -- Replace smoothToLp w.oneSubLap x with (w.toFun - Δ_g w)(x).
  have h_LHS_integral :
      ∫ a, @inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
              (w.toFun x - Δ_g (I := I) g w.smooth x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae ?_
    filter_upwards [h_LHS_coe] with x hx
    -- ⟪a, b⟫_ℝ = b * a for ℝ-valued inner product.
    have h_inner_apply :
        @inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    -- Now use hx to rewrite the smoothToLp w.oneSubLap value as (w.toFun - Δ_g w).
    -- hx : (smoothToLp w.oneSubLap)(x) = (w.toFun x - Δ_g w x).
    -- The goal: (smoothToLp w.oneSubLap)(x) * (H1ComplToLp w_lift)(x)
    --         = (H1ComplToLp w_lift)(x) * (w.toFun x - Δ_g w x).
    change _ * _ = _ * _
    rw [hx]
    ring
  have h_RHS_integral :
      ∫ a, @inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, w.toFun x *
              ((laplacianDomain.preimage (I := I) (M := M) g
                  ⟨w_lift, hw_lift⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae ?_
    filter_upwards [h_RHS_coe] with x hx
    have h_inner_apply :
        @inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    change _ * _ = _ * _
    rw [hx]
    ring
  -- Combine h_abs with the two integral rewrites.
  -- h_abs has the form: ⟪H1ComplToLp w_lift, smoothToLp w.oneSubLap⟫_ℝ =
  --                     ⟪smoothToLp w, preimage⟨w_lift⟩⟫_ℝ
  -- After L2.inner_def unfolding (already done):
  -- ∫ ⟪H1ComplToLp w_lift x, smoothToLp w.oneSubLap x⟫_ℝ = ∫ ⟪smoothToLp w x, preimage⟨w_lift⟩ x⟫_ℝ.
  -- We rewrite each side using h_LHS_integral and h_RHS_integral.
  rw [← h_LHS_integral, ← h_RHS_integral]
  exact h_abs

/-- **Integral-form variational identity for `gradInnerCLM g φ u_h`,
hypothesis-bearing**. Given `w_lift ∈ laplacianDomain g` with
`H1ComplToLp w_lift = gradInnerCLM g φ u_h`, for every smooth
`w : SmoothScalar g`,

```
∫ g(∇φ, ∇u_h)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · (laplacianDomain.preimage ⟨w_lift, hw_lift⟩)(x) dμ_g(x).
```

The left-hand integrand `g(∇φ, ∇u_h)(x)` is interpreted via the coeFn of
`gradInnerCLM g φ u_h`; on the smooth subspace `u_h := smoothToH1Compl v`
it agrees with the pointwise smooth function `b ↦ g.inner b (∇φ b) (∇v b)`. -/
theorem integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← h_witness]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

/-! ## Section D — Specialisation to the M3.2 candidate (smooth case)

For smooth `v : SmoothScalar g` with `u_h := smoothToH1Compl v` and
`hu_h := smoothToH1Compl_mem_laplacianDomainPow_two g v`, the witness
`w_lift := smoothGradInnerWitness g φ v` (i.e. `smoothToH1Compl
(gradInnerSmoothBundle g φ v)`) satisfies `H1ComplToLp w_lift =
gradInnerCLM g φ (smoothToH1Compl v)`, unconditionally. The corresponding
Lp preimage is `smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)`.

The integral identity then takes the form

```
∫ g(∇φ, ∇v)(x) · (1 - Δ_g) w(x) dμ_g(x) =
  ∫ w(x) · (1 - Δ_g)(g(∇φ, ∇v))(x) dμ_g(x).
```
-/

/-- **Integral form, smooth case via the `smoothGradInnerWitness`**. For smooth
`v : SmoothScalar g` and smooth `w : SmoothScalar g`,

```
∫ g(∇φ, ∇v)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · (1 - Δ_g)(g(∇φ, ∇v))(x) dμ_g(x).
```

The right-hand side is the integral against the smooth Lp class of
`(gradInnerSmoothBundle g φ v).oneSubLapClassical`, i.e. the classical
`(1 - Δ_g)(g(∇φ, ∇v))`. -/
theorem integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase_unconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((smoothToLp (I := I) (M := M) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- We use w_lift := smoothGradInnerWitness g φ v with its known properties.
  set w_lift : H1Compl (I := I) (M := M) g :=
    smoothGradInnerWitness (I := I) (M := M) g φ v with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact smoothGradInnerWitness_mem_laplacianDomain (I := I) (M := M) g φ v
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
    rw [hw_lift_def]
    exact H1ComplToLp_smoothGradInnerWitness (I := I) (M := M) g φ v
  -- Apply the hypothesis-bearing form.
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  -- Identify preimage ⟨w_lift, hw_lift_mem⟩ with smoothToLp(...).oneSubLap.
  -- w_lift = smoothToH1Compl(gradInnerSmoothBundle g φ v).
  -- By smoothToH1Compl_eq_resolvent_oneSubLap, this equals
  -- resolvent (smoothToLp(gradInnerSmoothBundle g φ v).oneSubLapClassical).
  -- Hence preimage = smoothToLp(gradInnerSmoothBundle g φ v).oneSubLapClassical.
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
    apply resolvent_injective (I := I) (M := M) g
    -- Goal: resolvent (preimage ⟨w_lift, hw_lift_mem⟩) = resolvent (smoothToLp ...).
    -- LHS reduces to ↑⟨w_lift, hw_lift_mem⟩ = w_lift via resolvent_laplacianDomain_preimage_eq.
    -- RHS: resolvent (smoothToLp ...) = smoothToH1Compl (gradInnerSmoothBundle g φ v) (smooth bridge).
    -- Both equal w_lift (= smoothGradInnerWitness = smoothToH1Compl (gradInnerSmoothBundle)).
    have h_lhs := resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g
      ⟨w_lift, hw_lift_mem⟩
    -- h_lhs: resolvent (preimage ⟨w_lift, hw_lift_mem⟩) = ↑⟨w_lift, hw_lift_mem⟩ = w_lift.
    rw [h_lhs]
    -- Goal: ↑⟨w_lift, hw_lift_mem⟩ = resolvent (smoothToLp ...).
    -- ↑⟨w_lift, hw_lift_mem⟩ = w_lift definitionally; w_lift = smoothGradInnerWitness g φ v
    -- = smoothToH1Compl (gradInnerSmoothBundle g φ v)
    -- = resolvent (smoothToLp (gradInnerSmoothBundle g φ v).oneSubLapClassical) (smooth bridge).
    change w_lift = _
    rw [hw_lift_def]
    unfold smoothGradInnerWitness
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
      (gradInnerSmoothBundle (I := I) (M := M) g φ v)
  -- Substitute the preimage in the RHS of h_main.
  rw [h_preimage_eq] at h_main
  exact h_main

/-! ## Section E — Specialisation to `u_h ∈ laplacianDomainPow g 2` via M3.2

For arbitrary `u_h ∈ laplacianDomainPow g 2`, the witness is the resolvent
of `gradInnerLaplacianCandidateUnconditional g φ hu_h`, and the
preimage is the candidate itself, **conditional** on the variational
identity hypothesis. -/

/-- **Integral form for arbitrary `u_h ∈ laplacianDomainPow g 2`, variational-identity-bearing**.
Given the variational identity for the unconditional Bochner candidate:

```
gradInnerCLM g φ u_h = H1ComplToLp(resolvent g (Bochner candidate)),
```

for every smooth `w : SmoothScalar g`,

```
∫ g(∇φ, ∇u_h)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · F(x) dμ_g(x),
```

where `F := gradInnerLaplacianCandidateUnconditional g φ hu_h`. -/
theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h)))
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Use w_lift := resolvent (candidate).
  set F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h with hF_def
  set w_lift : H1Compl (I := I) (M := M) g :=
    resolvent (I := I) (M := M) g F with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨F, rfl⟩
  -- preimage⟨w_lift⟩ = F.
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ = F := by
    apply resolvent_injective (I := I) (M := M) g
    -- Goal: resolvent (preimage ⟨w_lift, hw_lift_mem⟩) = resolvent F.
    -- LHS = ↑⟨w_lift, hw_lift_mem⟩ = w_lift (since the resolvent inverts preimage),
    -- and w_lift = resolvent F by `set`.
    rw [resolvent_laplacianDomain_preimage_eq]
  -- H1ComplToLp w_lift = gradInnerCLM g φ u_h.
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h := by
    rw [hw_lift_def]
    exact hvar_id.symm
  -- Apply the hypothesis-bearing integral identity.
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  rw [h_preimage_eq] at h_main
  exact h_main

/-! ## Section F — Smooth-case unconditional form (conditional on Christoffel discharge)

Combining Section D with the M3.2 smooth-case unconditional form from
`GradInnerLaplacianM32SmoothFullUnconditional`, the integral form for the
unconditional candidate holds for smooth `v` under the Christoffel discharge
hypothesis. -/

/-- **Integral form, smooth case via the unconditional candidate, conditional
on Christoffel discharge**. For smooth `v : SmoothScalar g`, smooth
`w : SmoothScalar g`, given the Christoffel discharge:

```
∫ g(∇φ, ∇v)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · F(x) dμ_g(x),
```

where `F := gradInnerLaplacianCandidateUnconditional g φ
(smoothToH1Compl_mem_laplacianDomainPow_two g v)` is the unconditional
Bochner candidate. -/
theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v) :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Use the variational identity from M32SmoothFullUnconditional.
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
      (I := I) (M := M) g φ v h_discharge
  -- Apply the hypothesis-bearing form.
  exact integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    hvar_id w

/-! ## Section G — Density-extension form

The density-extension form combines the smooth-case identity with the
density argument from `GradInnerLaplacianM32DensityExtension`. -/

/-- **Integral form for `u_h ∈ laplacianDomainPow g 2`, density-extension form**.
Given an approximating sequence of smooth scalars `v_n` with H¹Compl
convergence to `u_h` and Lp convergence of the candidates plus the smooth
identification target for each `v_n`,

```
∫ g(∇φ, ∇u_h)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · F(x) dμ_g(x),
```

for every smooth `w : SmoothScalar g`, where `F` is the unconditional Bochner
candidate. -/
theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_density
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g φ
        (h_smooth_seq n))
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_via_density
      (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
      h_conv_candidate h_smooth_identity
  exact integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (I := I) (M := M) g φ hu_h hvar_id w

/-! ## Section H — Convenience: integral form using `ContMDiff` test scalars

For a smooth function `w : M → ℝ` (with smoothness witness), the integral
identity holds by wrapping `w` into a `SmoothScalar g`. This is the form
most useful for downstream callers who present the test scalar as a raw
smooth function. -/

/-- **Integral-form variational identity, smooth-function form**. Given a
smooth `w : M → ℝ` with witness `hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w`, the
hypothesis-bearing form reads:

```
∫ A(x) · (w(x) - Δ_g w(x)) dμ_g(x) = ∫ w(x) · F(x) dμ_g(x)
```

where `A := gradInnerCLM g φ u_h` and `F := laplacianDomain.preimage
⟨w_lift, hw_lift⟩` for any `w_lift ∈ laplacianDomain g` with
`H1ComplToLp w_lift = A`. -/
theorem integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    {w : M → ℝ} (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w x - Δ_g (I := I) g hw x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  -- Bundle (w, hw) into a SmoothScalar g and apply the SmoothScalar form.
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨w, hw⟩

/-! ## Section I — Explicit pointwise smooth-case integral form

For smooth `v : SmoothScalar g` and smooth `w : SmoothScalar g`, the LHS
integrand `(gradInnerCLM g φ (smoothToH1Compl v) : Lp 2)(x)` agrees a.e.
with the pointwise smooth function `g.inner x (∇φ x) (∇v x)`. The RHS
integrand `((gradInnerSmoothBundle g φ v).oneSubLapClassical : Lp 2)(x)`
agrees a.e. with the pointwise smooth function
`(gradInnerSmoothBundle g φ v).toFun x - Δ_g (g(∇φ, ∇v)) x`.

This section delivers the **fully pointwise** smooth-case integral
identity, which is the form most useful for downstream applications. -/

/-- **Fully pointwise smooth-case integral form**. For smooth `φ`, smooth
`v : SmoothScalar g`, and smooth `w : SmoothScalar g`,

```
∫ g.inner x (∇φ x) (∇v x) · (w x - Δ_g w x) dμ_g =
  ∫ w x · ((g(∇φ, ∇v))(x) - Δ_g (g(∇φ, ∇v))(x)) dμ_g.
```

Both integrands are pointwise smooth functions; no Lp coercions appear in
the statement. -/
theorem integral_grad_inner_oneSubLap_smooth_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
              Δ_g (I := I) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Start from the Lp-coercion form.
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase_unconditional
      (I := I) (M := M) g φ v w
  -- LHS pointwise rewrite: (gradInnerCLM g φ (smoothToH1Compl v) : Lp)(x)
  -- =ᵐ g.inner x (∇φ x) (∇v x), since gradInnerCLM g φ (smoothToH1Compl v)
  -- = gradInnerSmooth g φ v and gradInnerSmooth_coeFn gives the a.e. pointwise form.
  have h_LHS_coeFn :
      ((gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)) := by
    rw [gradInnerCLM_smoothToH1Compl (I := I) (M := M) g φ v]
    exact gradInnerSmooth_coeFn (I := I) (M := M) g φ v
  -- RHS pointwise rewrite: smoothToLp ((gradInnerSmoothBundle g φ v).oneSubLapClassical) (x)
  -- =ᵐ (gradInnerSmoothBundle g φ v).oneSubLapClassical.toFun x
  -- = (gradInnerSmoothBundle g φ v).toFun x - Δ_g (gradInnerSmoothBundle g φ v).smooth x.
  have h_RHS_coeFn :
      ((smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            Δ_g (I := I) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x) := by
    have h := MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    change ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two.toLp
        _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) = _
    rw [hx]
    -- (gradInnerSmoothBundle g φ v).oneSubLapClassical.toFun x =
    --   (gradInnerSmoothBundle g φ v).toFun x - Δ_g (...).smooth x
    -- by oneSubLapClassical_toFun.
    rfl
  -- Rewrite both sides of h_main using ae-equality and integral_congr_ae.
  -- Build the ae-equality between LHS-integrand and the smooth pointwise form.
  have h_LHS_int_ae :
      (fun x : M =>
          ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
          (w.toFun x - Δ_g (I := I) g w.smooth x)) := by
    filter_upwards [h_LHS_coeFn] with x hx
    rw [hx]
  have h_RHS_int_ae :
      (fun x : M =>
          w.toFun x *
          ((smoothToLp (I := I) (M := M) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => w.toFun x *
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            Δ_g (I := I) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x)) := by
    filter_upwards [h_RHS_coeFn] with x hx
    rw [hx]
  -- Combine: integral_congr_ae aligns each side of h_main with the pointwise smooth form.
  have h_LHS_eq :=
    integral_congr_ae h_LHS_int_ae
  have h_RHS_eq :=
    integral_congr_ae h_RHS_int_ae
  -- h_main: LHS_Lp = RHS_Lp.
  -- h_LHS_eq: LHS_Lp_integral = LHS_smooth_integral.
  -- h_RHS_eq: RHS_Lp_integral = RHS_smooth_integral.
  -- Goal: LHS_smooth_integral = RHS_smooth_integral.
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact h_main

/-! ## Section J' — `C^∞⟮I, M; ℝ⟯`-test-scalar form

For downstream consumers who present the test scalar as a bundled smooth
map `C^∞⟮I, M; ℝ⟯` rather than a `SmoothScalar g`, the same integral
identity holds. This is the most common form in Mathlib-style downstream
usage. -/

/-- **Integral-form variational identity, `C^∞⟮I, M; ℝ⟯` form**. Given
`w_lift ∈ laplacianDomain g` with `H1ComplToLp w_lift = gradInnerCLM g φ u_h`,
for every smooth test map `w : C^∞⟮I, M; ℝ⟯`,

```
∫ g(∇φ, ∇u_h)(x) · (w(x) - Δ_g w(x)) dμ_g(x) =
  ∫ w(x) · (laplacianDomain.preimage ⟨w_lift, hw_lift⟩)(x) dμ_g(x).
```
-/
theorem integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : C^∞⟮I, M; ℝ⟯) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((w : M → ℝ) x - Δ_g (I := I) g w.contMDiff x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, (w : M → ℝ) x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  -- Wrap w into a SmoothScalar g.
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨(w : M → ℝ), w.contMDiff⟩

/-! ## Section J — Weak-Laplacian characterization (corollary)

The integral-form identity is the **weak-Laplacian transfer** characterizing
when `A := gradInnerCLM g φ u_h ∈ Lp 2` has a Hilbert lift in
`laplacianDomain g`. This is a corollary of the resolvent-form M3.2
deliverables.

Specifically, when the integral identity holds for some explicit Lp 2 class
`F`, the function `A` has weak `(1 - Δ_g) A = F` in the sense that

```
∫ A(x) · (1 - Δ_g) w(x) dμ_g(x) = ∫ F(x) · w(x) dμ_g(x)
```

for every smooth test scalar `w`. This generalizes Green's first identity to
non-smooth `A` via the Hilbert-space variational framework. -/

/-- **Weak `(1 - Δ_g) A = F` characterization (forward direction)**. If
`A ∈ Lp 2 μ_g` is the `H1ComplToLp` image of `w_lift ∈ laplacianDomain g`,
then the weak-Laplacian transfer holds with `F := preimage⟨w_lift⟩`. -/
theorem weak_oneSubLap_holds_of_image_in_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {A : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_A_eq : H1ComplToLp (I := I) (M := M) g w_lift = A) :
    ∀ w : SmoothScalar g,
      ∫ x, (A : M → ℝ) x * (w.toFun x - Δ_g (I := I) g w.smooth x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  intro w
  rw [← h_A_eq]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

section SanityTests

example (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v) :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_gradInner_oneSubLap_smooth_eq_integral_candidate_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge w

example (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((smoothToLp (I := I) (M := M) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase_unconditional
    (I := I) (M := M) g φ v w

end SanityTests

end GradInnerVariationalIntegralForm
end Laplacian
end Analysis
end DifferentialGeometry

end
