import DifferentialGeometry.Analysis.Laplacian.Regularity.Bochner.PolarisedLpSmooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianFinal

/-!
# Lp-class lift of the polarised Bochner-Weitzenböck identity (smooth case)

For a closed Riemannian manifold `(M, g)` and smooth scalars
`φ : C^∞⟮I, M; ℝ⟯`, `v : SmoothScalar g`, this module derives the
**Lp-class identity**

```
gradInnerLaplacianCandidateUnconditional g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two g v) =
  smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical),
```

i.e. the smooth-case discharge of `smoothCandidate_identification_target`
from `GradInnerLaplacianVariational.lean`.

The proof works by combining:

* The **pointwise polarised Bochner identity** in `(1 - Δ_g)` form, applied to
  smooth `(φ, v)` (from `BochnerPolarised.bochner_polarised_pointwise_oneSubLap`):
  ```
  (1 - Δ_g)(g(∇φ, ∇v))(x) =
      g(∇φ, ∇v)(x)
    - g(∇v, ∇Δφ)(x) - g(∇φ, ∇Δv)(x)
    - 2 · hessPairingChart g φ v x
    - 2 · ricciTensor g x (∇φ x) (∇v x).
  ```
* **Smooth-case identifications** of each CLM summand in the unconditional
  Bochner candidate as `smoothToLp` of a specific smooth scalar:
  - `gradInnerCLM g φ (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g φ v)`.
  - `gradInnerCLM g (Δφ) (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g (Δφ) v)`.
  - `gradInnerLapU g φ hu_h = smoothToLp(gradInnerSmoothBundle g φ v) -
        smoothToLp(gradInnerSmoothBundle g φ v.oneSubLapClassical)`
    (after identifying `preimageLift g hu_h = smoothToH1Compl(v.oneSubLapClassical)`).
  - `ricciPairingCLM g φ (smoothToH1Compl v) = smoothToLp(smoothRicciPairingBundle g φ v)`.
  - `hessPairingLpOnLapDom g φ (...) = smoothToLp(hessPairingSmoothLp g φ v)`
    (taken as a hypothesis; this Hessian-piece bridge requires substantial
    chart-side infrastructure and is exposed as `hessPairingLpOnLapDom_smoothCase`).

Once each summand is identified with a `smoothToLp(...)`, the candidate
equals `smoothToLp` of an explicit sum of smooth scalars. By the pointwise
polarised Bochner identity, this sum agrees pointwise with
`(gradInnerSmoothBundle g φ v).oneSubLapClassical`, hence the Lp classes
are equal.

## Main results

* `H1ComplToLp_injOn_laplacianDomain` — H1ComplToLp restricted to
  laplacianDomain is injective.

* `preimageLift_smoothCase` — for smooth v, the Classical.choose lift
  `preimageLift g hu_h` equals `smoothToH1Compl(v.oneSubLapClassical)`.

* `gradInnerLapU_smoothCase` — Lp identification of `gradInnerLapU` for
  smooth `v`.

* `gradInnerLapU_smoothCase_eq_smoothToLp` — direct Lp identification
  with `smoothToLp(gradInnerSmoothBundle g φ v) -
  smoothToLp(gradInnerSmoothBundle g φ v.oneSubLapClassical)`.

* `gradInnerLapU_smoothCase_pointwise` — the pointwise smoothScalar
  identification, in terms of the polarised identity.

* `smoothCandidate_identification_smooth_of_hessHypothesis` —
  the smooth-case candidate identification, conditional on the Hessian
  bridge hypothesis.

* `smoothCandidate_identification_smooth_unconditional_target` — the
  target statement for the Hessian bridge.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarisedLpFull

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
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarised
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianM32Final

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Injectivity of `H1ComplToLp` on `laplacianDomain`

Two elements of `laplacianDomain g` with the same `H1ComplToLp` image are
equal. This is a consequence of the variational identity satisfied by
elements of `laplacianDomain g` and the coercivity of the H¹Compl bilinear
form (which equals the H¹Compl inner product). -/

/-- **Injectivity of `H1ComplToLp` on `laplacianDomain`.** For
`w₁, w₂ ∈ laplacianDomain g` with `H1ComplToLp w₁ = H1ComplToLp w₂`,
`w₁ = w₂`. -/
theorem H1ComplToLp_injOn_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {w₁ w₂ : H1Compl (I := I) (M := M) g}
    (hw₁ : w₁ ∈ laplacianDomain (I := I) (M := M) g)
    (hw₂ : w₂ ∈ laplacianDomain (I := I) (M := M) g)
    (heq : H1ComplToLp (I := I) (M := M) g w₁ =
      H1ComplToLp (I := I) (M := M) g w₂) :
    w₁ = w₂ := by
  classical
  -- w_i = resolvent g f_i with f_i = preimage ⟨w_i, hw_i⟩.
  set f₁ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₁, hw₁⟩ with hf₁_def
  set f₂ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₂, hw₂⟩ with hf₂_def
  -- The variational identity: ⟨w_i, v⟩ = ⟨H1ComplToLp v, f_i⟩ for all v.
  -- Subtracting: ⟨w₁ - w₂, v⟩ = ⟨H1ComplToLp v, f₁ - f₂⟩ for all v.
  -- Take v = w₁ - w₂.
  have hw₁_eq : w₁ = resolvent (I := I) (M := M) g f₁ := by
    rw [hf₁_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₁, hw₁⟩).symm
  have hw₂_eq : w₂ = resolvent (I := I) (M := M) g f₂ := by
    rw [hf₂_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₂, hw₂⟩).symm
  -- Inner identity for w_i.
  have h_var₁ : ∀ v : H1Compl g,
      ⟪w₁, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₁⟫_ℝ := by
    intro v
    rw [hw₁_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₁ v
  have h_var₂ : ∀ v : H1Compl g,
      ⟪w₂, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₂⟫_ℝ := by
    intro v
    rw [hw₂_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₂ v
  -- ⟨w₁ - w₂, v⟩ = ⟨H1ComplToLp v, f₁ - f₂⟩.
  have h_diff_var : ∀ v : H1Compl g,
      ⟪w₁ - w₂, v⟫_ℝ =
        ⟪H1ComplToLp (I := I) (M := M) g v, f₁ - f₂⟫_ℝ := by
    intro v
    rw [inner_sub_left, inner_sub_right]
    rw [h_var₁ v, h_var₂ v]
  -- Take v = w₁ - w₂.
  specialize h_diff_var (w₁ - w₂)
  -- The RHS evaluates to 0 since H1ComplToLp (w₁ - w₂) = 0.
  have h_H1ComplToLp_diff : H1ComplToLp (I := I) (M := M) g (w₁ - w₂) = 0 := by
    rw [(H1ComplToLp (I := I) (M := M) g).map_sub]
    rw [heq, sub_self]
  rw [h_H1ComplToLp_diff, inner_zero_left] at h_diff_var
  -- LHS = ⟨w₁ - w₂, w₁ - w₂⟩ = ‖w₁ - w₂‖² = 0.
  rw [real_inner_self_eq_norm_sq] at h_diff_var
  -- ‖w₁ - w₂‖² = 0 → w₁ - w₂ = 0.
  have h_norm_zero : ‖w₁ - w₂‖ = 0 := by
    have h_pow_zero : ‖w₁ - w₂‖ ^ 2 = 0 := h_diff_var
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  have h_sub_zero : w₁ - w₂ = 0 := norm_eq_zero.mp h_norm_zero
  exact sub_eq_zero.mp h_sub_zero

/-! ## The `preimageLift` smooth-case identification

For smooth `v ∈ SmoothScalar g` with `u_h := smoothToH1Compl v`,
`preimageLift g hu_h` is a `Classical.choose` artefact. But by the
injectivity of `H1ComplToLp` on `laplacianDomain`, and since
`smoothToH1Compl(v.oneSubLapClassical)` also lies in `laplacianDomain` with
the same `H1ComplToLp` image, they must coincide. -/

/-- For smooth `v`, the H1Compl-lift `preimageLift g hu_h` (where
`hu_h := smoothToH1Compl_mem_laplacianDomainPow_two g v`) equals
`smoothToH1Compl(v.oneSubLapClassical)`. -/
theorem preimageLift_smoothCase
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    preimageLift (I := I) (M := M) g
        (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical := by
  classical
  -- Both elements lie in laplacianDomain g; both have the same H1ComplToLp
  -- image (= smoothToLp v.oneSubLapClassical). By H1ComplToLp_injOn_laplacianDomain,
  -- they are equal.
  set u_h := smoothToH1Compl (I := I) (M := M) g v
  set hu_h := smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v
  set hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h
  -- preimageLift is in laplacianDomain.
  have h_pl_dom : preimageLift (I := I) (M := M) g hu_h ∈
      laplacianDomain (I := I) (M := M) g :=
    preimageLift_mem_laplacianDomain (I := I) (M := M) g hu_h
  -- smoothToH1Compl(v.oneSubLapClassical) is in laplacianDomain.
  have h_st_dom : smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical ∈
      laplacianDomain (I := I) (M := M) g :=
    smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v.oneSubLapClassical
  -- Their H1ComplToLp images are equal.
  have h_pl_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, hu_dom⟩ :=
    H1ComplToLp_preimageLift (I := I) (M := M) g hu_h
  have h_st_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical
  -- Identify laplacianDomain.preimage ⟨u_h, hu_dom⟩ = smoothToLp v.oneSubLapClassical.
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    -- preimage ⟨resolvent f, _⟩ = f. We have u_h = resolvent g (smoothToLp v.oneSubLapClassical).
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    -- Goal: ↑⟨u_h, hu_dom⟩ = resolvent g (smoothToLp v.oneSubLapClassical), i.e.
    -- u_h = resolvent g (smoothToLp v.oneSubLapClassical), which is smoothToH1Compl_eq_resolvent_oneSubLap.
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) v
  have h_H1ComplToLp_eq :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) := by
    rw [h_pl_H1ComplToLp, h_st_H1ComplToLp, h_preimage_eq]
  exact H1ComplToLp_injOn_laplacianDomain (I := I) (M := M) g h_pl_dom h_st_dom
    h_H1ComplToLp_eq

/-! ## Smooth-case identification of `gradInnerLapU`

For smooth `v`, the auxiliary class `gradInnerLapU g φ hu_h` equals
`smoothToLp(gradInnerSmoothBundle g φ v) -
smoothToLp(gradInnerSmoothBundle g φ v.oneSubLapClassical)`. -/

/-- Smooth-case identification of `gradInnerLapU` as a difference of two
smoothToLp classes. -/
theorem gradInnerLapU_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerLapU (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            v.oneSubLapClassical) := by
  classical
  rw [gradInnerLapU_eq_sub]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]
  rw [preimageLift_smoothCase]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

/-! ## Pointwise smooth-scalar version of `gradInnerSmoothBundle` linearity

For smooth `v`, the smooth scalars
`gradInnerSmoothBundle g φ v - gradInnerSmoothBundle g φ v.oneSubLapClassical`
and `gradInnerSmoothBundle g φ (v - v.oneSubLapClassical) = gradInnerSmoothBundle g φ (Δ_g v)`
have the same pointwise values. -/

/-- The smooth scalar arising from `v - v.oneSubLapClassical = Δ_g v`. -/
theorem v_sub_oneSubLap_eq_lap
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) (x : M) :
    v.toFun x - v.oneSubLapClassical.toFun x = Δ_g (I := I) g v.smooth x := by
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  ring

/-- Pointwise identity: `gradInnerSmoothBundle g φ v - gradInnerSmoothBundle g φ v.oneSubLapClassical`
has the toFun `b ↦ g(∇φ, ∇(Δ_g v))(b)`. -/
theorem gradInnerSmoothBundle_sub_oneSubLap_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ
          v.oneSubLapClassical).toFun b =
      g.inner b (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (Δ_g (I := I) g v.smooth) b) := by
  classical
  rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply]
  -- Need: g(∇φ, ∇v)(b) - g(∇φ, ∇v.oneSubLap)(b) = g(∇φ, ∇(Δ_g v))(b).
  -- = g(∇φ, ∇v - ∇v.oneSubLap)(b) = g(∇φ, ∇(v - v.oneSubLap))(b) = g(∇φ, ∇(Δ_g v))(b).
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.toFun b :=
    v.smooth.mdifferentiable (by simp) b
  have hvl_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.oneSubLapClassical.toFun b :=
    v.oneSubLapClassical.smooth.mdifferentiable (by simp) b
  have hΔv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (Δ_g (I := I) g v.smooth) b :=
    (Δ_g_contMDiff (I := I) g v.smooth).mdifferentiable (by simp) b
  -- Step 1: g(∇φ, ∇v) - g(∇φ, ∇v.oneSubLap) = g(∇φ, ∇v - ∇v.oneSubLap) by bilinearity.
  have h_inner_sub : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b -
          gradFun (I := I) g v.oneSubLapClassical.toFun b) := by
    rw [(g.inner b (gradFun (I := I) g (φ : M → ℝ) b)).map_sub]
  rw [h_inner_sub]
  -- Step 2: gradFun(v) - gradFun(v.oneSubLap) = gradFun(v - v.oneSubLap) (pointwise).
  have h_grad_sub : gradFun (I := I) g v.toFun b -
        gradFun (I := I) g v.oneSubLapClassical.toFun b =
      gradFun (I := I) g
        (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) b := by
    rw [gradFun_sub (I := I) g hv_diff hvl_diff]
  rw [h_grad_sub]
  -- Step 3: gradFun (fun y => v y - v.oneSubLap y) = gradFun (Δ_g v) (by funext on the inner functions).
  -- v.toFun - v.oneSubLap.toFun = Δ_g v.
  have h_fun_eq : (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) =
      (fun y : M => Δ_g (I := I) g v.smooth y) := by
    funext y
    exact v_sub_oneSubLap_eq_lap (I := I) (M := M) g v y
  rw [h_fun_eq]

/-! ## Smooth-case pointwise expansion of the unconditional candidate

For smooth `(φ, v)` the unconditional Bochner candidate equals (pointwise)
the polarised Bochner RHS minus the Hessian-piece's `Lp` class. This is the
core pointwise content; the full `Lp`-class identification is then a
matter of bridging the Hessian piece. -/

/-- The classical Laplacian Δφ of a smooth bundled `φ`, as a `SmoothScalar`. -/
noncomputable def smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : SmoothScalar g where
  toFun := Δ_g (I := I) g φ.contMDiff
  smooth := Δ_g_contMDiff (I := I) g φ.contMDiff

@[simp] lemma smoothLaplacianAsScalar_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun =
      Δ_g (I := I) g φ.contMDiff := rfl

/-- The smoothLaplacianBundle and smoothLaplacianAsScalar agree as bundled
smooth functions / smooth scalars (their underlying functions are equal). -/
lemma smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
      (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun := rfl

/-! ## The pointwise polarised Bochner identity in `SmoothScalar` form

We restate the polarised identity for `(φ, v)` smooth, expressing it in
terms of pointwise differences and products of smooth scalars. -/

/-- Pointwise polarised Bochner identity, expressed via `(gradInnerSmoothBundle ...)`
and `hessPairingChart`, using `φ.contMDiff` as the smoothness witness for the
classical Laplacian of `φ`. -/
theorem oneSubLapClassical_gradInner_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun x =
      g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)
      - g.inner x
          (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
      - g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.smooth) x)
      - 2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ x
      - 2 * ricciTensor (I := I) g x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) := by
  classical
  -- (gradInnerSmoothBundle).oneSubLapClassical.toFun = (gradInnerSmoothBundle).toFun - Δ_g (gradInnerSmoothBundle).smooth.
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  -- (gradInnerSmoothBundle g φ v).toFun x = g(∇φ, ∇v)(x).
  rw [gradInnerSmoothBundle_apply]
  -- Δ_g (gradInnerSmoothBundle).smooth x = Δ_g (b ↦ g.inner b (∇φ b) (∇v.toFun b)) x (same witness via Δ_g_congr_func).
  have h_Δ_eq := Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (I := I) (M := M) g φ v x
  rw [h_Δ_eq]
  -- Now apply bochner_polarised_pointwise_oneSubLap with φ and the smooth scalar v as C^∞⟮I,M;ℝ⟯.
  have h_polar := bochner_polarised_pointwise_oneSubLap (I := I) (M := M) g
    φ ⟨v.toFun, v.smooth⟩
    (contMDiff_phi_add_v (I := I) (M := M) φ ⟨v.toFun, v.smooth⟩)
    (contMDiff_phi_sub_v (I := I) (M := M) φ ⟨v.toFun, v.smooth⟩)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ ⟨v.toFun, v.smooth⟩) x
  -- h_polar uses ⟨v.toFun, v.smooth⟩ : C^∞⟮I,M;ℝ⟯.
  -- The bundled ⟨v.toFun, v.smooth⟩.contMDiff is v.smooth by structure equality.
  exact h_polar

/-! ## Lp-class identification of the unconditional candidate (Hessian-hypothesis form)

The smooth-case identification of `gradInnerLaplacianCandidateUnconditional`
with `smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical)` follows
from:

1. Identifying each gradient-CLM summand as a `smoothToLp` of a smooth scalar.
2. Identifying `gradInnerLapU` via `preimageLift_smoothCase`.
3. Identifying `ricciPairingCLM g φ (smoothToH1Compl v) = smoothToLp(...)`.
4. **Hessian bridge hypothesis**: `hessPairingLpOnLapDom g φ (...) =
   smoothToLp(hessPairing-as-smooth)` for the smooth `v`.

The Hessian bridge requires substantial chart-side infrastructure
(`laplacianDomainHessianChart_smooth_case` plus POU summation and metric
chart pullback identifications). We expose this as a hypothesis. -/

/-- The unconditional candidate, smooth-case, conditional on the Hessian
bridge hypothesis. -/
theorem gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
  classical
  -- Unfold the candidate.
  unfold gradInnerLaplacianCandidateUnconditional
  -- Identify each summand:
  -- (1) gradInnerCLM g φ (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g φ v).
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  -- (2) gradInnerCLM g (Δφ) (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g (Δφ) v).
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) v]
  -- (3) gradInnerLapU g φ hu_h = smoothToLp(...) - smoothToLp(...) (gradInnerLapU_smoothCase).
  rw [gradInnerLapU_smoothCase (I := I) (M := M) g φ v]
  -- (4) ricciPairingCLM g φ (smoothToH1Compl v) = smoothToLp(smoothRicciPairingBundle g φ v).
  rw [ricciPairingCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  -- (5) hessPairingLpOnLapDom = hessPairingSmoothLp (by hypothesis).
  rw [h_hess]
  -- Now LHS is an explicit sum of smoothToLp of smooth scalars and hessPairingSmoothLp.
  -- We want LHS = smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical).
  -- Use Lp.ext: both sides represent functions on M.
  -- LHS coeFn (a.e.) equals smoothToLp_coeFn applied summand-by-summand.
  -- RHS coeFn equals the smoothToLp pointwise function.
  -- The polarised identity gives the pointwise equality.
  apply MeasureTheory.Lp.ext
  -- Step a: extract a.e. coeFn descriptions for each summand.
  -- LHS = smoothToLp gradInnerSmoothBundle g φ v
  --       - smoothToLp gradInnerSmoothBundle g (Δφ) v
  --       - (smoothToLp gradInnerSmoothBundle g φ v - smoothToLp gradInnerSmoothBundle g φ v.oneSubLap)
  --       - 2 • smoothToLp smoothRicciPairingBundle g φ v
  --       - 2 • hessPairingSmoothLp g φ v.
  -- Each smoothToLp(s) has coeFn s.toFun (a.e.).
  -- hessPairingSmoothLp coeFn = hessPairingChart g φ ⟨v.toFun, v.smooth⟩.
  -- RHS = smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical), coeFn = (gradInnerSmoothBundle).oneSubLapClassical.toFun.
  -- Use Lp arithmetic: (a - b - c - 2•d - 2•e).coeFn =ᵐ a.coeFn - b.coeFn - c.coeFn - 2*d.coeFn - 2*e.coeFn.
  -- Then by the pointwise identity (oneSubLapClassical_gradInner_apply + gradInnerSmoothBundle_sub_oneSubLap_apply
  -- + hessPairingSmoothLp_coeFn + smoothRicciPairingLp_coeFn), the two sides agree pointwise.

  -- Set abbreviations for clarity.
  set A1 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) with hA1_def
  set A2 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v) with hA2_def
  set A3 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
    smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) with hA3_def
  set A4 := ricciPairingSmooth (I := I) (M := M) g φ v with hA4_def
  set A5 := hessPairingSmoothLp (I := I) (M := M) g φ v with hA5_def
  set RHS := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical with hRHS_def
  -- coeFn equalities. We unfold smoothToLp_apply to get the equalities at the toLp level,
  -- so the syntactic patterns match.
  have h_A1_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A2_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).memLp_two
  have h_A3a_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A3b_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).memLp_two
  have h_A4_coe := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have h_A5_coe := hessPairingSmoothLp_coeFn (I := I) (M := M) g φ v
  have h_RHS_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
  -- Lp arithmetic.
  have h_A3_diff_coe : (A3 : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b : M =>
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b := by
    change ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) : Lp ℝ 2 _) :
        M → ℝ) =ᵐ[_] _
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v))
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical))
    refine h_sub.trans ?_
    filter_upwards [h_A3a_coe, h_A3b_coe] with b h_a h_b
    rw [Pi.sub_apply]
    rw [h_a, h_b]
  -- Build up the LHS coeFn description.
  -- LHS = A1 - A2 - A3 - 2 • A4 - 2 • A5.
  set LHS := A1 - A2 - A3 - (2 : ℝ) • A4 - (2 : ℝ) • A5 with hLHS_def
  -- LHS coeFn =ᵐ A1.coeFn - A2.coeFn - A3.coeFn - 2 * A4.coeFn - 2 * A5.coeFn.
  -- We compute step by step.
  have h_step1 : ((A1 - A2 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b := by
    refine (MeasureTheory.Lp.coeFn_sub A1 A2).trans ?_
    filter_upwards [h_A1_coe, h_A2_coe] with b h_a1 h_a2
    rw [Pi.sub_apply, h_a1, h_a2]
  have h_step2 : ((A1 - A2 - A3 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
      ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2) A3).trans ?_
    filter_upwards [h_step1, h_A3_diff_coe] with b h_12 h_3
    rw [Pi.sub_apply, h_12, h_3]
  have h_A4_smul_coe : (((2 : ℝ) • A4 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * ricciTensor (I := I) g b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A4).trans ?_
    filter_upwards [h_A4_coe] with b h_a4
    rw [Pi.smul_apply, h_a4]
    rfl
  have h_step3 : ((A1 - A2 - A3 - (2 : ℝ) • A4 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
        ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
      2 * ricciTensor (I := I) g b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3) ((2 : ℝ) • A4)).trans ?_
    filter_upwards [h_step2, h_A4_smul_coe] with b h_123 h_4
    rw [Pi.sub_apply, h_123, h_4]
  have h_A5_smul_coe : (((2 : ℝ) • A5 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * hessPairingChart (I := I) g φ
      ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A5).trans ?_
    filter_upwards [h_A5_coe] with b h_a5
    rw [Pi.smul_apply, h_a5]
    rfl
  have h_LHS_coe : (LHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
            (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
          2 * ricciTensor (I := I) g b
            (gradFun (I := I) g (φ : M → ℝ) b)
            (gradFun (I := I) g v.toFun b)) -
        2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3 - (2 : ℝ) • A4) ((2 : ℝ) • A5)).trans ?_
    filter_upwards [h_step3, h_A5_smul_coe] with b h_1234 h_5
    rw [Pi.sub_apply, h_1234, h_5]
  -- Now produce the RHS coeFn description.
  have h_RHS_coe' : (RHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun b := by
    change ((smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
      Lp ℝ 2 _) : M → ℝ) =ᵐ[_] _
    exact h_RHS_coe
  -- Goal: LHS =ᵐ RHS as Lp coeFn. Combine h_LHS_coe and h_RHS_coe' via pointwise.
  refine h_LHS_coe.trans ?_
  refine EventuallyEq.symm ?_
  refine h_RHS_coe'.trans ?_
  -- Now both sides are pointwise smooth functions; relate via the polarised identity.
  refine Filter.Eventually.of_forall ?_
  intro b
  beta_reduce
  -- RHS-side function value: (gradInnerSmoothBundle g φ v).oneSubLapClassical.toFun b.
  -- By oneSubLapClassical_gradInner_apply, this equals:
  --   g(∇φ, ∇v)(b) - g(∇v, ∇Δφ)(b) - g(∇φ, ∇Δv)(b) - 2 hessPairing(b) - 2 Ric(∇φ,∇v)(b).
  rw [oneSubLapClassical_gradInner_apply (I := I) (M := M) g φ v b]
  -- LHS function (after expanding): the constant identities for gradInnerSmoothBundle.
  -- We use simp to unfold all gradInnerSmoothBundle.toFun on the RHS.
  simp only [gradInnerSmoothBundle_apply]
  -- The (a - b - (c - d) - 2 r - 2 h) expansion.
  -- a = g(∇φ, ∇v), b = g(∇(Δφ), ∇v), c = g(∇φ, ∇v), d = g(∇φ, ∇v.oneSubLap).
  -- We need: a - b - (c - d) - 2r - 2h = a - g(∇v, ∇Δφ) - g(∇φ, ∇Δv) - 2h - 2r.
  -- i.e. -b + d = -g(∇v, ∇Δφ) - g(∇φ, ∇Δv) - g(∇φ, ∇v) + g(∇φ, ∇v).
  -- a - c = 0, so LHS = -b - 2r - 2h + (a - c) + d = -b + d - 2r - 2h.
  -- We need: -b + d = -g(∇v, ∇Δφ) - g(∇φ, ∇Δv).
  -- d = g(∇φ, ∇v.oneSubLap) = g(∇φ, ∇v) - g(∇φ, ∇Δv) (by gradInnerSmoothBundle_sub_oneSubLap_apply)
  -- So d - a = -g(∇φ, ∇Δv).
  -- And -b = -g(∇(Δφ), ∇v) = -g(∇v, ∇Δφ) (by g.symm).
  -- Hence LHS = -g(∇v, ∇Δφ) + (-g(∇φ, ∇Δv)) - 2r - 2h + (a - c + a) - a (since a appears twice now)
  -- = a - g(∇v, ∇Δφ) - g(∇φ, ∇Δv) - 2r - 2h.
  -- The polarised identity says RHS_target = a - g(∇v, ∇Δφ) - g(∇φ, ∇Δv) - 2h - 2r.
  -- Match by symmetry of (·)+(·).
  -- We expand g(∇(Δφ), ∇v) = g(∇v, ∇(Δφ)) (g.symm).
  have h_phi_sym : g.inner b
        (gradFun (I := I) g
          ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) =
      g.inner b
        (gradFun (I := I) g v.toFun b)
        (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) b) := by
    -- (smoothLaplacianBundle g φ : M → ℝ) = Δ_g g φ.contMDiff (rfl).
    -- Apply g.symm.
    rw [show ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
        Δ_g (I := I) g φ.contMDiff from rfl]
    exact g.symm b _ _
  rw [h_phi_sym]
  -- Sub-expression g(∇φ, ∇v)(b) - g(∇φ, ∇v.oneSubLap)(b) = g(∇φ, ∇Δv)(b).
  -- We need this in the form "the (c - d) bracket equals g(∇φ, ∇Δv)(b)".
  -- Since gradInnerSmoothBundle (φ,v).toFun = g(∇φ, ∇v) (by gradInnerSmoothBundle_apply),
  -- and similarly for v.oneSubLapClassical, the (c - d) bracket reduces to (using
  -- gradInnerSmoothBundle_sub_oneSubLap_apply) g(∇φ, ∇Δv)(b).
  -- (We can't rewrite directly because of subtraction order; just use ring + the identity.)
  have h_diff_eq : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (Δ_g (I := I) g v.smooth) b) := by
    have h := gradInnerSmoothBundle_sub_oneSubLap_apply (I := I) (M := M) g φ v b
    rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply] at h
    exact h
  -- Now the LHS becomes:
  -- a - g(∇v, ∇Δφ) - (a - g(∇φ, ∇v.oneSubLap)) - 2r - 2h
  -- = a - g(∇v, ∇Δφ) - g(∇φ, ∇Δv) - 2r - 2h.
  -- Use h_diff_eq to substitute: a - g(∇φ, ∇v.oneSubLap) = g(∇φ, ∇Δv).
  linarith [h_diff_eq]

/-! ## Re-export as `smoothCandidate_identification_target`

For ease of downstream use, we re-export the hypothesis-bearing form as
the proof of `smoothCandidate_identification_target g φ v`, conditional on
the Hessian-bridge hypothesis. -/

/-- The `smoothCandidate_identification_target` statement is discharged by
`gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis`. -/
theorem smoothCandidate_identification_target_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    smoothCandidate_identification_target (I := I) (M := M) g φ v := by
  unfold smoothCandidate_identification_target
  exact gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis
    (I := I) (M := M) g φ v h_hess

end BochnerPolarisedLpFull
end Laplacian
end Analysis
end DifferentialGeometry

end
