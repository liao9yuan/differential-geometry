import DifferentialGeometry.Metric.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

-- order 401: fiberwise form
/-- Fiberwise pullback of the inner product along a diffeomorphism `Φ`. As a
continuous bilinear form on `T_x M`, this is the composition of the inner
product `g.inner (Φ x)` at the image with the manifold derivative
`mfderiv I I Φ x` in both slots.

The construction uses `ContinuousLinearMap.comp` and
`ContinuousLinearMap.precomp` to avoid the `SeminormedAddCommGroup`
hypotheses that `ContinuousLinearMap.bilinearComp` would require — those
instances are not synthesised on `TangentSpace I _` without manual aid. -/
noncomputable def Diffeomorph.pullbackInner
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  -- `step1 : T_x M →L T_{Φ x} M →L ℝ`, by pre-composing slot 1 with `mfderiv I I Φ x`.
  let step1 : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) →L[ℝ] ℝ :=
    (g.inner (Φ x)).comp (mfderiv I I Φ x)
  -- The "post-composition with `mfderiv I I Φ x`" CLM
  --   `precompOp : (T_{Φ x} M →L ℝ) →L (T_x M →L ℝ)`,
  -- precomposing a linear functional with `mfderiv I I Φ x`.
  let precompOp : (TangentSpace I (Φ x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)
  -- Compose `step1` with `precompOp` to also pre-compose slot 2.
  precompOp.comp step1

-- order 402: symmetry
theorem Diffeomorph.pullbackInner_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = Diffeomorph.pullbackInner g Φ x w v := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  exact g.symm (Φ x) _ _

-- order 403: positive-definite
theorem Diffeomorph.pullbackInner_pos
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInner g Φ x v v := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  -- The image `mfderiv I I Φ x v` is nonzero because the manifold derivative
  -- of a diffeomorphism is a continuous linear equivalence.
  set hΦeq : TangentSpace I x ≃L[ℝ] TangentSpace I (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x with hΦeq_def
  have hvImg : mfderiv I I Φ x v ≠ 0 := by
    have h1 : hΦeq v ≠ 0 := (hΦeq.map_ne_zero_iff).mpr hv
    -- By `Diffeomorph.mfderivToContinuousLinearEquiv_coe` the underlying CLM
    -- of `hΦeq` is `mfderiv I I Φ x`, so they agree on `v`.
    have h2 : (hΦeq : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) v
        = mfderiv I I Φ x v := by
      rw [hΦeq_def]
      have heq := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero
      exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) => f v) heq
    have hcoe : (hΦeq : TangentSpace I x → TangentSpace I (Φ x)) v = hΦeq v := rfl
    rw [← h2]; exact fun h => h1 (by simpa [hcoe] using h)
  exact g.pos (Φ x) _ hvImg

-- order 408: smoothness of `x ↦ g.inner (Φ x)` as a section over the original base.
/-- The fiberwise inner product `g.inner` of the original metric, pulled back along the
diffeomorphism `Φ` (i.e. evaluated at `Φ x`), is a smooth section of the bundle of
continuous bilinear forms on `E`. -/
theorem inner_comp_smooth_along_diffeo
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      ((fun b ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) ∘ (Φ : M → M)) :=
  g.contMDiff.comp Φ.contMDiff

-- Helper lemma extracted from the bundled metric: pullback inner is computable in
-- terms of `mfderiv I I Φ x` applied to its arguments.
private theorem pullbackInner_eval
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

-- Helper: the underlying CLM of `Diffeomorph.mfderivToContinuousLinearEquiv`
-- agrees with `mfderiv I I Φ x` on each vector.
private theorem mfderiv_eq_mfderivCLE_apply
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x v
      = mfderiv I I Φ x v := by
  have h := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero
  exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) => f v) h

-- order 404: vN-bounded preservation
/-- For each base point `x`, the set `{v ∈ T_x M | pullbackInner g Φ x v v < 1}`
is von-Neumann-bounded. -/
theorem Diffeomorph.pullbackInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ∀ x : M, Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Diffeomorph.pullbackInner g Φ x v v < 1} := by
  intro x
  -- The continuous linear equivalence `T_x M ≃L T_{Φ x} M` induced by the
  -- manifold derivative of `Φ` at `x`.
  set hΦeq := Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x with hΦeq_def
  have hg := g.isVonNBounded (Φ x)
  -- Image of the bounded set under the (continuous, linear) inverse equiv:
  have himg := hg.image (hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x)
  -- Show the set we want is exactly the image set whose boundedness `himg` gives us.
  have hseteq :
      {v : TangentSpace I x | Diffeomorph.pullbackInner g Φ x v v < 1}
        = ((hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x) : _ → _)
            '' {w : TangentSpace I (Φ x) | g.inner (Φ x) w w < 1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    refine ⟨fun hv => ⟨hΦeq v, ?_, ?_⟩, ?_⟩
    · -- `g.inner (Φ x) (hΦeq v) (hΦeq v) < 1` from `hv` and the
      -- `pullbackInner` evaluation formula.
      have h1 := pullbackInner_eval (g := g) (Φ := Φ) x v v
      rw [h1] at hv
      have h2 := mfderiv_eq_mfderivCLE_apply (Φ := Φ) (x := x) v
      rw [← h2] at hv
      exact hv
    · -- `((hΦeq.symm : _ →L _) : _ → _) (hΦeq v) = v`.
      -- The coerce-to-fun of the CLM `hΦeq.symm` is the same as
      -- the coerce-to-fun of the CLE `hΦeq.symm`, by
      -- `ContinuousLinearEquiv.coe_coe`.
      change (hΦeq.symm : TangentSpace I (Φ x) → TangentSpace I x) (hΦeq v) = v
      exact hΦeq.symm_apply_apply v
    · rintro ⟨w, hw, rfl⟩
      -- `((hΦeq.symm : _ →L _) : _ → _) w = hΦeq.symm w`.
      have hsym : ((hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x) :
            TangentSpace I (Φ x) → TangentSpace I x) w = hΦeq.symm w := rfl
      rw [hsym]
      -- Goal: `pullbackInner g Φ x (hΦeq.symm w) (hΦeq.symm w) < 1`.
      rw [pullbackInner_eval]
      have hImg : mfderiv I I Φ x (hΦeq.symm w) = w := by
        have hmap := mfderiv_eq_mfderivCLE_apply (Φ := Φ) (x := x) (hΦeq.symm w)
        rw [← hmap]
        exact hΦeq.apply_symm_apply w
      rw [hImg]; exact hw
  rw [hseteq]
  exact himg

-- order 409: bundled pullback metric
/-- The pullback of a smooth Riemannian metric along a diffeomorphism. -/
noncomputable def Diffeomorph.pullbackMetric
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    SmoothRiemannianMetric I M where
  inner x := Diffeomorph.pullbackInner g Φ x
  symm x v w := Diffeomorph.pullbackInner_symm g Φ x v w
  pos x v hv := Diffeomorph.pullbackInner_pos g Φ x v hv
  isVonNBounded x := Diffeomorph.pullbackInner_isVonNBounded g Φ x
  contMDiff := by
    -- The pullback section factors pointwise as
    --   pullbackInner g Φ x = (g.inner (Φ x)).bilinearComp (mfderiv I I Φ x) (mfderiv I I Φ x)
    -- (see `pullbackInner_eval`). The first factor `x ↦ g.inner (Φ x)` is
    -- smooth as a section of the bilinear-form bundle over `M` (see
    -- `inner_comp_smooth_along_diffeo`). The second factor `x ↦ mfderiv I I Φ x`
    -- is a section of `Hom(TM, Φ^* TM)`. Combining the two into a section of
    -- the bilinear-form bundle over `M` requires a "smoothness of a pulled-back
    -- bilinear-form section along a smooth base map" lemma that is not yet
    -- available; the chart-local building blocks are in place via
    -- `bilinear_pullback_bundle_smooth`, but a bundle-level wrapper is missing.
    sorry

-- order 400: capstone wrapper-existence
/-- The pullback metric exists: it is `Diffeomorph.pullbackMetric g Φ`. -/
theorem diffeomorph_pullback_metric_exists
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ∃ g' : SmoothRiemannianMetric I M, g' = Diffeomorph.pullbackMetric g Φ :=
  ⟨Diffeomorph.pullbackMetric g Φ, rfl⟩

-- order 410: pullback under identity diffeomorphism
/-- Pullback by the identity diffeomorphism is the identity operation. -/
theorem Diffeomorph.pullbackMetric_refl
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetric g (_root_.Diffeomorph.refl I M ∞) = g := by
  -- Establish equality of the `inner` data, then conclude record equality
  -- by destructuring `g` and using the proof-irrelevance of the remaining
  -- propositional fields.
  rcases g with ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
  -- Identify the `inner` field of the LHS with `inner_g`.
  have hinner :
      (fun x => Diffeomorph.pullbackInner
          ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
          (_root_.Diffeomorph.refl I M ∞) x)
        = inner_g := by
    funext x
    apply ContinuousLinearMap.ext; intro v
    apply ContinuousLinearMap.ext; intro w
    rw [pullbackInner_eval]
    -- LHS now: `inner_g ((refl) x) (mfderiv refl x v) (mfderiv refl x w)`.
    -- `(refl) x = x` and `mfderiv refl x = id`.
    have hmfd : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x
        = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      have h1 : mfderiv I I (fun y : M => (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) y) x
          = mfderiv I I (id : M → M) x := rfl
      rw [h1]
      exact mfderiv_id
    have hv : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x v = v := by
      rw [hmfd]; rfl
    have hw : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x w = w := by
      rw [hmfd]; rfl
    rw [hv, hw]
    -- LHS: `inner_g ((refl) x) v w` — and `(refl) x = x` by `rfl`.
    rfl
  -- The two records have the same `inner` data; the other fields are propositions,
  -- so proof-irrelevance gives the record equality after the data agrees.
  unfold Diffeomorph.pullbackMetric
  -- After unfolding, the LHS structure literal has its `inner` field equal to
  -- `fun x => pullbackInner ... x`. By `hinner` this matches `inner_g`. The
  -- remaining fields are propositions, so the record-equality follows.
  congr 1

-- order 405: smoothness of the pullback section (placeholder substep).
/-- Smoothness of the pullback inner-product section.
This is exactly the `contMDiff` field of `Diffeomorph.pullbackMetric g Φ`. -/
theorem Diffeomorph.pullbackInner_contMDiff
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        ((Diffeomorph.pullbackInner g Φ x : E →L[ℝ] E →L[ℝ] ℝ))) :=
  (Diffeomorph.pullbackMetric g Φ).contMDiff

-- order 406: smoothness of a diffeomorphism as a manifold map.
/-- A diffeomorphism is smooth as a map `M → M`. This is the smoothness witness
carried by the `Diffeomorph` structure. -/
theorem Diffeomorph.mfderiv_contMDiff
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I I ∞ (Φ : M → M) :=
  Φ.contMDiff

-- order 407: bilinear pullback bundle is smooth.
/-- The bilinear pullback `(B, L) ↦ B.bilinearComp L L` is smooth in `(B, L)` on the
model normed space. The operation is a polynomial composition of (i) precomposition
`(B, L) ↦ B.comp L`, (ii) `ContinuousLinearMap.flip` (a linear isometry equivalence,
hence smooth), and these are iterated twice, so the composite is `C^∞`. -/
theorem bilinear_pullback_bundle_smooth
    (_Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        ContinuousLinearMap.bilinearComp p.1 p.2 p.2) := by
  -- Use the manifold-level CLM-comp / CLM-from-CLM combinators directly on
  -- the prod model, avoiding any conversion between `ModelProd` and `×`.
  -- The two component projections are smooth on the product manifold.
  have hfst : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.1) :=
    contMDiff_fst
  have hsnd : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.2) :=
    contMDiff_snd
  -- The CLM-flip operation on the model is itself a continuous linear isometry,
  -- in particular a CLM, hence `ContDiff ℝ ∞`. Promote it to a smooth-on-source
  -- map via `ContDiff.comp_contMDiff`.
  have hflipDiff : ContDiff ℝ ∞
      ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) :
        (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  -- Step 1: precomposition `(B, L) ↦ B.comp L` is smooth.
  have h1 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.1.comp p.2) :=
    hfst.clm_comp hsnd
  -- Step 2: apply flip.
  have h2 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => (p.1.comp p.2).flip) := by
    have hcomp := hflipDiff.comp_contMDiff h1
    -- `(flipₗᵢ ℝ E E ℝ) (p.1.comp p.2) = (p.1.comp p.2).flip` definitionally.
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using hcomp
  -- Step 3: precompose again with `p.2`.
  have h3 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        (p.1.comp p.2).flip.comp p.2) := h2.clm_comp hsnd
  -- Step 4: apply flip a second time.
  have h4 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        ((p.1.comp p.2).flip.comp p.2).flip) := by
    have hcomp := hflipDiff.comp_contMDiff h3
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using hcomp
  -- Unfold the goal: `bilinearComp f gE gF = ((f.comp gE).flip.comp gF).flip`.
  -- This is the body of `def bilinearComp`, so `show` discharges it.
  exact h4

end DifferentialGeometry.PDE.RicciFlow.Pullback
