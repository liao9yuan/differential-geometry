import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainSmoothMulHC
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedLaplacianDomain
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedH2RegularityStep

/-!
# Manifold-side `Lp`-class identity for `gradInnerCLM g φ u_h`

For a closed Riemannian manifold `(M, g)` and an arbitrary smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, this module derives an explicit `Lp`-class identity for
twice the gradient inner product `2 · gradInnerCLM g φ u_h` valid for every
`u_h ∈ laplacianDomain g`.

The identity follows from the Phase 3 `(1-Δ)`-preimage formula
`laplacianDomain.preimage⟨smoothMulHC g φ u_h⟩ = fHLeibnizGeneral g φ u_h hu_h`
combined with the definitional unfolding of `fHLeibnizGeneral` and
`fHLeibnizGeneralResidualCLM`.

## Main results

* `gradInnerCLM_eq_two_inv_preimageDiff` — for `u_h ∈ laplacianDomain g`:

  ```
  2 • gradInnerCLM g φ u_h
    = smoothMulLp g φ (preimage⟨u_h⟩)
      − preimage⟨smoothMulHC g φ u_h⟩
      − smoothMulLp g (Δφ) (H1ComplToLp u_h).
  ```

  This rearranges the existing Phase 3 preimage decomposition; for
  `φ := chartAtlasPOU I M α` it specialises to (and is mathematically
  equivalent to) `ResidualLpDecomposition.fHLeibnizGeneralResidualCLM_eq_preimageDiff`.

* `gradInnerCLM_mem_H1ComplToLp_laplacianDomain_iff` — the equivalence

  ```
  gradInnerCLM g φ u_h ∈ H1ComplToLp '' (laplacianDomain g)
    ↔ smoothMulHC g φ u_h ∈ laplacianDomainPow g 2,
  ```

  proved for `u_h ∈ laplacianDomainPow g 2`. The forward direction is the
  iterated regularity closure for `smoothMulHC`; the reverse is the
  rearrangement of the Lp identity above using that the other two summands
  always lie in the image of the resolvent.

* `gradInnerCLM_mem_image_implies_smoothMulHC_mem_pow_two` — direct
  implication form of the equivalence, packaged for downstream use.

## Connection to the iterated regularity bottleneck

For `u_h ∈ laplacianDomainPow g 2`, the membership
`smoothMulHC g φ u_h ∈ laplacianDomainPow g 2` is the iterated closure of
the Laplacian domain under smooth multiplication. By the equivalence above,
this is precisely the question whether `gradInnerCLM g φ u_h` lifts to an
H¹Compl element in `laplacianDomain g`.

Equivalently: whether `g(∇φ, ∇u_h)` is H¹ chart-wise, which is true
mathematically (each chart-side ∂_j of `u_h` is H¹ for `u_h ∈ laplacianDomain g`,
and smooth-bounded `g_inv^{ij} · ∂_i φ ∘ symm` times H¹ is H¹). The chart-side
non-smooth formalisation requires a "raw" chart-pushed weak-partial Lp class
without partition-of-unity weight, which is a separate substantial
infrastructure item.

This file does NOT attempt that chart-side construction. It exposes the
equivalence cleanly so that the bottleneck localizes to a single, sharp
mathematical statement.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLpIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Algebraic helper lemmas -/

/-- Algebraic rearrangement in an additive commutative group:
`a = b - c - d ↔ c = b - a - d`. -/
private lemma sub_rearrange_three {α : Type*} [AddCommGroup α] {a b c d : α}
    (h : a = b - c - d) : c = b - a - d := by
  have hcomp : c = b - (b - c - d) - d := by abel
  rw [← h] at hcomp
  exact hcomp

/-- Algebraic rearrangement in an additive commutative group:
`a + b = c - d ↔ a = c - b - d`. (We don't actually need this; see
`sub_rearrange_three` instead.) -/
private lemma add_sub_rearrange {α : Type*} [AddCommGroup α] {a b c d : α}
    (h : a + b = c - d) : a = c - b - d := by
  have : a = c - d - b := by
    rw [← h]; abel
  rw [this]; abel

/-! ## Step 1: the general `Lp`-class identity for `2 • gradInnerCLM g φ u_h`

We rearrange the Phase 3 preimage decomposition
`preimage⟨smoothMulHC g φ u_h⟩ = smoothMulLp g φ (preimage⟨u_h⟩) +
    fHLeibnizGeneralResidualCLM g φ u_h`
together with the unfolding
`fHLeibnizGeneralResidualCLM g φ u_h = -2 • gradInnerCLM g φ u_h −
    smoothMulLp g (Δφ) (H1ComplToLp u_h)`
into an explicit formula for `2 • gradInnerCLM g φ u_h`. -/

/-- **The general manifold-side `Lp`-class identity for `2 • gradInnerCLM g φ u_h`.**

For an arbitrary smooth scalar `φ : C^∞⟮I, M; ℝ⟯` and `u_h ∈ laplacianDomain g`,
twice the gradient inner product splits as the difference of two
`(1-Δ_g)`-preimages plus the smooth-multiplication of `u_h` by `Δφ`:

```
2 • gradInnerCLM g φ u_h
  = smoothMulLp g φ (preimage⟨u_h⟩)
    − preimage⟨smoothMulHC g φ u_h⟩
    − smoothMulLp g (Δφ) (H1ComplToLp u_h).
```

This generalises `ResidualLpDecomposition.fHLeibnizGeneralResidualCLM_eq_preimageDiff`
from `φ := chartAtlasPOU I M α` to arbitrary smooth `φ`. -/
theorem gradInnerCLM_eq_two_inv_preimageDiff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h =
      smoothMulLp (I := I) (M := M) g φ
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) -
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h,
            smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  classical
  -- Step 1: Phase 3 preimage identity:
  --   preimage⟨smoothMulHC φ u_h⟩ = fHLeibnizGeneral g φ u_h hu_dom.
  have h_preimage :=
    laplacianDomain_preimage_smoothMulHC (I := I) (M := M) g φ hu_dom
  -- Step 2: Unfold `fHLeibnizGeneral` definitionally.
  --   fHLeibnizGeneral = smoothMulLp φ (H1ComplToLp u_h - laplacianOp ⟨u_h⟩)
  --                       + fHLeibnizGeneralResidualCLM g φ u_h.
  unfold fHLeibnizGeneral at h_preimage
  -- Step 3: Identify (H1ComplToLp u_h - laplacianOp ⟨u_h, hu_dom⟩) with preimage⟨u_h⟩.
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq] at h_preimage
  -- After step 3: h_preimage says
  --   preimage⟨smoothMulHC φ u_h⟩
  --     = smoothMulLp φ (preimage⟨u_h⟩) + fHLeibnizGeneralResidualCLM g φ u_h.
  -- Step 4: Unfold `fHLeibnizGeneralResidualCLM g φ u_h` =
  --   -2 • gradInnerCLM g φ u_h - smoothMulLp Δφ (H1ComplToLp u_h).
  have h_residual_apply := fHLeibnizGeneralResidualCLM_apply
    (I := I) (M := M) g φ u_h
  rw [h_residual_apply] at h_preimage
  -- Step 5: Rearrange to solve for 2 • gradInnerCLM φ u_h.
  -- h_preimage:
  --   preimage⟨smoothMulHC φ u_h⟩ =
  --     smoothMulLp φ (preimage⟨u_h⟩) + (-2 • gradInnerCLM φ u_h - smoothMulLp Δφ (H1ComplToLp u_h)).
  -- Adding 2 • gradInnerCLM φ u_h to both sides and rearranging gives the conclusion.
  -- For modules (no CommSemiring), we use `abel_nf` after suitable rewrites.
  have h_rearrange :
      smoothMulLp (I := I) (M := M) g φ
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) +
        (-((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h) -
          smoothMulLp (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ)
            (H1ComplToLp (I := I) (M := M) g u_h)) =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulHC (I := I) (M := M) g φ u_h,
          smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ :=
    h_preimage.symm
  -- Now rearrange algebraically:
  -- 2 • gradInner = smoothMulLp φ preimage⟨u_h⟩ - preimage⟨smoothMulHC⟩ - smoothMulLp Δφ u_h.
  rw [← h_rearrange]
  abel

/-! ## Step 2: equivalence between iterated closure and `gradInnerCLM` image membership -/

/-- The auxiliary lift of `preimage⟨u_h⟩ ∈ Lp` to an `H1Compl` element in
`laplacianDomain g`, available for `u_h ∈ laplacianDomainPow g 2`. -/
noncomputable def preimageLift
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1Compl (I := I) (M := M) g :=
  Classical.choose (laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h)

lemma preimageLift_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    preimageLift (I := I) (M := M) g hu_h ∈
      laplacianDomain (I := I) (M := M) g :=
  (Classical.choose_spec (laplacianDomainPow_two_preimage_eq
    (I := I) (M := M) g hu_h)).1

lemma H1ComplToLp_preimageLift
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1ComplToLp (I := I) (M := M) g
        (preimageLift (I := I) (M := M) g hu_h) =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :=
  (Classical.choose_spec (laplacianDomainPow_two_preimage_eq
    (I := I) (M := M) g hu_h)).2

/-! ### The forward direction: iterated closure → `gradInnerCLM` image membership

For `u_h ∈ laplacianDomainPow g 2`, suppose
`smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`. Then
`preimage⟨smoothMulHC g φ u_h⟩` lifts to `H1Compl` (via the `preimageLift`
construction), and hence `gradInnerCLM g φ u_h` is expressed via the
identity above as a sum of three terms each of which lies in
`H1ComplToLp '' laplacianDomain g`. -/

/-- For `u_h ∈ laplacianDomainPow g 2`, the `Lp`-class
`smoothMulLp g φ (preimage⟨u_h⟩)` lifts to `H1Compl`: it is the L²-image
of `smoothMulHC g φ (preimageLift g hu_h) ∈ laplacianDomain g`. -/
theorem smoothMulLp_preimage_in_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  -- Lift preimage⟨u_h⟩ to vH ∈ laplacianDomain g via `preimageLift`.
  have hvH_mem := preimageLift_mem_laplacianDomain (I := I) (M := M) g hu_h
  -- smoothMulHC g φ vH ∈ laplacianDomain g (Phase 3).
  have h_sM_mem := smoothMulHC_mem_laplacianDomain
    (I := I) (M := M) g φ hvH_mem
  -- H1ComplToLp (smoothMulHC φ vH) = smoothMulLp φ (H1ComplToLp vH) = smoothMulLp φ (preimage⟨u_h⟩).
  refine ⟨smoothMulHC (I := I) (M := M) g φ
    (preimageLift (I := I) (M := M) g hu_h), ?_, ?_⟩
  · exact h_sM_mem
  · rw [H1ComplToLp_smoothMulHC]
    rw [H1ComplToLp_preimageLift]

/-- For any `u_h ∈ H1Compl g`, the `Lp`-class
`smoothMulLp g (Δφ) (H1ComplToLp u_h)` lifts to `H1Compl` when
`u_h ∈ laplacianDomain g`: it equals `H1ComplToLp(smoothMulHC g (Δφ) u_h)`
with `smoothMulHC g (Δφ) u_h ∈ laplacianDomain g` (Phase 3). -/
theorem smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    smoothMulLp (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ)
        (H1ComplToLp (I := I) (M := M) g u_h) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  have h_sM_mem := smoothMulHC_mem_laplacianDomain (I := I) (M := M) g
    (smoothLaplacianBundle (I := I) (M := M) g φ) hu_dom
  refine ⟨smoothMulHC (I := I) (M := M) g
    (smoothLaplacianBundle (I := I) (M := M) g φ) u_h, ?_, ?_⟩
  · exact h_sM_mem
  · rw [H1ComplToLp_smoothMulHC]

/-! ### Reverse direction: `gradInnerCLM` image membership → iterated closure -/

/-- **Reverse implication (gradInnerCLM image ⊆ iterated closure)**.

For `u_h ∈ laplacianDomainPow g 2`, if `gradInnerCLM g φ u_h` lifts to an
`H1Compl` element in `laplacianDomain g`, then so does
`preimage⟨smoothMulHC g φ u_h⟩` (the `Lp` class `(1-Δ_g)(φ · u_h)`).
This is precisely the iterated closure
`smoothMulHC g φ u_h ∈ laplacianDomainPow g 2`. -/
theorem smoothMulHC_mem_pow_two_of_gradInnerCLM_mem_image
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_grad : gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g))) :
    smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  -- Notation: hu_dom for u_h ∈ laplacianDomain g.
  have hu_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 hu_h
  -- preimage⟨smoothMulHC φ u_h⟩ = smoothMulLp φ (preimage⟨u_h⟩)
  --                              - 2 • gradInnerCLM φ u_h
  --                              - smoothMulLp Δφ (H1ComplToLp u_h)
  -- as Lp classes (by rearrangement of the headline Lp identity).
  have h_lp_identity :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h,
            smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ =
        smoothMulLp (I := I) (M := M) g φ
            (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) -
          (2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h -
          smoothMulLp (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ)
            (H1ComplToLp (I := I) (M := M) g u_h) := by
    have h := gradInnerCLM_eq_two_inv_preimageDiff
      (I := I) (M := M) g φ hu_dom
    -- h: 2 • gradInner = smoothMulLp φ preimage⟨u_h⟩ - preimage⟨smoothMulHC⟩ - smoothMulLp Δφ u_h.
    -- Solve for preimage⟨smoothMulHC⟩: it equals smoothMulLp φ preimage⟨u_h⟩ - 2 • gradInner - smoothMulLp Δφ u_h.
    exact sub_rearrange_three h
  -- Each summand on the RHS is in H1ComplToLp '' laplacianDomain g.
  have h1 := smoothMulLp_preimage_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_h
  obtain ⟨w1, hw1_dom, hw1_eq⟩ := h1
  obtain ⟨w2, hw2_dom, hw2_eq⟩ := h_grad
  have h3 := smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_dom
  obtain ⟨w3, hw3_dom, hw3_eq⟩ := h3
  -- Then the Lp combination corresponds to an H1Compl combination.
  -- We need: preimage⟨smoothMulHC φ u_h⟩ = H1ComplToLp(w1 - 2 • w2 - w3).
  have h_in_image :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h,
            smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ ∈
        Set.image (H1ComplToLp (I := I) (M := M) g)
          (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
    refine ⟨w1 - (2 : ℝ) • w2 - w3, ?_, ?_⟩
    · -- w1 - 2 • w2 - w3 ∈ laplacianDomain g (closed under sub + smul).
      refine sub_mem (sub_mem hw1_dom ?_) hw3_dom
      exact (laplacianDomain (I := I) (M := M) g).smul_mem (2 : ℝ) hw2_dom
    · -- H1ComplToLp (w1 - 2 • w2 - w3) = H1ComplToLp w1 - 2 • H1ComplToLp w2 - H1ComplToLp w3.
      rw [map_sub, map_sub, map_smul]
      rw [hw1_eq, hw2_eq, hw3_eq]
      exact h_lp_identity.symm
  -- Conclude: smoothMulHC φ u_h ∈ laplacianDomainPow g 2.
  -- By laplacianDomainPow_succ_mem_iff (with k = 1): smoothMulHC φ u_h ∈ laplacianDomainPow g 2
  --   iff ∃ f. smoothMulHC φ u_h = resolvent g (resolventL2 g f).
  -- iteratedResolventL2 g 1 = resolventL2 g (definition).
  -- And smoothMulHC φ u_h = resolvent g (preimage⟨smoothMulHC φ u_h⟩) (resolvent_preimage_eq).
  -- So we need: preimage⟨smoothMulHC φ u_h⟩ = resolventL2 g (some f).
  -- resolventL2 g = H1ComplToLp ∘ resolvent (definition).
  -- preimage⟨smoothMulHC φ u_h⟩ ∈ H1ComplToLp '' laplacianDomain g
  --   ↔ ∃ w ∈ laplacianDomain g. H1ComplToLp w = preimage⟨smoothMulHC φ u_h⟩
  --   ↔ ∃ f. H1ComplToLp (resolvent g f) = preimage⟨smoothMulHC φ u_h⟩
  --   ↔ ∃ f. resolventL2 g f = preimage⟨smoothMulHC φ u_h⟩.
  obtain ⟨w, hw_dom, hw_eq⟩ := h_in_image
  obtain ⟨f, hf⟩ := (laplacianDomain_mem_iff (I := I) (M := M) g).mp hw_dom
  -- hf : w = resolvent g f.
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [laplacianDomainPow_succ_mem_iff]
  refine ⟨f, ?_⟩
  rw [iteratedResolventL2_one]
  -- Need: smoothMulHC φ u_h = resolvent g (resolventL2 g f).
  -- We have:
  --   smoothMulHC φ u_h = resolvent g (preimage⟨smoothMulHC φ u_h⟩)  (by `resolvent_laplacianDomain_preimage_eq`)
  --   preimage⟨smoothMulHC φ u_h⟩ = H1ComplToLp w  (hw_eq.symm)
  --   H1ComplToLp w = H1ComplToLp (resolvent g f)  (hf)
  --   H1ComplToLp (resolvent g f) = resolventL2 g f  (definitionally).
  -- Chaining gives the goal.
  have h1 : (smoothMulHC (I := I) (M := M) g φ u_h : H1Compl g) =
      resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h,
            smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩) := by
    rw [resolvent_laplacianDomain_preimage_eq]
  rw [h1]
  -- Goal: resolvent g (preimage⟨smoothMulHC φ u_h⟩) = resolvent g (resolventL2 g f).
  congr 1
  -- preimage⟨smoothMulHC φ u_h⟩ = resolventL2 g f.
  rw [← hw_eq]
  -- H1ComplToLp w = resolventL2 g f.
  rw [hf]
  rfl

/-! ### Forward direction: iterated closure → `gradInnerCLM` image membership -/

/-- **Forward implication (iterated closure → gradInnerCLM image)**.

For `u_h ∈ laplacianDomainPow g 2`, if `smoothMulHC g φ u_h ∈
laplacianDomainPow g 2`, then `gradInnerCLM g φ u_h` lifts to an
`H1Compl` element in `laplacianDomain g`. -/
theorem gradInnerCLM_mem_image_of_smoothMulHC_mem_pow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_sM : smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  have hu_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 hu_h
  have h_sM_dom := laplacianDomainPow_succ_subset_laplacianDomain
    (I := I) (M := M) g 1 h_sM
  -- preimage⟨smoothMulHC φ u_h⟩ lifts to H1Compl via h_sM ∈ laplacianDomainPow g 2.
  -- Use preimageLift on smoothMulHC φ u_h.
  -- Let z := preimageLift g h_sM ∈ laplacianDomain g (lift of preimage⟨smoothMulHC φ u_h⟩).
  -- Then H1ComplToLp z = preimage⟨smoothMulHC φ u_h, h_sM_dom⟩ — but wait:
  -- preimage⟨smoothMulHC φ u_h, smoothMulHC_mem_laplacianDomain ...⟩ vs
  -- preimage⟨smoothMulHC φ u_h, h_sM_dom⟩
  -- — these are the same Lp element (preimage is well-defined up to membership proof).
  have h_preimage_unique :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h,
            smoothMulHC_mem_laplacianDomain (I := I) (M := M) g φ hu_dom⟩ =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulHC (I := I) (M := M) g φ u_h, h_sM_dom⟩ := by
    -- preimage depends only on the H1Compl element, not on the proof.
    rfl
  -- The headline identity for 2 • gradInnerCLM φ u_h.
  have h_identity := gradInnerCLM_eq_two_inv_preimageDiff
    (I := I) (M := M) g φ hu_dom
  -- Lift each RHS summand to H1Compl.
  -- Summand 1: smoothMulLp φ (preimage⟨u_h⟩) — by h_sM_mem above.
  have h1 := smoothMulLp_preimage_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_h
  obtain ⟨w1, hw1_dom, hw1_eq⟩ := h1
  -- Summand 2: -preimage⟨smoothMulHC φ u_h⟩ — lift via preimageLift on h_sM.
  have w2_eq := H1ComplToLp_preimageLift (I := I) (M := M) g h_sM
  have w2_dom := preimageLift_mem_laplacianDomain (I := I) (M := M) g h_sM
  -- Summand 3: smoothMulLp Δφ (H1ComplToLp u_h) — by smoothMulHC g (Δφ) u_h ∈ laplacianDomain g.
  have h3 := smoothMulLp_DeltaPhi_in_image_laplacianDomain
    (I := I) (M := M) g φ hu_dom
  obtain ⟨w3, hw3_dom, hw3_eq⟩ := h3
  -- Combine: 2 • gradInnerCLM φ u_h = H1ComplToLp (w1 - preimageLift g h_sM - w3).
  -- So gradInnerCLM φ u_h = (1/2) • H1ComplToLp (...).
  -- Equivalently, gradInnerCLM φ u_h = H1ComplToLp ((1/2) • (w1 - preimageLift g h_sM - w3)).
  refine ⟨(1/2 : ℝ) • (w1 - preimageLift (I := I) (M := M) g h_sM - w3), ?_, ?_⟩
  · -- (1/2) • (w1 - preimageLift g h_sM - w3) ∈ laplacianDomain g.
    refine (laplacianDomain (I := I) (M := M) g).smul_mem (1/2 : ℝ) ?_
    refine sub_mem (sub_mem hw1_dom w2_dom) hw3_dom
  · -- H1ComplToLp ((1/2) • ...) = (1/2) • H1ComplToLp(...).
    -- And H1ComplToLp (w1 - preimageLift - w3) = LHS - LHS - LHS.
    -- We need: H1ComplToLp ((1/2) • (w1 - preimageLift g h_sM - w3)) = gradInnerCLM φ u_h.
    rw [map_smul, map_sub, map_sub]
    rw [hw1_eq, w2_eq, hw3_eq]
    rw [h_preimage_unique.symm]
    -- We're left with goal:
    --   (1/2) • (smoothMulLp φ (preimage⟨u_h⟩) - preimage⟨smoothMulHC φ u_h⟩ - smoothMulLp Δφ (H1ComplToLp u_h))
    --     = gradInnerCLM φ u_h.
    -- By h_identity (after multiplying both sides by 1/2):
    rw [← h_identity]
    -- Goal: (1/2 : ℝ) • ((2 : ℝ) • gradInnerCLM g φ u_h) = gradInnerCLM g φ u_h.
    rw [smul_smul]
    norm_num

/-! ### Two-sided equivalence -/

/-- **Equivalence theorem**: for `u_h ∈ laplacianDomainPow g 2`,

```
smoothMulHC g φ u_h ∈ laplacianDomainPow g 2
  ↔ gradInnerCLM g φ u_h ∈ H1ComplToLp '' laplacianDomain g.
```

This localizes the iterated-closure question to a single sharp statement:
whether the gradient-inner-product Lp class is in the image of
`H1ComplToLp` restricted to `laplacianDomain g`. Equivalently, whether
`g(∇φ, ∇u_h)` is H¹ chart-wise (the "H²-of-product" question for `φ · u_h`).

The forward direction is `gradInnerCLM_mem_image_of_smoothMulHC_mem_pow_two`;
the reverse is `smoothMulHC_mem_pow_two_of_gradInnerCLM_mem_image`. -/
theorem smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulHC (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 ↔
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  refine ⟨gradInnerCLM_mem_image_of_smoothMulHC_mem_pow_two
    (I := I) (M := M) g φ hu_h, ?_⟩
  exact smoothMulHC_mem_pow_two_of_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h

/-! ## Step 3: smooth-case discharge of `gradInnerCLM ∈ H1ComplToLp '' laplacianDomain g`

For smooth `v ∈ SmoothScalar g`, the gradient inner product
`x ↦ g.inner x (gradFun g φ x) (gradFun g v.toFun x)` is C^∞ on `M` (by
`contMDiff_g_inner_of_smooth_sections`). Hence it lifts to a smooth scalar,
whose `smoothToH1Compl` image lies in `laplacianDomain g` and whose
`H1ComplToLp` image is precisely `gradInnerCLM g φ (smoothToH1Compl v) =
gradInnerSmooth g φ v`. -/

/-- The smooth scalar representing the pointwise gradient inner product
`x ↦ g.inner x (∇φ x) (∇v x)` for smooth `φ, v`. -/
noncomputable def gradInnerSmoothBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x => g.inner x (gradFun (I := I) g (φ : C^∞⟮I, M; ℝ⟯) x)
    (gradFun (I := I) g v.toFun x)
  smooth := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g φ.contMDiff) (grad_g (I := I) g v.smooth)
    refine h.congr ?_
    intro x
    change g.inner x ((grad_g (I := I) g φ.contMDiff :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g v.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v.toFun x)
    rw [grad_g_apply, grad_g_apply]

@[simp] lemma gradInnerSmoothBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v.toFun x) := rfl

/-- For smooth `v`, `gradInnerSmooth g φ v` (the Lp class) equals
`smoothToLp g (gradInnerSmoothBundle g φ v)`. -/
theorem gradInnerSmooth_eq_smoothToLp_bundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g φ v =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) := by
  apply MeasureTheory.Lp.ext
  refine (gradInnerSmooth_coeFn (I := I) (M := M) g φ v).trans ?_
  refine (MemLp.coeFn_toLp (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two).symm.trans ?_
  -- Both sides are the same pointwise function definitionally.
  refine Filter.Eventually.of_forall ?_
  intro x; rfl

/-- **Smooth-case discharge**: for smooth `v`, the gradient inner product
`gradInnerCLM g φ (smoothToH1Compl v)` lies in `H1ComplToLp '' laplacianDomain g`.

The discharge is direct: the smooth scalar
`gradInnerSmoothBundle g φ v` has its `smoothToH1Compl` lift in
`laplacianDomain g`, and the `H1ComplToLp` of that lift equals
`gradInnerCLM g φ (smoothToH1Compl v) = gradInnerSmooth g φ v`. -/
theorem gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  -- Lift to smooth scalar; smoothToH1Compl preserves laplacianDomain.
  refine ⟨smoothToH1Compl (I := I) (M := M) g
    (gradInnerSmoothBundle (I := I) (M := M) g φ v), ?_, ?_⟩
  · exact smoothToH1Compl_mem_laplacianDomain
      (I := I) (M := M) (gradInnerSmoothBundle (I := I) (M := M) g φ v)
  · rw [H1ComplToLp_smoothToH1Compl]
    rw [gradInnerCLM_smoothToH1Compl]
    rw [gradInnerSmooth_eq_smoothToLp_bundle]

/-- Specialised form: for smooth `v`, the bottleneck statement (`gradInnerCLM
g φ u_h ∈ H1ComplToLp '' laplacianDomain g`) holds. Hence by the equivalence
`smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image`, the iterated closure
`smoothMulHC g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2` follows once
`smoothToH1Compl v ∈ laplacianDomainPow g 2`. The latter is automatic since
the variational Laplacian on smooth scalars agrees with the classical
Laplacian, which iterates within smooth scalars. -/
theorem smoothToH1Compl_mem_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g v ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  classical
  -- By definition, laplacianDomainPow g 2 = laplacianDomainPow g (1+1)
  --   = range(resolvent ∘ iteratedResolventL2 g 1) = range(resolvent ∘ resolventL2).
  -- We need: ∃ f. smoothToH1Compl v = resolvent g (resolventL2 g f).
  -- Take f := smoothToLp g (Δ²_classical-something). Specifically:
  --   smoothToH1Compl v = resolvent g (smoothToLp ((1-Δ)v))   (by smooth bridge).
  -- So we need: smoothToLp ((1-Δ)v) = resolventL2 g f for some f.
  -- Let w := v.oneSubLapClassical (= (1-Δ_classical) v, a smooth scalar).
  -- Then smoothToH1Compl w ∈ laplacianDomain g, and resolventL2 g w.oneSubLapClassical =
  --   H1ComplToLp(resolvent g w.oneSubLapClassical.smoothToLp) = ...
  -- Actually the cleanest path: smoothToH1Compl v = resolvent (smoothToLp v.oneSubLapClassical),
  -- and smoothToLp v.oneSubLapClassical = resolventL2 (smoothToLp v.oneSubLapClassical.oneSubLapClassical).
  -- So f := smoothToLp ((v.oneSubLapClassical).oneSubLapClassical) works.
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [laplacianDomainPow_succ_mem_iff]
  refine ⟨smoothToLp (I := I) (M := M) g
    v.oneSubLapClassical.oneSubLapClassical, ?_⟩
  rw [iteratedResolventL2_one]
  -- Goal: smoothToH1Compl v = resolvent g (resolventL2 g (smoothToLp v.oneSubLapClassical.oneSubLapClassical)).
  -- Apply smooth bridge: smoothToH1Compl v = resolvent g (smoothToLp v.oneSubLapClassical).
  rw [smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) v]
  -- Goal: resolvent g (smoothToLp v.oneSubLapClassical) =
  --       resolvent g (resolventL2 g (smoothToLp v.oneSubLapClassical.oneSubLapClassical)).
  congr 1
  -- smoothToLp v.oneSubLapClassical = resolventL2 g (smoothToLp v.oneSubLapClassical.oneSubLapClassical).
  -- By definition: resolventL2 g = H1ComplToLp ∘ resolvent.
  -- So: resolventL2 g (smoothToLp w.oneSubLapClassical) = H1ComplToLp (resolvent g (smoothToLp w.oneSubLapClassical))
  --     = H1ComplToLp (smoothToH1Compl w)   (smooth bridge for w := v.oneSubLapClassical)
  --     = smoothToLp w   (H1ComplToLp ∘ smoothToH1Compl).
  -- So we need: smoothToLp v.oneSubLapClassical = smoothToLp v.oneSubLapClassical. ✓
  rw [show resolventL2 (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical.oneSubLapClassical) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical.oneSubLapClassical)) from rfl]
  rw [← smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    v.oneSubLapClassical]
  rw [H1ComplToLp_smoothToH1Compl]

/-- **Smooth-case full discharge**: for smooth `v`,
`smoothMulHC g φ (smoothToH1Compl v) ∈ laplacianDomainPow g 2`.

This is the smooth case of the iterated closure bottleneck. It follows from
`gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain` (the smooth-case
discharge of `gradInnerCLM`) combined with the equivalence theorem
`smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image`. -/
theorem smoothMulHC_smoothToH1Compl_mem_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulHC (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [smoothMulHC_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)]
  exact gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

end GradInnerLpIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
