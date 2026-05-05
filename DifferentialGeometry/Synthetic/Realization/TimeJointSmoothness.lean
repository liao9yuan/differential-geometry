import DifferentialGeometry.Synthetic.Realization.TimeDeriv

/-!
# Two-Time Smooth Families on `C^∞⟮I, M; ℝ⟯`

Concrete realisation of the two-time smoothness predicate used by the
`TimeRegularFam2` class. A family
`f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯`
is **two-time smooth** when the fully uncurried map
`((τ₁, τ₂), x) ↦ f (τ₁, τ₂) x`
is jointly `C^∞` on `(ℝ × ℝ) × M`, equipped with the product model
`(𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I`.

This file establishes nine structural theorems about `concreteIsSmoothFam2`:

* four **closure axioms** — constants, pointwise addition, pointwise
  multiplication, pointwise negation;
* two **single-time embeddings** — a one-time smooth family of either the
  first or second coordinate is two-time smooth;
* three **slice axioms** — the diagonal `τ ↦ G (τ, τ)` and the frozen
  slices `τ ↦ G (τ, τ₀)`, `τ ↦ G (τ₀, τ)` are all one-time smooth.

These results are the structural ingredients consumed by P29.2.5 to assemble
the `TimeRegularFam2` instance; the remaining axiom `dt_apply_diag_leibniz`
is proved separately (P29.2.4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- A family `f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯` is **two-time smooth** when the fully
uncurried map `((τ₁, τ₂), x) ↦ f (τ₁, τ₂) x` is jointly `C^∞` on
`(ℝ × ℝ) × M`, equipped with the product model
`(𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I`. -/
def concreteIsSmoothFam2 (f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) : Prop :=
  ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => f p.1 p.2)

-- ============================================================
-- Closure axioms
-- ============================================================

/-- Constant two-time families are two-time smooth. -/
theorem concreteIsSmoothFam2_const (c : C^∞⟮I, M; ℝ⟯) :
    concreteIsSmoothFam2 I M (fun _ => c) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => c p.2)
  exact c.contMDiff.comp contMDiff_snd

/-- Two-time smooth families are closed under pointwise addition. -/
theorem concreteIsSmoothFam2_add (f g : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2 I M f) (hg : concreteIsSmoothFam2 I M g) :
    concreteIsSmoothFam2 I M (f + g) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => (f + g) p.1 p.2)
  have heq : (fun p : (ℝ × ℝ) × M => (f + g) p.1 p.2) =
      (fun p : (ℝ × ℝ) × M => f p.1 p.2) + (fun p : (ℝ × ℝ) × M => g p.1 p.2) := by
    funext p
    change (f p.1 + g p.1) p.2 = f p.1 p.2 + g p.1 p.2
    simp [ContMDiffMap.coe_add]
  rw [heq]
  exact hf.add hg

/-- Two-time smooth families are closed under pointwise multiplication. -/
theorem concreteIsSmoothFam2_mul (f g : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2 I M f) (hg : concreteIsSmoothFam2 I M g) :
    concreteIsSmoothFam2 I M (f * g) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => (f * g) p.1 p.2)
  have heq : (fun p : (ℝ × ℝ) × M => (f * g) p.1 p.2) =
      (fun p : (ℝ × ℝ) × M => f p.1 p.2) * (fun p : (ℝ × ℝ) × M => g p.1 p.2) := by
    funext p
    change (f p.1 * g p.1) p.2 = f p.1 p.2 * g p.1 p.2
    simp [ContMDiffMap.coe_mul]
  rw [heq]
  exact hf.mul hg

/-- Two-time smooth families are closed under pointwise negation. -/
theorem concreteIsSmoothFam2_neg (f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2 I M f) :
    concreteIsSmoothFam2 I M (-f) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => (-f) p.1 p.2)
  have heq : (fun p : (ℝ × ℝ) × M => (-f) p.1 p.2) =
      (fun p : (ℝ × ℝ) × M => -(f p.1 p.2)) := by
    funext p
    change (-(f p.1)) p.2 = -(f p.1 p.2)
    simp [ContMDiffMap.coe_neg]
  rw [heq]
  exact hf.neg

-- ============================================================
-- Single-time embeddings
-- ============================================================

/-- A one-time smooth family depending only on the first coordinate is two-time
smooth. -/
theorem concreteIsSmoothFam2_of_single_fst (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    concreteIsSmoothFam2 I M (fun p => f p.1) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => f p.1.1 p.2)
  -- Factor through the projection `((τ₁, τ₂), x) ↦ (τ₁, x)`.
  have hproj : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : (ℝ × ℝ) × M => (p.1.1, p.2)) :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  exact hf.comp hproj

/-- A one-time smooth family depending only on the second coordinate is two-time
smooth. -/
theorem concreteIsSmoothFam2_of_single_snd (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam I M f) :
    concreteIsSmoothFam2 I M (fun p => f p.2) := by
  change ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : (ℝ × ℝ) × M => f p.1.2 p.2)
  -- Factor through the projection `((τ₁, τ₂), x) ↦ (τ₂, x)`.
  have hproj : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : (ℝ × ℝ) × M => (p.1.2, p.2)) :=
    (contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd
  exact hf.comp hproj

-- ============================================================
-- Slice / diagonal projections
-- ============================================================

/-- The diagonal of a two-time smooth family is one-time smooth. -/
theorem concreteIsSmoothFam2_diag (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hG : concreteIsSmoothFam2 I M G) :
    concreteIsSmoothFam I M (fun τ => G (τ, τ)) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => G (p.1, p.1) p.2)
  -- Lift via `(τ, x) ↦ ((τ, τ), x)`.
  have hlift :
      ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × M => ((p.1, p.1), p.2)) :=
    (contMDiff_fst.prodMk contMDiff_fst).prodMk contMDiff_snd
  exact hG.comp hlift

/-- The left-frozen slice `τ ↦ G (τ, τ₀)` of a two-time smooth family is
one-time smooth. -/
theorem concreteIsSmoothFam2_slice_left (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (τ₀ : ℝ)
    (hG : concreteIsSmoothFam2 I M G) :
    concreteIsSmoothFam I M (fun τ => G (τ, τ₀)) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => G (p.1, τ₀) p.2)
  -- Lift via `(τ, x) ↦ ((τ, τ₀), x)`.
  have hlift :
      ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × M => ((p.1, τ₀), p.2)) :=
    (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
  exact hG.comp hlift

/-- The right-frozen slice `τ ↦ G (τ₀, τ)` of a two-time smooth family is
one-time smooth. -/
theorem concreteIsSmoothFam2_slice_right (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (τ₀ : ℝ)
    (hG : concreteIsSmoothFam2 I M G) :
    concreteIsSmoothFam I M (fun τ => G (τ₀, τ)) := by
  change ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => G (τ₀, p.1) p.2)
  -- Lift via `(τ, x) ↦ ((τ₀, τ), x)`.
  have hlift :
      ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × M => ((τ₀, p.1), p.2)) :=
    (contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd
  exact hG.comp hlift

-- ============================================================
-- Diagonal chain rule
-- ============================================================

/-- **Concrete diagonal chain rule.** Given a two-time smooth family
    `G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯`, the diagonal time derivative
    `∂_τ[G (τ, τ)]` at `t` splits into the sum of the two single-variable
    partial derivatives. Follows from the Mathlib chain rule applied to the
    uncurried jointly-smooth scalar function `F(τ₁, τ₂) := G(τ₁, τ₂)(x)`
    at each base point `x`. -/
theorem concreteIsSmoothFam2_dt_apply_diag_leibniz
    (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hG : concreteIsSmoothFam2 I M G) :
    (concreteTimeDerivativeData I M).dt_apply (fun τ => G (τ, τ)) t =
    (concreteTimeDerivativeData I M).dt_apply (fun τ => G (τ, t)) t +
    (concreteTimeDerivativeData I M).dt_apply (fun τ => G (t, τ)) t := by
  -- Name the three single-time smooth families obtained by projection.
  set fDiag : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (τ, τ) with hfDiag_def
  set fLeft : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (τ, t) with hfLeft_def
  set fRight : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (t, τ) with hfRight_def
  have hDiag : concreteIsSmoothFam I M fDiag :=
    concreteIsSmoothFam2_diag I M G hG
  have hLeft : concreteIsSmoothFam I M fLeft :=
    concreteIsSmoothFam2_slice_left I M G t hG
  have hRight : concreteIsSmoothFam I M fRight :=
    concreteIsSmoothFam2_slice_right I M G t hG
  -- Prove the equality pointwise at each `x₀ : M`.
  ext x₀
  -- Scalar-valued uncurrying: the real-valued function of two time variables.
  set F : ℝ × ℝ → ℝ := fun q => G q x₀ with hF_def
  -- `F` is jointly `C^∞` on `ℝ × ℝ`: extract from `hG` by composing with
  -- `q ↦ (q, x₀)`, then convert the product-of-self-models formulation into
  -- the self-model-of-the-product formulation using `modelWithCornersSelf_prod`
  -- and `chartedSpaceSelf_prod`.
  have hF_contMDiff :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F := by
    have hpair :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
          (fun q : ℝ × ℝ => (q, x₀)) :=
      contMDiff_id.prodMk contMDiff_const
    exact hG.comp hpair
  have hF_smooth : ContDiff ℝ ∞ F := by
    rw [show (∞ : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl,
        ← contMDiff_iff_contDiff]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hF_contMDiff
  have hF_diff : Differentiable ℝ F := hF_smooth.differentiable (by decide)
  -- The total Fréchet derivative of `F` at `(t, t)`.
  set L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ F (t, t) with hL_def
  have hFD : HasFDerivAt F L (t, t) := (hF_diff (t, t)).hasFDerivAt
  -- 1-D `HasDerivAt` facts for the three parameterizations.
  have hasDerivAt_pairLeft : HasDerivAt (fun τ : ℝ => (τ, t)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t t)
  have hasDerivAt_pairRight : HasDerivAt (fun τ : ℝ => (t, τ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t t).prodMk (hasDerivAt_id t)
  have hasDerivAt_pairDiag : HasDerivAt (fun τ : ℝ => (τ, τ)) ((1 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_id t)
  -- Chain rule: compose `F` with each parameterization to get `HasDerivAt` of
  -- the composite scalar functions.
  have hasDerivAt_sliceLeft :
      HasDerivAt (F ∘ fun τ : ℝ => (τ, t)) (L (1, 0)) t :=
    hFD.comp_hasDerivAt (f := fun τ : ℝ => (τ, t)) (x := t)
      (f' := ((1 : ℝ), (0 : ℝ))) hasDerivAt_pairLeft
  have hasDerivAt_sliceRight :
      HasDerivAt (F ∘ fun τ : ℝ => (t, τ)) (L (0, 1)) t :=
    hFD.comp_hasDerivAt (f := fun τ : ℝ => (t, τ)) (x := t)
      (f' := ((0 : ℝ), (1 : ℝ))) hasDerivAt_pairRight
  have hasDerivAt_sliceDiag :
      HasDerivAt (F ∘ fun τ : ℝ => (τ, τ)) (L (1, 1)) t :=
    hFD.comp_hasDerivAt (f := fun τ : ℝ => (τ, τ)) (x := t)
      (f' := ((1 : ℝ), (1 : ℝ))) hasDerivAt_pairDiag
  -- Convert each `HasDerivAt` into a `deriv = _` equality.
  have hSliceLeft_eq : deriv (fun τ : ℝ => F (τ, t)) t = L (1, 0) :=
    hasDerivAt_sliceLeft.deriv
  have hSliceRight_eq : deriv (fun τ : ℝ => F (t, τ)) t = L (0, 1) :=
    hasDerivAt_sliceRight.deriv
  have hSliceDiag_eq : deriv (fun τ : ℝ => F (τ, τ)) t = L (1, 1) :=
    hasDerivAt_sliceDiag.deriv
  -- Linearity: `L (1, 1) = L (1, 0) + L (0, 1)`.
  have hLsplit : L (1, 1) = L (1, 0) + L (0, 1) := by
    have h11 : ((1, 1) : ℝ × ℝ) = ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by simp
    rw [h11, L.map_add]
  have hDeriv_split :
      deriv (fun τ : ℝ => F (τ, τ)) t =
        deriv (fun τ : ℝ => F (τ, t)) t + deriv (fun τ : ℝ => F (t, τ)) t := by
    rw [hSliceDiag_eq, hSliceLeft_eq, hSliceRight_eq, hLsplit]
  -- Unfold `dt_apply` on each of the three families.  For a smooth family
  -- `f : ℝ → C^∞⟮I, M; ℝ⟯`, `(dt_apply f t) x₀ = deriv (fun u => f u x₀) t`.
  have hLiftDiag :
      ((concreteLift I M fDiag : SmoothTimeAlgebra I M) : ℝ × M → ℝ) =
        fun p => fDiag p.1 p.2 :=
    concreteEval_concreteLift_apply I M fDiag hDiag
  have hLiftLeft :
      ((concreteLift I M fLeft : SmoothTimeAlgebra I M) : ℝ × M → ℝ) =
        fun p => fLeft p.1 p.2 :=
    concreteEval_concreteLift_apply I M fLeft hLeft
  have hLiftRight :
      ((concreteLift I M fRight : SmoothTimeAlgebra I M) : ℝ × M → ℝ) =
        fun p => fRight p.1 p.2 :=
    concreteEval_concreteLift_apply I M fRight hRight
  -- Slice equality for each family.
  have hGoalDiag :
      (concreteTimeDerivativeData I M).dt_apply fDiag t x₀ =
        deriv (fun u : ℝ => F (u, u)) t := by
    change (concreteDt I M (concreteLift I M fDiag)) (t, x₀) = _
    change deriv (fun u : ℝ =>
        ((concreteLift I M fDiag : SmoothTimeAlgebra I M) : ℝ × M → ℝ) (u, x₀)) t = _
    congr 1
    funext u
    rw [hLiftDiag]
  have hGoalLeft :
      (concreteTimeDerivativeData I M).dt_apply fLeft t x₀ =
        deriv (fun u : ℝ => F (u, t)) t := by
    change (concreteDt I M (concreteLift I M fLeft)) (t, x₀) = _
    change deriv (fun u : ℝ =>
        ((concreteLift I M fLeft : SmoothTimeAlgebra I M) : ℝ × M → ℝ) (u, x₀)) t = _
    congr 1
    funext u
    rw [hLiftLeft]
  have hGoalRight :
      (concreteTimeDerivativeData I M).dt_apply fRight t x₀ =
        deriv (fun u : ℝ => F (t, u)) t := by
    change (concreteDt I M (concreteLift I M fRight)) (t, x₀) = _
    change deriv (fun u : ℝ =>
        ((concreteLift I M fRight : SmoothTimeAlgebra I M) : ℝ × M → ℝ) (u, x₀)) t = _
    congr 1
    funext u
    rw [hLiftRight]
  -- Assemble the final pointwise equality.
  change (concreteTimeDerivativeData I M).dt_apply fDiag t x₀ =
    ((concreteTimeDerivativeData I M).dt_apply fLeft t +
      (concreteTimeDerivativeData I M).dt_apply fRight t) x₀
  rw [ContMDiffMap.coe_add]
  change (concreteTimeDerivativeData I M).dt_apply fDiag t x₀ =
    (concreteTimeDerivativeData I M).dt_apply fLeft t x₀ +
      (concreteTimeDerivativeData I M).dt_apply fRight t x₀
  rw [hGoalDiag, hGoalLeft, hGoalRight, hDeriv_split]

/-- **Concrete `TimeRegularFam2` instance** for the joint-smooth time algebra.
    Bundles the nine structural theorems (closure, embedding, slice) together
    with the diagonal chain rule from `concreteIsSmoothFam2_dt_apply_diag_leibniz`,
    exposing `concreteIsSmoothFam2` as the class-level predicate. -/
noncomputable instance concreteTimeRegularFam2 :
    TimeRegularFam2 (concreteTimeDerivativeData I M) where
  isSmoothFam2              := concreteIsSmoothFam2 I M
  isSmoothFam2_const        := concreteIsSmoothFam2_const I M
  isSmoothFam2_add          := concreteIsSmoothFam2_add I M
  isSmoothFam2_mul          := concreteIsSmoothFam2_mul I M
  isSmoothFam2_neg          := concreteIsSmoothFam2_neg I M
  isSmoothFam2_of_single_fst := concreteIsSmoothFam2_of_single_fst I M
  isSmoothFam2_of_single_snd := concreteIsSmoothFam2_of_single_snd I M
  diag_isSmoothFam          := concreteIsSmoothFam2_diag I M
  slice_left_isSmoothFam    := concreteIsSmoothFam2_slice_left I M
  slice_right_isSmoothFam   := concreteIsSmoothFam2_slice_right I M
  dt_apply_diag_leibniz     := concreteIsSmoothFam2_dt_apply_diag_leibniz I M

-- ============================================================
-- Subset-time 2-time smoothness
-- ============================================================

/-!
### Subset-time 2-time smoothness

Subset-time analogue of `concreteIsSmoothFam2`: a family
`f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯` is **subset 2-time smooth** on a set `s : Set ℝ`
when the fully uncurried map is jointly `ContMDiffOn` on `s ×ˢ s ×ˢ univ`,
*and* every left and right slice is subset 1-time smooth.

The slice conjuncts are what makes `slice_left_isSmoothFam` /
`slice_right_isSmoothFam` in the `TimeRegularFam2` class provable for any
`τ₀ : ℝ` (including `τ₀ ∉ s`): without them we could only recover slices
through points of `s`. In practice these slice witnesses are always easy
to produce for families arising from Ricci flow data.
-/

/-- A family `f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯` is **subset 2-time smooth** on `s`
when the fully uncurried map `((τ₁, τ₂), x) ↦ f (τ₁, τ₂) x` is jointly
`ContMDiffOn` on `(s ×ˢ s) ×ˢ univ`, *and* for every `τ₀ : ℝ` the left slice
`τ ↦ f (τ, τ₀)` and the right slice `τ ↦ f (τ₀, τ)` are each subset
1-time smooth on `s`. -/
def concreteIsSmoothFam2On (s : Set ℝ) (f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => f p.1 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M)) ∧
    (∀ τ₀ : ℝ, concreteIsSmoothFamOn I M s (fun τ => f (τ, τ₀))) ∧
    (∀ τ₀ : ℝ, concreteIsSmoothFamOn I M s (fun τ => f (τ₀, τ)))

/-- Global 2-time smoothness implies subset 2-time smoothness on any `s`. -/
theorem concreteIsSmoothFam2.of_global_to_on
    (s : Set ℝ) (f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2 I M f) :
    concreteIsSmoothFam2On I M s f := by
  refine ⟨hf.contMDiffOn, ?_, ?_⟩
  · intro τ₀
    exact concreteIsSmoothFam.of_global_to_on I M s _
      (concreteIsSmoothFam2_slice_left I M f τ₀ hf)
  · intro τ₀
    exact concreteIsSmoothFam.of_global_to_on I M s _
      (concreteIsSmoothFam2_slice_right I M f τ₀ hf)

/-- Constant subset 2-time families are subset 2-smooth. -/
theorem concreteIsSmoothFam2On_const (s : Set ℝ) (c : C^∞⟮I, M; ℝ⟯) :
    concreteIsSmoothFam2On I M s (fun _ => c) := by
  refine ⟨?_, ?_, ?_⟩
  · -- First conjunct: `(p, x) ↦ c x` on `(s × s) × univ` is smooth.
    exact (c.contMDiff.comp contMDiff_snd).contMDiffOn
  · intro _
    exact concreteIsSmoothFamOn_const I M s c
  · intro _
    exact concreteIsSmoothFamOn_const I M s c

/-- Subset 2-time smoothness is closed under pointwise addition. -/
theorem concreteIsSmoothFam2On_add (s : Set ℝ) (f g : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2On I M s f) (hg : concreteIsSmoothFam2On I M s g) :
    concreteIsSmoothFam2On I M s (f + g) := by
  obtain ⟨hfJoint, hfLeft, hfRight⟩ := hf
  obtain ⟨hgJoint, hgLeft, hgRight⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · -- First conjunct.
    change ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => (f + g) p.1 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M))
    have heq : (fun p : (ℝ × ℝ) × M => (f + g) p.1 p.2) =
        (fun p : (ℝ × ℝ) × M => f p.1 p.2) + (fun p : (ℝ × ℝ) × M => g p.1 p.2) := by
      funext p
      change (f p.1 + g p.1) p.2 = f p.1 p.2 + g p.1 p.2
      simp [ContMDiffMap.coe_add]
    rw [heq]
    exact hfJoint.add hgJoint
  · -- Left slices.
    intro τ₀
    have hadd_eq : (fun τ : ℝ => (f + g) (τ, τ₀)) =
        (fun τ : ℝ => f (τ, τ₀)) + (fun τ : ℝ => g (τ, τ₀)) := by
      funext τ; rfl
    rw [hadd_eq]
    exact concreteIsSmoothFamOn_add I M s _ _ (hfLeft τ₀) (hgLeft τ₀)
  · -- Right slices.
    intro τ₀
    have hadd_eq : (fun τ : ℝ => (f + g) (τ₀, τ)) =
        (fun τ : ℝ => f (τ₀, τ)) + (fun τ : ℝ => g (τ₀, τ)) := by
      funext τ; rfl
    rw [hadd_eq]
    exact concreteIsSmoothFamOn_add I M s _ _ (hfRight τ₀) (hgRight τ₀)

/-- Subset 2-time smoothness is closed under pointwise multiplication. -/
theorem concreteIsSmoothFam2On_mul (s : Set ℝ) (f g : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2On I M s f) (hg : concreteIsSmoothFam2On I M s g) :
    concreteIsSmoothFam2On I M s (f * g) := by
  obtain ⟨hfJoint, hfLeft, hfRight⟩ := hf
  obtain ⟨hgJoint, hgLeft, hgRight⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · change ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => (f * g) p.1 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M))
    have heq : (fun p : (ℝ × ℝ) × M => (f * g) p.1 p.2) =
        (fun p : (ℝ × ℝ) × M => f p.1 p.2) * (fun p : (ℝ × ℝ) × M => g p.1 p.2) := by
      funext p
      change (f p.1 * g p.1) p.2 = f p.1 p.2 * g p.1 p.2
      simp [ContMDiffMap.coe_mul]
    rw [heq]
    exact hfJoint.mul hgJoint
  · intro τ₀
    have hmul_eq : (fun τ : ℝ => (f * g) (τ, τ₀)) =
        (fun τ : ℝ => f (τ, τ₀)) * (fun τ : ℝ => g (τ, τ₀)) := by
      funext τ; rfl
    rw [hmul_eq]
    exact concreteIsSmoothFamOn_mul I M s _ _ (hfLeft τ₀) (hgLeft τ₀)
  · intro τ₀
    have hmul_eq : (fun τ : ℝ => (f * g) (τ₀, τ)) =
        (fun τ : ℝ => f (τ₀, τ)) * (fun τ : ℝ => g (τ₀, τ)) := by
      funext τ; rfl
    rw [hmul_eq]
    exact concreteIsSmoothFamOn_mul I M s _ _ (hfRight τ₀) (hgRight τ₀)

/-- Subset 2-time smoothness is closed under pointwise negation. -/
theorem concreteIsSmoothFam2On_neg (s : Set ℝ) (f : ℝ × ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : concreteIsSmoothFam2On I M s f) :
    concreteIsSmoothFam2On I M s (-f) := by
  obtain ⟨hfJoint, hfLeft, hfRight⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · change ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => (-f) p.1 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M))
    have heq : (fun p : (ℝ × ℝ) × M => (-f) p.1 p.2) =
        (fun p : (ℝ × ℝ) × M => -(f p.1 p.2)) := by
      funext p
      change (-(f p.1)) p.2 = -(f p.1 p.2)
      simp [ContMDiffMap.coe_neg]
    rw [heq]
    exact hfJoint.neg
  · intro τ₀
    have hneg_eq : (fun τ : ℝ => (-f) (τ, τ₀)) =
        -(fun τ : ℝ => f (τ, τ₀)) := by
      funext τ; rfl
    rw [hneg_eq]
    exact concreteIsSmoothFamOn_neg I M s _ (hfLeft τ₀)
  · intro τ₀
    have hneg_eq : (fun τ : ℝ => (-f) (τ₀, τ)) =
        -(fun τ : ℝ => f (τ₀, τ)) := by
      funext τ; rfl
    rw [hneg_eq]
    exact concreteIsSmoothFamOn_neg I M s _ (hfRight τ₀)

/-- A subset 1-time smooth family depending only on the first coordinate
is subset 2-time smooth. -/
theorem concreteIsSmoothFam2On_of_single_fst (s : Set ℝ)
    (f : ℝ → C^∞⟮I, M; ℝ⟯) (hf : concreteIsSmoothFamOn I M s f) :
    concreteIsSmoothFam2On I M s (fun p => f p.1) := by
  refine ⟨?_, ?_, ?_⟩
  · -- First conjunct: `(p, x) ↦ f p.1.1 x` on `(s × s) × univ` smoothness.
    -- Factor through the projection `((τ₁, τ₂), x) ↦ (τ₁, x)` which maps
    -- `(s × s) × univ` into `s × univ`, where `hf` holds.
    change ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => f p.1.1 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M))
    have hproj :
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : (ℝ × ℝ) × M => (p.1.1, p.2)) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    have hmap : Set.MapsTo (fun p : (ℝ × ℝ) × M => (p.1.1, p.2))
        ((s ×ˢ s) ×ˢ (Set.univ : Set M)) (s ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨hp.1.1, Set.mem_univ _⟩
    exact hf.comp hproj.contMDiffOn hmap
  · -- Left slice `τ ↦ f τ`: identical to `f`, use `hf`.
    intro _
    exact hf
  · -- Right slice `τ ↦ f τ₀`: constant in `τ`.
    intro τ₀
    exact concreteIsSmoothFamOn_const I M s (f τ₀)

/-- A subset 1-time smooth family depending only on the second coordinate
is subset 2-time smooth. -/
theorem concreteIsSmoothFam2On_of_single_snd (s : Set ℝ)
    (f : ℝ → C^∞⟮I, M; ℝ⟯) (hf : concreteIsSmoothFamOn I M s f) :
    concreteIsSmoothFam2On I M s (fun p => f p.2) := by
  refine ⟨?_, ?_, ?_⟩
  · change ContMDiffOn ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × ℝ) × M => f p.1.2 p.2) ((s ×ˢ s) ×ˢ (Set.univ : Set M))
    have hproj :
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : (ℝ × ℝ) × M => (p.1.2, p.2)) :=
      (contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd
    have hmap : Set.MapsTo (fun p : (ℝ × ℝ) × M => (p.1.2, p.2))
        ((s ×ˢ s) ×ˢ (Set.univ : Set M)) (s ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact ⟨hp.1.2, Set.mem_univ _⟩
    exact hf.comp hproj.contMDiffOn hmap
  · -- Left slice `τ ↦ f τ₀`: constant in `τ`.
    intro τ₀
    exact concreteIsSmoothFamOn_const I M s (f τ₀)
  · -- Right slice `τ ↦ f τ`: identical to `f`.
    intro _
    exact hf

/-- The diagonal of a subset 2-time smooth family is subset 1-time smooth. -/
theorem concreteIsSmoothFam2On_diag (s : Set ℝ)
    (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (hG : concreteIsSmoothFam2On I M s G) :
    concreteIsSmoothFamOn I M s (fun τ => G (τ, τ)) := by
  obtain ⟨hGJoint, _, _⟩ := hG
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => G (p.1, p.1) p.2) (s ×ˢ (Set.univ : Set M))
  -- Lift via `(τ, x) ↦ ((τ, τ), x)`. This map is `ContMDiff`, and maps
  -- `s × univ` into `(s × s) × univ`.
  have hlift :
      ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × M => ((p.1, p.1), p.2)) :=
    (contMDiff_fst.prodMk contMDiff_fst).prodMk contMDiff_snd
  have hmap : Set.MapsTo (fun p : ℝ × M => ((p.1, p.1), p.2))
      (s ×ˢ (Set.univ : Set M)) ((s ×ˢ s) ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact ⟨⟨hp.1, hp.1⟩, Set.mem_univ _⟩
  exact hGJoint.comp hlift.contMDiffOn hmap

/-- The left-frozen slice `τ ↦ G (τ, τ₀)` of a subset 2-time smooth family
is subset 1-time smooth (for any `τ₀ : ℝ`, including `τ₀ ∉ s`). -/
theorem concreteIsSmoothFam2On_slice_left (s : Set ℝ)
    (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (τ₀ : ℝ)
    (hG : concreteIsSmoothFam2On I M s G) :
    concreteIsSmoothFamOn I M s (fun τ => G (τ, τ₀)) :=
  hG.2.1 τ₀

/-- The right-frozen slice `τ ↦ G (τ₀, τ)` of a subset 2-time smooth family
is subset 1-time smooth (for any `τ₀ : ℝ`, including `τ₀ ∉ s`). -/
theorem concreteIsSmoothFam2On_slice_right (s : Set ℝ)
    (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (τ₀ : ℝ)
    (hG : concreteIsSmoothFam2On I M s G) :
    concreteIsSmoothFamOn I M s (fun τ => G (τ₀, τ)) :=
  hG.2.2 τ₀

/-- **Concrete subset-time diagonal chain rule.** Given a subset 2-smooth
family `G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯`, the subset-time diagonal derivative
`∂_τ[G (τ, τ)]` at `t` splits into the sum of the two single-variable
subset-time partial derivatives. For `t ∉ s` both sides are `0` vacuously.
For `t ∈ s` the identity reduces to the Mathlib chain rule with a
`HasFDerivWithinAt` at `(t, t)` on `s ×ˢ s`. -/
theorem concreteIsSmoothFam2On_dt_apply_diag_leibniz (s : Set ℝ)
    (hs : UniqueDiffOn ℝ s) (G : ℝ × ℝ → C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hG : concreteIsSmoothFam2On I M s G) :
    (concreteTimeDerivativeDataOn I M s hs).dt_apply (fun τ => G (τ, τ)) t =
    (concreteTimeDerivativeDataOn I M s hs).dt_apply (fun τ => G (τ, t)) t +
    (concreteTimeDerivativeDataOn I M s hs).dt_apply (fun τ => G (t, τ)) t := by
  obtain ⟨hGJoint, hGLeft, hGRight⟩ := hG
  -- Name the three single-time smooth families obtained by projection.
  set fDiag : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (τ, τ) with hfDiag_def
  set fLeft : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (τ, t) with hfLeft_def
  set fRight : ℝ → C^∞⟮I, M; ℝ⟯ := fun τ => G (t, τ) with hfRight_def
  have hDiag : concreteIsSmoothFamOn I M s fDiag :=
    concreteIsSmoothFam2On_diag I M s G ⟨hGJoint, hGLeft, hGRight⟩
  have hLeft : concreteIsSmoothFamOn I M s fLeft := hGLeft t
  have hRight : concreteIsSmoothFamOn I M s fRight := hGRight t
  -- Prove the equality pointwise at each `x₀ : M`.
  ext x₀
  -- Unfold `dt_apply` = `eval ∘ dt ∘ lift`, then `eval = .fam` at `t`.
  change (concreteDtOnFam I M hs (concreteLiftOn I M s fDiag) t : M → ℝ) x₀ =
    (((concreteDtOnFam I M hs (concreteLiftOn I M s fLeft) t) +
      (concreteDtOnFam I M hs (concreteLiftOn I M s fRight) t) :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀
  rw [ContMDiffMap.coe_add, Pi.add_apply]
  -- Split on `t ∈ s` vs `t ∉ s`.
  by_cases ht : t ∈ s
  · -- Case `t ∈ s`. Reduce each side to `derivWithin`.
    rw [concreteDtOnFam_apply_of_mem I M hs _ ht x₀,
        concreteDtOnFam_apply_of_mem I M hs _ ht x₀,
        concreteDtOnFam_apply_of_mem I M hs _ ht x₀]
    -- Rewrite `.fam` in each `derivWithin` to recover the underlying family.
    have hLiftDiag : (concreteLiftOn I M s fDiag).fam = fDiag :=
      concreteEvalOn_concreteLiftOn_apply I M fDiag hDiag
    have hLiftLeft : (concreteLiftOn I M s fLeft).fam = fLeft :=
      concreteEvalOn_concreteLiftOn_apply I M fLeft hLeft
    have hLiftRight : (concreteLiftOn I M s fRight).fam = fRight :=
      concreteEvalOn_concreteLiftOn_apply I M fRight hRight
    -- Scalar-valued uncurrying at `x₀`: `F : ℝ × ℝ → ℝ`.
    set F : ℝ × ℝ → ℝ := fun q => G q x₀ with hF_def
    have hSliceDiag_fn :
        (fun τ : ℝ => ((concreteLiftOn I M s fDiag).fam τ : M → ℝ) x₀) =
          fun τ : ℝ => F (τ, τ) := by
      funext τ
      have : (concreteLiftOn I M s fDiag).fam τ = fDiag τ :=
        congrFun hLiftDiag τ
      rw [this]
    have hSliceLeft_fn :
        (fun τ : ℝ => ((concreteLiftOn I M s fLeft).fam τ : M → ℝ) x₀) =
          fun τ : ℝ => F (τ, t) := by
      funext τ
      have : (concreteLiftOn I M s fLeft).fam τ = fLeft τ :=
        congrFun hLiftLeft τ
      rw [this]
    have hSliceRight_fn :
        (fun τ : ℝ => ((concreteLiftOn I M s fRight).fam τ : M → ℝ) x₀) =
          fun τ : ℝ => F (t, τ) := by
      funext τ
      have : (concreteLiftOn I M s fRight).fam τ = fRight τ :=
        congrFun hLiftRight τ
      rw [this]
    rw [hSliceDiag_fn, hSliceLeft_fn, hSliceRight_fn]
    -- Main step: `F` is `ContMDiffOn` on `s ×ˢ s`, and `(t, t) ∈ s ×ˢ s`.
    have hF_joint :
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F (s ×ˢ s) := by
      have hpair : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
          (fun q : ℝ × ℝ => (q, x₀)) :=
        contMDiff_id.prodMk contMDiff_const
      have hmap : Set.MapsTo (fun q : ℝ × ℝ => (q, x₀))
          (s ×ˢ s) ((s ×ˢ s) ×ˢ (Set.univ : Set M)) := by
        intro q hq; exact ⟨hq, Set.mem_univ _⟩
      exact hGJoint.comp hpair.contMDiffOn hmap
    -- Transport `ContMDiffOn` to `ContDiffOn` on `s ×ˢ s`.
    -- Reshape the source model/charted-space from `𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)` to
    -- `𝓘(ℝ, ℝ × ℝ)` via `modelWithCornersSelf_prod` and `chartedSpaceSelf_prod`.
    have hF_contDiffOn : ContDiffOn ℝ ∞ F (s ×ˢ s) := by
      rw [← contMDiffOn_iff_contDiffOn]
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hF_joint
    have hF_diffOn : DifferentiableOn ℝ F (s ×ˢ s) :=
      hF_contDiffOn.differentiableOn (by decide)
    have htt : (t, t) ∈ s ×ˢ s := ⟨ht, ht⟩
    -- Extract `HasFDerivWithinAt` at `(t, t)`.
    have hF_hasFDeriv :
        HasFDerivWithinAt F (fderivWithin ℝ F (s ×ˢ s) (t, t)) (s ×ˢ s) (t, t) :=
      (hF_diffOn (t, t) htt).hasFDerivWithinAt
    set L : ℝ × ℝ →L[ℝ] ℝ := fderivWithin ℝ F (s ×ˢ s) (t, t) with hL_def
    -- Three 1-D curves: `τ ↦ (τ, t)`, `τ ↦ (t, τ)`, `τ ↦ (τ, τ)`.
    have hPairLeft : HasDerivWithinAt (fun τ : ℝ => (τ, t)) ((1 : ℝ), (0 : ℝ)) s t :=
      (hasDerivWithinAt_id t s).prodMk (hasDerivWithinAt_const t s t)
    have hPairRight : HasDerivWithinAt (fun τ : ℝ => (t, τ)) ((0 : ℝ), (1 : ℝ)) s t :=
      (hasDerivWithinAt_const t s t).prodMk (hasDerivWithinAt_id t s)
    have hPairDiag : HasDerivWithinAt (fun τ : ℝ => (τ, τ)) ((1 : ℝ), (1 : ℝ)) s t :=
      (hasDerivWithinAt_id t s).prodMk (hasDerivWithinAt_id t s)
    -- `MapsTo` facts: each curve maps `s` into `s ×ˢ s`.
    have hMapLeft : Set.MapsTo (fun τ : ℝ => (τ, t)) s (s ×ˢ s) := by
      intro τ hτ; exact ⟨hτ, ht⟩
    have hMapRight : Set.MapsTo (fun τ : ℝ => (t, τ)) s (s ×ˢ s) := by
      intro τ hτ; exact ⟨ht, hτ⟩
    have hMapDiag : Set.MapsTo (fun τ : ℝ => (τ, τ)) s (s ×ˢ s) := by
      intro τ hτ; exact ⟨hτ, hτ⟩
    -- Compose `F` with each curve to obtain `HasDerivWithinAt` on `s`.
    -- We need a `HasFDerivWithinAt F _ _ (f x)` hypothesis; our `(t, t)` must
    -- match `f t` for each curve `f`. Use `_of_eq` to rewrite the base point.
    have hasDerivWithinAt_sliceLeft :
        HasDerivWithinAt ((fun q : ℝ × ℝ => F q) ∘ fun τ : ℝ => (τ, t))
          (L (1, 0)) s t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
        (f := fun τ : ℝ => (τ, t)) (x := t) hF_hasFDeriv hPairLeft hMapLeft rfl
    have hasDerivWithinAt_sliceRight :
        HasDerivWithinAt ((fun q : ℝ × ℝ => F q) ∘ fun τ : ℝ => (t, τ))
          (L (0, 1)) s t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
        (f := fun τ : ℝ => (t, τ)) (x := t) hF_hasFDeriv hPairRight hMapRight rfl
    have hasDerivWithinAt_sliceDiag :
        HasDerivWithinAt ((fun q : ℝ × ℝ => F q) ∘ fun τ : ℝ => (τ, τ))
          (L (1, 1)) s t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
        (f := fun τ : ℝ => (τ, τ)) (x := t) hF_hasFDeriv hPairDiag hMapDiag rfl
    -- Convert each to a `derivWithin = _` equality via `UniqueDiffWithinAt`.
    have hunique : UniqueDiffWithinAt ℝ s t := hs t ht
    have hSliceLeft_eq :
        derivWithin (fun τ : ℝ => F (τ, t)) s t = L (1, 0) :=
      hasDerivWithinAt_sliceLeft.derivWithin hunique
    have hSliceRight_eq :
        derivWithin (fun τ : ℝ => F (t, τ)) s t = L (0, 1) :=
      hasDerivWithinAt_sliceRight.derivWithin hunique
    have hSliceDiag_eq :
        derivWithin (fun τ : ℝ => F (τ, τ)) s t = L (1, 1) :=
      hasDerivWithinAt_sliceDiag.derivWithin hunique
    -- Linearity: `L (1, 1) = L (1, 0) + L (0, 1)`.
    have hLsplit : L (1, 1) = L (1, 0) + L (0, 1) := by
      have h11 : ((1, 1) : ℝ × ℝ) = ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by simp
      rw [h11, L.map_add]
    -- Assemble.
    rw [hSliceDiag_eq, hSliceLeft_eq, hSliceRight_eq, hLsplit]
  · -- Case `t ∉ s`. Both sides are 0.
    rw [concreteDtOnFam_of_notMem I M hs _ ht,
        concreteDtOnFam_of_notMem I M hs _ ht,
        concreteDtOnFam_of_notMem I M hs _ ht]
    change ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
      ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ + ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀
    simp

/-- **Concrete subset-time `TimeRegularFam2` instance**. Bundles all 10
subset-time structural theorems into the `TimeRegularFam2` class applied
to the subset-time `concreteTimeDerivativeDataOn I M s hs`. Registered as
an `instance` alongside `concreteTimeRegularFamOn` so that downstream
declarations (structure fields depending on `concreteTimeDerivativeDataOn`)
can resolve the typeclass automatically. -/
@[reducible]
noncomputable instance concreteTimeRegularFam2On
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    TimeRegularFam2 (concreteTimeDerivativeDataOn I M s hs) :=
  { isSmoothFam2              := concreteIsSmoothFam2On I M s
    isSmoothFam2_const        := concreteIsSmoothFam2On_const I M s
    isSmoothFam2_add          := concreteIsSmoothFam2On_add I M s
    isSmoothFam2_mul          := concreteIsSmoothFam2On_mul I M s
    isSmoothFam2_neg          := concreteIsSmoothFam2On_neg I M s
    isSmoothFam2_of_single_fst := concreteIsSmoothFam2On_of_single_fst I M s
    isSmoothFam2_of_single_snd := concreteIsSmoothFam2On_of_single_snd I M s
    diag_isSmoothFam          := concreteIsSmoothFam2On_diag I M s
    slice_left_isSmoothFam    := concreteIsSmoothFam2On_slice_left I M s
    slice_right_isSmoothFam   := concreteIsSmoothFam2On_slice_right I M s
    dt_apply_diag_leibniz     := concreteIsSmoothFam2On_dt_apply_diag_leibniz I M s hs }
