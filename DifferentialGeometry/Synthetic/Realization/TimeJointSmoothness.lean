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
