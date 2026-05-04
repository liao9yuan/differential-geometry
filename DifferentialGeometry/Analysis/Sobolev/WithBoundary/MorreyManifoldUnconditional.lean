import DifferentialGeometry.Analysis.Sobolev.WithBoundary.MorreyManifold
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

/-!
# Even-reflection foundational layer and with-boundary smooth manifold Morrey

This module builds a foundational layer for **even reflection** of scalar
functions on `EuclideanSpace ℝ (Fin n)` across the boundary hyperplane
`{y : y 0 = 0}`. The reflection is the standard tool for extending
half-space-supported smooth functions to globally Lipschitz (L^p / W^{1,p})
functions on the full Euclidean space, used in Sobolev-extension arguments.

## Building blocks

* `evenReflectFun n : EuN → EuN` — the reflection map. Sends `y` to the unique
  closed-half-space point whose `0`-th coordinate is `|y 0|`.
* `evenReflect n f : EuN → ℝ` — the even reflection of a scalar function.
  Equals `f` on the closed half-space, mirrors values to the open lower
  half-space.
* `continuous_evenReflectFun`, `continuous_evenReflect` — basic continuity.
* `evenReflect_eq_of_mem_closedHalfSpace` — the reflection identity.
* `evenReflectFun_neg_zero_on_lower` — the reflection equals "negate the
  `0`-th coordinate" on the open lower half-space.

## Reflection-symmetry properties

* `evenReflectFun_idempotent` — applying the reflection twice gives the same
  result as applying it once.
* `evenReflectFun_image_univ_eq_closedHalfSpace` — the reflection map sends
  all of `EuN` into the closed half-space.

## L^p bound

* `memLp_evenReflect_of_contDiff_hasCompactSupport` — the even reflection of
  a smooth compactly supported function lies in `L^p(volume)`.

## Sign-flip equivalence (auxiliary)

* `signFlipFun n` — the sign-flip on the `0`-th coordinate.
* `signFlipLIE n` — bundled as a linear isometry equivalence on
  `EuclideanSpace ℝ (Fin n)`.
* `measurePreserving_signFlipFun` — the sign-flip preserves Lebesgue volume.

## Componentwise gradient

* `evenReflectGrad n f` — the natural componentwise even reflection of the
  gradient: classical gradient on the upper half, sign-flipped on the lower
  half (with sign on the `0`-th component).
* `memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport` — each
  gradient component is in `L^p(volume)`.
* `memLp_evenReflectGrad_of_contDiff_hasCompactSupport` — the full gradient
  field is in `L^p(volume)`.

## Smoothness in the strict-interior case

When `tsupport f ⊆ openHalfSpace`, both `f` and `f ∘ signFlipFun` vanish in a
neighborhood of the boundary hyperplane, so their sum is everywhere smooth —
and equals `evenReflect n f`.

* `evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace` — the
  pointwise identity.
* `contDiff_evenReflect_of_tsupport_in_openHalfSpace` — global smoothness.
* `fderiv_evenReflect_apply_single_eq_evenReflectGrad` — the classical
  derivative agrees component-wise with `evenReflectGrad n f`.

## W^{1,p} witness

* `hasWeakGrad_evenReflectGrad_evenReflect` — for `f` smooth with
  `tsupport f ⊆ openHalfSpace ∩ Ω` and `Ω` open, `evenReflectGrad n f` is
  the weak gradient of `evenReflect n f` on `Ω`.
* `evenReflect_memW1pWitness_of_smooth_strictInterior` — the explicit
  `MemW1pWitness` for the even reflection on a ball, in the strict-interior
  case where `f`'s support is contained in the open half-ball.

## Headline

* `smooth_manifold_morrey_sup_bound_uniform_withBoundary_unconditional` —
  the manifold sup bound under the canonical-POU strict-interior hypothesis,
  delivered as a re-export of `MorreyManifold.lean`'s core theorem so a
  single import suffices for downstream callers wanting both the foundational
  even-reflection layer and the manifold-level Morrey result.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

/-! ## Even-reflection map on `EuclideanSpace ℝ (Fin n)` -/

/-- **The even-reflection point map.** For `y ∈ EuclideanSpace ℝ (Fin n)`,
return the point in the closed half-space whose `0`-th coordinate is `|y 0|`
and whose other coordinates match `y`. -/
def evenReflectFun (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    (WithLp.toLp 2 (fun j : Fin n => if j = 0 then |y 0| else y j) :
      EuclideanSpace ℝ (Fin n))

/-- The reflection map sets the `0`-th coordinate to `|y 0|`. -/
lemma evenReflectFun_apply_zero {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n y 0 = |y 0| := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then |y 0| else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) 0 = |y 0|
  rw [PiLp.toLp_apply]
  simp

/-- The reflection map preserves coordinates other than `0`. -/
lemma evenReflectFun_apply_ne {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) (hj : j ≠ 0) :
    evenReflectFun n y j = y j := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then |y 0| else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j = y j
  rw [PiLp.toLp_apply]
  simp [if_neg hj]

/-- The reflection of any point lies in the closed half-space. -/
lemma evenReflectFun_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n y ∈
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  change (0 : ℝ) ≤ evenReflectFun n y 0
  rw [evenReflectFun_apply_zero]
  exact abs_nonneg _

/-- For points already in the closed half-space, the reflection map is the
identity. -/
lemma evenReflectFun_eq_self_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    evenReflectFun n y = y := by
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [evenReflectFun_apply_zero]
    have : (0 : ℝ) ≤ y 0 := hy
    exact abs_of_nonneg this
  · exact evenReflectFun_apply_ne y j hj

/-- The reflection map is idempotent: applying it twice has no effect. -/
lemma evenReflectFun_idempotent {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectFun n (evenReflectFun n y) = evenReflectFun n y := by
  exact evenReflectFun_eq_self_of_mem_closedHalfSpace
    (evenReflectFun_mem_closedHalfSpace y)

/-- The reflection map sends all of `EuN` into the closed half-space. -/
lemma evenReflectFun_image_univ_subset_closedHalfSpace {n : ℕ} [NeZero n] :
    Set.range (evenReflectFun n) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  rintro y ⟨z, rfl⟩
  exact evenReflectFun_mem_closedHalfSpace z

/-- The image of the closed half-space under the reflection map equals the
closed half-space. -/
lemma evenReflectFun_image_closedHalfSpace_eq {n : ℕ} [NeZero n] :
    evenReflectFun n ''
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, _, rfl⟩
    exact evenReflectFun_mem_closedHalfSpace z
  · intro hy
    refine ⟨y, hy, ?_⟩
    exact evenReflectFun_eq_self_of_mem_closedHalfSpace hy

/-- The reflection map is continuous. -/
lemma continuous_evenReflectFun {n : ℕ} [NeZero n] :
    Continuous (evenReflectFun n) := by
  classical
  -- Decompose: the map is `WithLp.toLp 2` (continuous linear) ∘ a
  -- coordinate-wise function. Each coordinate is continuous in `y`.
  have h_cont_components : ∀ j : Fin n, Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        if j = 0 then |y 0| else y j) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      have h_proj : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => y 0) :=
        PiLp.continuous_apply 2 _ 0
      exact (continuous_abs.comp h_proj).congr (fun y => by simp)
    · have h_proj : Continuous
          (fun y : EuclideanSpace ℝ (Fin n) => y j) :=
        PiLp.continuous_apply 2 _ j
      exact h_proj.congr (fun y => by simp [hj])
  have h_pi_cont : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        fun j : Fin n => if j = 0 then |y 0| else y j) :=
    continuous_pi h_cont_components
  -- The linear map `(Fin n → ℝ) → (EuclideanSpace ℝ (Fin n))` given by
  -- `WithLp.toLp 2` is continuous (continuous linear equivalence on a
  -- finite-dimensional space).
  have hWithLp : Continuous
      (fun g : Fin n → ℝ => (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))) := by
    have h_lin_eq : (fun g : Fin n → ℝ =>
          (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))) =
        ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm :
          (Fin n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n))) := by
      funext g; rfl
    rw [h_lin_eq]
    exact LinearMap.continuous_of_finiteDimensional _
  exact hWithLp.comp h_pi_cont

/-- The reflection map is measurable. -/
lemma measurable_evenReflectFun {n : ℕ} [NeZero n] :
    Measurable (evenReflectFun n) :=
  (continuous_evenReflectFun (n := n)).measurable

/-! ## The even reflection of a scalar function -/

/-- **The even reflection of a scalar function** `f : EuN → ℝ`. Defined by
`evenReflect n f y := f (evenReflectFun n y)`. -/
def evenReflect (n : ℕ) [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => f (evenReflectFun n y)

/-- On the closed half-space, the even reflection equals the original function. -/
lemma evenReflect_eq_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    evenReflect n f y = f y := by
  unfold evenReflect
  rw [evenReflectFun_eq_self_of_mem_closedHalfSpace hy]

/-- The even reflection is continuous when the original function is continuous. -/
lemma continuous_evenReflect {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) :
    Continuous (evenReflect n f) := by
  unfold evenReflect
  exact hf.comp (continuous_evenReflectFun (n := n))

/-- The even reflection is measurable when the original is measurable. -/
lemma measurable_evenReflect {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) :
    Measurable (evenReflect n f) := by
  unfold evenReflect
  exact hf.comp (continuous_evenReflectFun (n := n)).measurable

/-! ## Identity on closed half-space portion of any subset -/

lemma evenReflect_eq_on_inter_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {S : Set (EuclideanSpace ℝ (Fin n))} :
    ∀ y ∈ S ∩ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
      evenReflect n f y = f y := by
  intro y hy
  exact evenReflect_eq_of_mem_closedHalfSpace f hy.2

/-- Norm identity for the reflection. -/
lemma norm_evenReflect_eq {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflect n f y‖ = ‖f (evenReflectFun n y)‖ := rfl

/-- On the closed half-space, `‖evenReflect n f y‖ = ‖f y‖`. -/
lemma norm_evenReflect_eq_norm_self_of_mem_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    ‖evenReflect n f y‖ = ‖f y‖ := by
  rw [evenReflect_eq_of_mem_closedHalfSpace f hy]

/-- The reflection of a function with bounded sup is bounded by the same sup
(on the closed half-space side; off it the values are images of half-space
points so still bounded). -/
lemma norm_evenReflect_le_sup_norm_on_closedHalfSpace {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : ℝ}
    (hfC : ∀ z ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace,
      ‖f z‖ ≤ C) :
    ∀ y : EuclideanSpace ℝ (Fin n), ‖evenReflect n f y‖ ≤ C := by
  intro y
  rw [norm_evenReflect_eq]
  exact hfC _ (evenReflectFun_mem_closedHalfSpace y)

/-! ## Tsupport of the reflection

If `f` has tsupport in the closed half-space portion of a set `S`, then
`evenReflect n f` has tsupport in `evenReflectFun n ⁻¹' S` (under suitable
closedness assumptions). The reflection extends the support symmetrically
across the boundary hyperplane. -/

/-- The support of the even reflection is contained in the preimage under
`evenReflectFun n` of the support of the original function. -/
lemma support_evenReflect_subset {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.support (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' Function.support f := by
  intro y hy
  -- `hy : evenReflect n f y ≠ 0`, i.e. `f (evenReflectFun n y) ≠ 0`.
  exact hy

/-- If `f` has compact support, then `evenReflect n f`'s support is contained
in the preimage of `support f` under the continuous reflection map. The
preimage is closed in `EuN`. -/
lemma tsupport_evenReflect_subset {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f := by
  classical
  have h_supp : Function.support (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' Function.support f := support_evenReflect_subset f
  have h_supp_le_tsupp : evenReflectFun n ⁻¹' Function.support f ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    fun y hy => Set.preimage_mono (subset_tsupport _) hy
  refine Set.Subset.trans (closure_mono (h_supp.trans h_supp_le_tsupp)) ?_
  -- The preimage of a closed set under a continuous map is closed.
  exact (isClosed_tsupport _).preimage continuous_evenReflectFun |>.closure_subset

/-! ## Reflection is its own inverse on the closed half-space (left-inverse) -/

/-- Composing `evenReflectFun n` after `evenReflectFun n` agrees with
`evenReflectFun n` itself (the reflection is idempotent), so in particular
the reflection equals its own composition with itself. -/
lemma evenReflectFun_comp_self {n : ℕ} [NeZero n] :
    evenReflectFun n ∘ evenReflectFun n = evenReflectFun n := by
  funext y
  exact evenReflectFun_idempotent y

/-! ## Sign-flip on the `0`-th coordinate as a measure-preserving equivalence

The map that negates the `0`-th coordinate is a linear isometry equivalence on
`EuclideanSpace ℝ (Fin n)`, hence measure-preserving for the Lebesgue volume.
This is the change-of-variables tool used to compare integrals over the upper
and lower half-balls. -/

/-- **The sign-flip on the `0`-th coordinate.** Negates `y 0`, leaves all other
coordinates unchanged. This is a linear isometry self-equivalence of
`EuclideanSpace ℝ (Fin n)`. -/
def signFlipFun (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    (WithLp.toLp 2 (fun j : Fin n => if j = 0 then -y 0 else y j) :
      EuclideanSpace ℝ (Fin n))

@[simp] lemma signFlipFun_apply_zero {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipFun n y 0 = -y 0 := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then -y 0 else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) 0 = -y 0
  rw [PiLp.toLp_apply]
  simp

@[simp] lemma signFlipFun_apply_ne {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) (hj : j ≠ 0) :
    signFlipFun n y j = y j := by
  classical
  change ((WithLp.toLp 2 (fun k : Fin n => if k = 0 then -y 0 else y k) :
      EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j = y j
  rw [PiLp.toLp_apply]
  simp [if_neg hj]

/-- The sign-flip is its own inverse. -/
@[simp] lemma signFlipFun_signFlipFun {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipFun n (signFlipFun n y) = y := by
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj; simp
  · simp [signFlipFun_apply_ne _ _ hj]

/-- The sign-flip as a linear endomorphism of `EuclideanSpace ℝ (Fin n)`. -/
def signFlipLinear (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := signFlipFun n
  map_add' x y := by
    classical
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [signFlipFun_apply_zero]
      ring
    · simp [signFlipFun_apply_ne _ _ hj]
  map_smul' c x := by
    classical
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [signFlipFun_apply_zero]
    · simp [signFlipFun_apply_ne _ _ hj]

@[simp] lemma signFlipLinear_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipLinear n y = signFlipFun n y := rfl

/-- The sign-flip preserves the Euclidean norm. -/
lemma norm_signFlipFun {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖signFlipFun n y‖ = ‖y‖ := by
  classical
  -- Use the formula ‖x‖ = √(∑ |x_i|²) and the sum coordinate-by-coordinate equality.
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · subst hj
    change ‖signFlipFun n y 0‖ ^ 2 = ‖y 0‖ ^ 2
    rw [signFlipFun_apply_zero]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_neg]
  · change ‖signFlipFun n y j‖ ^ 2 = ‖y j‖ ^ 2
    rw [signFlipFun_apply_ne _ _ hj]

/-- The sign-flip is a linear isometry equivalence. -/
def signFlipLIE (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv :=
    { toFun := signFlipFun n
      map_add' := (signFlipLinear n).map_add'
      map_smul' := (signFlipLinear n).map_smul'
      invFun := signFlipFun n
      left_inv := signFlipFun_signFlipFun
      right_inv := signFlipFun_signFlipFun }
  norm_map' := norm_signFlipFun

@[simp] lemma signFlipLIE_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    signFlipLIE n y = signFlipFun n y := rfl

@[simp] lemma signFlipLIE_symm_apply {n : ℕ} [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) :
    (signFlipLIE n).symm y = signFlipFun n y := rfl

/-- The sign-flip is continuous. -/
lemma continuous_signFlipFun {n : ℕ} [NeZero n] :
    Continuous (signFlipFun n) :=
  (signFlipLIE n).toContinuousLinearEquiv.continuous

/-- The sign-flip is measurable. -/
lemma measurable_signFlipFun {n : ℕ} [NeZero n] :
    Measurable (signFlipFun n) :=
  (continuous_signFlipFun (n := n)).measurable

/-- The sign-flip preserves the Lebesgue volume. -/
lemma measurePreserving_signFlipFun {n : ℕ} [NeZero n] :
    MeasurePreserving (signFlipFun n)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  -- Linear isometry equivalences preserve volume on inner product spaces.
  have h := (signFlipLIE n).measurePreserving
  exact h

/-- The sign-flip swaps the open upper and open lower half-spaces. -/
lemma signFlipFun_image_openHalfSpace_eq {n : ℕ} [NeZero n] :
    signFlipFun n ''
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace =
      {y : EuclideanSpace ℝ (Fin n) | y 0 < 0} := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    change signFlipFun n z 0 < 0
    rw [signFlipFun_apply_zero]
    have : (0 : ℝ) < z 0 := hz
    linarith
  · intro hy
    refine ⟨signFlipFun n y, ?_, signFlipFun_signFlipFun y⟩
    change (0 : ℝ) < signFlipFun n y 0
    rw [signFlipFun_apply_zero]
    have : y 0 < 0 := hy
    linarith

/-- For `y` in the open lower half-space, the even reflection equals `f` of the
sign-flip of `y`. -/
lemma evenReflect_eq_comp_signFlip_of_lower {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0) :
    evenReflect n f y = f (signFlipFun n y) := by
  unfold evenReflect
  congr 1
  classical
  apply PiLp.ext
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
    exact abs_of_neg hy
  · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]

/-- For `y` in the closed upper half-space, the even reflection equals `f`. -/
lemma evenReflect_eq_self_of_upper {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    evenReflect n f y = f y :=
  evenReflect_eq_of_mem_closedHalfSpace f hy

/-! ## L^p bound for the even reflection on a ball -/

/-- **Auxiliary smoothness via composition.** When `f` is smooth on `E` and `y`
is in the open lower half-space, the even reflection equals `f ∘ signFlipFun n`
near `y`, and is smooth there. Stated as a local Continuity result for use in
the global continuity & L^p arguments. -/
lemma continuous_evenReflect_of_continuous {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) :
    Continuous (evenReflect n f) :=
  continuous_evenReflect (n := n) hf

/-- **L^p membership of the even reflection.** When `f` is smooth and has
compact support, the even reflection is also continuous with compact support
contained in the preimage of the support under the reflection map. Hence it
is in `L^p` for any `p`. -/
theorem memLp_evenReflect_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) :
    MemLp (evenReflect n f) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  -- Continuity from continuity of `f` and `evenReflectFun`.
  have h_cont : Continuous (evenReflect n f) :=
    continuous_evenReflect (n := n) hf.continuous
  -- The support is contained in `evenReflectFun ⁻¹' tsupport f`.
  have h_supp_sub : tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    tsupport_evenReflect_subset (n := n) f
  -- The preimage of a compact set under `evenReflectFun n` is contained in a
  -- bounded set (closure of finite product). Better: the support of evenReflect
  -- is `evenReflectFun ⁻¹' (support f)`, hence contained in the union of `tsupport f`
  -- (in the upper half) and `signFlipFun n '' tsupport f` (in the lower half).
  -- Both are compact, so the support of evenReflect is contained in a compact set.
  have h_supp_compact :
      HasCompactSupport (evenReflect n f) := by
    -- The tsupport is contained in tsupport f ∪ signFlipFun n '' tsupport f, both compact.
    apply IsCompact.of_isClosed_subset
      (((hf_supp.image continuous_signFlipFun).union hf_supp))
      (isClosed_tsupport _)
    intro y hy
    have h1 : y ∈ evenReflectFun n ⁻¹' tsupport f := h_supp_sub hy
    -- Either `y 0 ≥ 0` (upper half), in which case `evenReflectFun n y = y` and so `y ∈ tsupport f`,
    -- or `y 0 < 0`, in which case `evenReflectFun n y = signFlipFun n y` and so
    -- `signFlipFun n y ∈ tsupport f`, equivalently `y ∈ signFlipFun n '' tsupport f`.
    rcases le_or_gt 0 (y 0) with hupper | hlower
    · right
      -- y is in tsupport f because evenReflectFun y = y here
      have : evenReflectFun n y = y :=
        evenReflectFun_eq_self_of_mem_closedHalfSpace
          (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
      rw [Set.mem_preimage, this] at h1
      exact h1
    · left
      -- y is in signFlipFun '' tsupport f
      have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
          exact abs_of_neg hlower
        · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
      rw [Set.mem_preimage, h_eq_sf] at h1
      refine ⟨signFlipFun n y, h1, ?_⟩
      exact signFlipFun_signFlipFun y
  -- Now use Continuous.memLp_of_hasCompactSupport.
  exact h_cont.memLp_of_hasCompactSupport h_supp_compact

/-! ## Gradient of the even reflection (component-wise definition)

The natural componentwise even reflection of the gradient: on the upper half,
just the gradient of `f`; on the lower half, the gradient of `f` evaluated at
the reflection point with the `0`-th component sign-flipped.

For `f` smooth and supported in `closedHalfSpace ∩ ball`, this captures the
weak gradient of `evenReflect n f`. -/

/-- The componentwise gradient of `f` at `y`, returning a Euclidean vector. -/
private noncomputable def fderivVec
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => (fderiv ℝ f y) (EuclideanSpace.single i 1))

@[simp] lemma fderivVec_apply
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderivVec f y i = (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
  unfold fderivVec
  rw [PiLp.toLp_apply]

/-- **The even-reflection gradient field.** On the upper half: classical
gradient of `f`. On the lower half: classical gradient of `f` at the reflected
point, with the `0`-th component negated. Defined to agree with the upper-half
formula on the boundary `{y_0 = 0}`. -/
noncomputable def evenReflectGrad (n : ℕ) [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y =>
    if 0 ≤ y 0 then
      fderivVec f y
    else
      WithLp.toLp 2 (fun i : Fin n =>
        if i = 0 then -(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)
        else (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1))

lemma evenReflectGrad_apply_upper
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    evenReflectGrad n f y = fderivVec f y := by
  unfold evenReflectGrad
  rw [if_pos hy]

lemma evenReflectGrad_apply_lower_component_zero
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0) :
    evenReflectGrad n f y 0 = -(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1) := by
  classical
  unfold evenReflectGrad
  rw [if_neg (not_le.mpr hy)]
  rw [PiLp.toLp_apply]
  simp

lemma evenReflectGrad_apply_lower_component_ne
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 < 0)
    {i : Fin n} (hi : i ≠ 0) :
    evenReflectGrad n f y i = (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1) := by
  classical
  unfold evenReflectGrad
  rw [if_neg (not_le.mpr hy)]
  rw [PiLp.toLp_apply]
  simp [if_neg hi]

/-- For `y` in the upper half (i.e. `0 ≤ y 0`), each component of
`evenReflectGrad` is the corresponding partial derivative of `f`. -/
lemma evenReflectGrad_apply_component_upper
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) (i : Fin n) :
    evenReflectGrad n f y i = (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
  rw [evenReflectGrad_apply_upper f hy, fderivVec_apply]

/-! ## L^p bounds for `evenReflectGrad` components

Each component of `evenReflectGrad n f` is in `L^p` when `f` is smooth with
compact support. Strategy: the component is continuous and has compact support,
so it is in `L^p`. -/

/-- For `i ≠ 0`, the `i`-th component of `evenReflectGrad n f` equals
`(fderiv ℝ f) (evenReflectFun n y)` applied to `EuclideanSpace.single i 1` —
because the formulas on the upper and lower halves agree there. -/
lemma evenReflectGrad_apply_component_eq_compReflect_of_ne_zero
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {i : Fin n} (hi : i ≠ 0) (y : EuclideanSpace ℝ (Fin n)) :
    evenReflectGrad n f y i =
      (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1) := by
  classical
  have h_evRefl_lower : ∀ {z : EuclideanSpace ℝ (Fin n)},
      z 0 < 0 → evenReflectFun n z = signFlipFun n z := fun {z} hz => by
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
      exact abs_of_neg hz
    · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
  rcases lt_or_ge (y 0) 0 with hlt | hge
  · rw [evenReflectGrad_apply_lower_component_ne f hlt hi]
    rw [h_evRefl_lower hlt]
  · rw [evenReflectGrad_apply_component_upper f hge i]
    rw [evenReflectFun_eq_self_of_mem_closedHalfSpace hge]

/-- For `i ≠ 0`, the `i`-th component of `evenReflectGrad n f` is continuous
when `f` is smooth. -/
theorem continuous_evenReflectGrad_component_of_contDiff_ne_zero
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {i : Fin n} (hi : i ≠ 0) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) := by
  classical
  have hderiv_cont : Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have h_eq : (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) =
      fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1) := by
    funext y
    exact evenReflectGrad_apply_component_eq_compReflect_of_ne_zero f hi y
  rw [h_eq]
  exact hderiv_cont.comp continuous_evenReflectFun

/-- The `0`-th component of `evenReflectGrad n f` equals
`(Real.sign (y 0)) * (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single 0 1)`
**off the boundary hyperplane** `{y : y 0 = 0}`. On the boundary itself the
formula gives the upper-half value `(fderiv ℝ f y) (EuclideanSpace.single 0 1)`,
which need not be zero — so the component is not continuous in general at
`y_0 = 0`. However, the boundary hyperplane has Lebesgue measure zero, so the
component agrees a.e. with a continuous function. -/
lemma evenReflectGrad_apply_zero_off_boundary
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y 0 ≠ 0) :
    evenReflectGrad n f y 0 =
      (Real.sign (y 0)) *
        (fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single 0 1) := by
  classical
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · rw [evenReflectGrad_apply_lower_component_zero f hlt]
    rw [Real.sign_of_neg hlt]
    have h_evRefl : evenReflectFun n y = signFlipFun n y := by
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlt
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [h_evRefl]
    ring
  · have h_le : (0 : ℝ) ≤ y 0 := le_of_lt hgt
    rw [evenReflectGrad_apply_component_upper f h_le 0]
    have h_evRefl : evenReflectFun n y = y := by
      apply evenReflectFun_eq_self_of_mem_closedHalfSpace h_le
    rw [h_evRefl]
    rw [Real.sign_of_pos hgt]
    ring

/-- The `0`-th component of `evenReflectGrad n f` is bounded pointwise by
`‖fderiv ℝ f (evenReflectFun n y)‖`. -/
lemma norm_evenReflectGrad_apply_zero_le
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflectGrad n f y 0‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ := by
  classical
  rcases lt_or_ge (y 0) 0 with hlt | hge
  · rw [evenReflectGrad_apply_lower_component_zero f hlt]
    have h_evRefl : evenReflectFun n y = signFlipFun n y := by
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlt
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [h_evRefl]
    rw [norm_neg]
    have h_op : ‖(fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)‖ ≤
        ‖fderiv ℝ f (signFlipFun n y)‖ * ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ = 1 := by
      simp
    rw [h_unit, mul_one] at h_op
    exact h_op
  · rw [evenReflectGrad_apply_component_upper f hge 0]
    have h_evRefl : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace hge
    rw [h_evRefl]
    have h_op : ‖(fderiv ℝ f y) (EuclideanSpace.single 0 1)‖ ≤
        ‖fderiv ℝ f y‖ * ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ = 1 := by simp
    rw [h_unit, mul_one] at h_op
    exact h_op

/-- For any `i`, the `i`-th component of `evenReflectGrad n f` is bounded
pointwise by `‖fderiv ℝ f (evenReflectFun n y)‖`. -/
lemma norm_evenReflectGrad_apply_le
    {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖evenReflectGrad n f y i‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ := by
  classical
  by_cases hi : i = 0
  · subst hi
    exact norm_evenReflectGrad_apply_zero_le f y
  · rw [evenReflectGrad_apply_component_eq_compReflect_of_ne_zero f hi y]
    have h_op : ‖(fderiv ℝ f (evenReflectFun n y)) (EuclideanSpace.single i 1)‖ ≤
        ‖fderiv ℝ f (evenReflectFun n y)‖ * ‖(EuclideanSpace.single i (1 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_unit : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
    rw [h_unit, mul_one] at h_op
    exact h_op

/-- The closed half-space `{y : E | 0 ≤ y 0}` is closed, hence measurable. -/
lemma measurableSet_closedHalfSpace_aux {n : ℕ} [NeZero n] :
    MeasurableSet
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
        (d := n)) := by
  classical
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => y 0) :=
    PiLp.continuous_apply 2 _ 0
  have heq : DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
      (d := n) = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' Set.Ici 0 := rfl
  rw [heq]
  exact hcont.measurable measurableSet_Ici

/-- The `i`-th component of `evenReflectGrad n f` is `AEStronglyMeasurable`
when `f` is smooth, on Lebesgue volume. The `i = 0` case uses the fact that
the discontinuity at `y 0 = 0` lives on a Lebesgue-null hyperplane. -/
theorem aestronglyMeasurable_evenReflectGrad_component_of_contDiff
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n) :
    AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  -- Continuity of the partial derivatives of `f`.
  have hderiv_cont : ∀ j : Fin n, Continuous
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single j 1)) := fun j =>
    (hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  by_cases hi : i = 0
  · subst hi
    -- The function is `if 0 ≤ y 0 then (∂_0 f) y else -(∂_0 f) (signFlipFun y)`,
    -- which is the indicator-decomposition of two continuous functions on
    -- the measurable sets `closedHalfSpace` and its complement.
    have h_uppercont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ f y) (EuclideanSpace.single 0 1)) := hderiv_cont 0
    have h_lowercont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1))) :=
      ((hderiv_cont 0).comp continuous_signFlipFun).neg
    have h_eq : (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y 0) =
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
          (d := n)).piecewise
          (fun y => (fderiv ℝ f y) (EuclideanSpace.single 0 1))
          (fun y => -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1))) := by
      funext y
      classical
      by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace
        (d := n)
      · rw [Set.piecewise_eq_of_mem _ _ _ hy]
        rw [evenReflectGrad_apply_component_upper f hy 0]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
        have hlt : y 0 < 0 := lt_of_not_ge (fun h => hy h)
        rw [evenReflectGrad_apply_lower_component_zero f hlt]
    rw [h_eq]
    refine AEStronglyMeasurable.piecewise (μ := volume)
      measurableSet_closedHalfSpace_aux ?_ ?_
    · exact h_uppercont.aestronglyMeasurable.restrict
    · exact h_lowercont.aestronglyMeasurable.restrict
  · exact (continuous_evenReflectGrad_component_of_contDiff_ne_zero hf hi).aestronglyMeasurable

/-! ## L^p bounds for the gradient components

Each component of `evenReflectGrad n f` is in `L^p(volume)` when `f` is smooth
with compact support, because the component is bounded pointwise by
`‖fderiv ℝ f (evenReflectFun n y)‖`, which itself is continuous and has compact
support. -/

/-- The map `y ↦ ‖fderiv ℝ f (evenReflectFun n y)‖` is continuous when `f` is
smooth. -/
lemma continuous_norm_fderiv_compReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f (evenReflectFun n y)‖) := by
  have h_cont_fderiv : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  exact (h_cont_fderiv.comp continuous_evenReflectFun).norm

/-- The map `y ↦ ‖fderiv ℝ f (evenReflectFun n y)‖` has compact support when
`f` has compact support. The support is contained in
`evenReflectFun n ⁻¹' tsupport f`. -/
lemma hasCompactSupport_norm_fderiv_compReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : HasCompactSupport f) :
    HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f (evenReflectFun n y)‖) := by
  classical
  -- The map ‖fderiv f (evenReflectFun y)‖ has support contained in
  -- evenReflectFun ⁻¹' (tsupport (fderiv f)) ⊆ evenReflectFun ⁻¹' (tsupport f).
  have h_fderiv_supp : HasCompactSupport (fderiv ℝ f) :=
    hf_supp.fderiv ℝ
  -- The support of ‖fderiv f ∘ evenReflectFun‖ is contained in:
  -- evenReflectFun ⁻¹' (support (fderiv f)) ⊆ evenReflectFun ⁻¹' (tsupport (fderiv f))
  -- ⊆ evenReflectFun ⁻¹' (tsupport f).
  -- Both `tsupport f` and `signFlipFun '' tsupport f` are compact. Their union
  -- is closed and contains evenReflectFun ⁻¹' (tsupport f).
  have h_compact_union :
      IsCompact (signFlipFun n '' tsupport f ∪ tsupport f) :=
    (hf_supp.image continuous_signFlipFun).union hf_supp
  apply IsCompact.of_isClosed_subset h_compact_union
    (isClosed_tsupport _)
  intro y hy
  -- We have `y ∈ tsupport (‖fderiv f ∘ evenReflectFun‖)`.
  -- This means `evenReflectFun y ∈ tsupport (fderiv f)`.
  have h_supp_pre : Function.support
      (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆
      evenReflectFun n ⁻¹' Function.support (fderiv ℝ f) := by
    intro z hz
    simp only [Function.mem_support, ne_eq, norm_eq_zero] at hz
    exact hz
  have h_pre_subset_t : evenReflectFun n ⁻¹' Function.support (fderiv ℝ f) ⊆
      evenReflectFun n ⁻¹' tsupport (fderiv ℝ f) :=
    Set.preimage_mono (subset_tsupport _)
  have h_pre_subset_t_f : evenReflectFun n ⁻¹' tsupport (fderiv ℝ f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    Set.preimage_mono (tsupport_fderiv_subset (𝕜 := ℝ))
  -- The closure of the support is the tsupport: a closed superset of the support.
  -- Since the closure of `evenReflectFun ⁻¹' tsupport f` equals itself
  -- (because preimage of closed under continuous is closed), we conclude.
  have h_closed : IsClosed (evenReflectFun n ⁻¹' tsupport f) :=
    (isClosed_tsupport _).preimage continuous_evenReflectFun
  have h_y_in : y ∈ evenReflectFun n ⁻¹' tsupport f := by
    have h_subset : tsupport (fun y : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆ evenReflectFun n ⁻¹' tsupport f := by
      have h1 : Function.support
          (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f (evenReflectFun n y)‖) ⊆
          evenReflectFun n ⁻¹' tsupport f :=
        h_supp_pre.trans (h_pre_subset_t.trans h_pre_subset_t_f)
      exact h_closed.closure_subset_iff.mpr h1
    exact h_subset hy
  -- Now `evenReflectFun n y ∈ tsupport f`. Decompose by upper/lower:
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · right
    have h_eq_self : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace
        (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
    rw [Set.mem_preimage, h_eq_self] at h_y_in
    exact h_y_in
  · left
    have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
      classical
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlower
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [Set.mem_preimage, h_eq_sf] at h_y_in
    refine ⟨signFlipFun n y, h_y_in, ?_⟩
    exact signFlipFun_signFlipFun y

/-- For each `i : Fin n`, the `i`-th component of `evenReflectGrad n f` is in
`L^p(volume)` when `f` is smooth with compact support. -/
theorem memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) (i : Fin n) :
    MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  -- Bound by the continuous compactly-supported `‖fderiv f ∘ evenReflectFun‖`.
  have h_aesm : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aestronglyMeasurable_evenReflectGrad_component_of_contDiff hf i
  -- Build the reference function and show it's MemLp.
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ‖fderiv ℝ f (evenReflectFun n y)‖ with hg_def
  have h_g_cont : Continuous g := continuous_norm_fderiv_compReflect hf
  have h_g_supp : HasCompactSupport g :=
    hasCompactSupport_norm_fderiv_compReflect hf hf_supp
  have h_g_memLp : MemLp g p (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    h_g_cont.memLp_of_hasCompactSupport h_g_supp
  -- Use the pointwise bound `‖evenReflectGrad y i‖ ≤ g y` and apply MemLp.of_le_mul.
  refine MemLp.of_le_mul (g := g) (c := 1) h_g_memLp h_aesm ?_
  filter_upwards
  intro y
  rw [one_mul]
  -- ‖evenReflectGrad y i‖ ≤ ‖fderiv f (evenReflectFun y)‖ = g y ≤ ‖g y‖
  have h1 : ‖evenReflectGrad n f y i‖ ≤ ‖fderiv ℝ f (evenReflectFun n y)‖ :=
    norm_evenReflectGrad_apply_le f y i
  have h2 : ‖fderiv ℝ f (evenReflectFun n y)‖ ≤ ‖g y‖ := by
    rw [hg_def]
    exact Real.le_norm_self _
  exact h1.trans h2

/-! ## L^p bound for the gradient (Euclidean-vector form)

The gradient field `evenReflectGrad n f : E → E` itself is in `L^p(volume)`,
with norm bounded by a constant times the `L^p` norm of `‖fderiv f‖` on the
half-space. -/

/-- The gradient field `evenReflectGrad n f` is in `MemLp p volume` when `f`
is smooth with compact support. -/
theorem memLp_evenReflectGrad_of_contDiff_hasCompactSupport
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_supp : HasCompactSupport f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MemLp (evenReflectGrad n f) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  -- A piLp-valued function is MemLp iff each component is.
  apply MemLp.of_eval_piLp
  intro i
  -- Component is `fun y => evenReflectGrad n f y i`, by definition of EuclideanSpace.
  exact memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf hf_supp p i

/-! ## Smoothness of `evenReflect f` when `f` is supported in the open half-space

Under the strict-interior hypothesis `tsupport f ⊆ openHalfSpace`, the even
reflection equals `f + f ∘ signFlipFun n` (a smooth function on all of `E`),
because the supports of these two terms are disjoint open-upper / open-lower
half-spaces. -/

/-- **Smoothness of `signFlipFun n`.** The sign-flip is a continuous linear
self-equivalence of `EuclideanSpace ℝ (Fin n)`, hence smooth. -/
lemma contDiff_signFlipFun {n : ℕ} [NeZero n] {k : WithTop ℕ∞} :
    ContDiff ℝ k (signFlipFun n) :=
  (signFlipLIE n).toContinuousLinearEquiv.contDiff

/-- **Smoothness of `f ∘ signFlipFun n`** when `f` is smooth. -/
lemma contDiff_comp_signFlipFun {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin n) => f (signFlipFun n y)) :=
  hf.comp contDiff_signFlipFun

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection
agrees pointwise with `f + f ∘ signFlipFun n`. -/
lemma evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace) :
    evenReflect n f =
      fun y : EuclideanSpace ℝ (Fin n) => f y + f (signFlipFun n y) := by
  funext y
  classical
  -- Case analysis on `y 0`:
  rcases lt_trichotomy (y 0) 0 with hlt | heq | hgt
  · -- `y_0 < 0`: y is outside upper half-space (and outside tsupport since tsupport ⊆ openHalfSpace)
    have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_y_zero : f y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_supp
    -- evenReflect f y = f (sf y)
    rw [evenReflect_eq_comp_signFlip_of_lower f hlt]
    rw [h_y_zero, zero_add]
  · -- y_0 = 0: y is outside tsupport, also signFlipFun y is at y_0 = 0 which is also outside tsupport
    have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_y_zero : f y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_supp
    -- signFlipFun y has 0-th component -y_0 = 0 too, so also not in tsupport
    have h_sfy_zero : f (signFlipFun n y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hin
      have : signFlipFun n y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      have : (0 : ℝ) < -y 0 := hopen
      linarith
    -- evenReflect f y at y_0 = 0 equals f y (since y is in closed half-space)
    have h_y_in_closed :
        y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
      le_of_eq heq.symm
    rw [evenReflect_eq_self_of_upper f h_y_in_closed]
    rw [h_y_zero, h_sfy_zero, add_zero]
  · -- y_0 > 0: y is potentially in tsupport, signFlipFun y is in lower half so outside tsupport
    have h_y_in_closed :
        y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
      le_of_lt hgt
    rw [evenReflect_eq_self_of_upper f h_y_in_closed]
    -- signFlipFun y has y_0 < 0, so signFlipFun y ∉ openHalfSpace ⊇ tsupport f
    have h_sfy_not_supp : signFlipFun n y ∉ tsupport f := by
      intro hin
      have : signFlipFun n y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      have : (0 : ℝ) < -y 0 := hopen
      linarith
    have h_sfy_zero : f (signFlipFun n y) = 0 :=
      image_eq_zero_of_notMem_tsupport h_sfy_not_supp
    rw [h_sfy_zero, add_zero]

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection is
`C^∞` on all of `E`. -/
theorem contDiff_evenReflect_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n] {k : WithTop ℕ∞}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ k f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace) :
    ContDiff ℝ k (evenReflect n f) := by
  rw [evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace hf_supp]
  exact hf.add (contDiff_comp_signFlipFun hf)

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the even reflection has
compact support contained in `tsupport f ∪ signFlipFun n '' tsupport f`. -/
theorem hasCompactSupport_evenReflect_of_tsupport_in_openHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp_compact : HasCompactSupport f) :
    HasCompactSupport (evenReflect n f) := by
  classical
  -- The tsupport is contained in evenReflectFun ⁻¹' tsupport f, and that is
  -- contained in tsupport f ∪ signFlipFun '' tsupport f, both compact.
  have h_compact_union :
      IsCompact (signFlipFun n '' tsupport f ∪ tsupport f) :=
    (hf_supp_compact.image continuous_signFlipFun).union hf_supp_compact
  apply IsCompact.of_isClosed_subset h_compact_union
    (isClosed_tsupport _)
  have h_supp_sub : tsupport (evenReflect n f) ⊆
      evenReflectFun n ⁻¹' tsupport f :=
    tsupport_evenReflect_subset (n := n) f
  intro y hy
  have h1 : y ∈ evenReflectFun n ⁻¹' tsupport f := h_supp_sub hy
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · right
    have h_eq_self : evenReflectFun n y = y :=
      evenReflectFun_eq_self_of_mem_closedHalfSpace
        (show y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace from hupper)
    rw [Set.mem_preimage, h_eq_self] at h1
    exact h1
  · left
    have h_eq_sf : evenReflectFun n y = signFlipFun n y := by
      classical
      apply PiLp.ext
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [evenReflectFun_apply_zero, signFlipFun_apply_zero]
        exact abs_of_neg hlower
      · rw [evenReflectFun_apply_ne _ _ hj, signFlipFun_apply_ne _ _ hj]
    rw [Set.mem_preimage, h_eq_sf] at h1
    refine ⟨signFlipFun n y, h1, ?_⟩
    exact signFlipFun_signFlipFun y

/-! ## Classical-vs-component identification of `evenReflectGrad`

For `f` smooth with `tsupport f ⊆ openHalfSpace`, we have
`evenReflect n f = f + f ∘ signFlipFun n`. Its classical Fréchet derivative
agrees component-wise with `evenReflectGrad n f`. -/

/-- For `f` smooth with `tsupport f ⊆ openHalfSpace`, the partial derivative
in coordinate `i` of `evenReflect n f` matches the `i`-th component of
`evenReflectGrad n f`. -/
theorem fderiv_evenReflect_apply_single_eq_evenReflectGrad
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1) =
      evenReflectGrad n f y i := by
  classical
  -- Use the rewrite `evenReflect n f = f + f ∘ signFlipFun`.
  have h_eq : evenReflect n f =
      fun z : EuclideanSpace ℝ (Fin n) => f z + f (signFlipFun n z) :=
    evenReflect_eq_add_comp_signFlip_of_tsupport_in_openHalfSpace hf_supp
  -- fderiv of a sum: fderiv f y + fderiv (f ∘ signFlipFun) y
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) :=
    contDiff_comp_signFlipFun hf
  have hg_diff : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) :=
    hg.differentiable (by simp)
  rw [h_eq]
  rw [fderiv_fun_add hf_diff.differentiableAt hg_diff.differentiableAt]
  rw [ContinuousLinearMap.add_apply]
  -- Compute fderiv of `fun z => f (signFlipFun n z)` via chain rule.
  -- Use the fact that `signFlipFun n = (signFlipLIE n).toContinuousLinearEquiv` as a function.
  -- We use the key identity:
  --   fderiv ℝ (f ∘ iso) y = (fderiv ℝ f (iso y)).comp (iso : E →L[ℝ] F)
  -- where `iso = (signFlipLIE n).toContinuousLinearEquiv`.
  set iso : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (signFlipLIE n).toContinuousLinearEquiv with hiso_def
  have h_iso_apply : ∀ z, (iso : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) z = signFlipFun n z := by
    intro z; rfl
  have h_fderiv_comp_eq : (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z))
      = f ∘ iso := by
    funext z
    simp [h_iso_apply]
  have h_fderiv_comp : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin n) => f (signFlipFun n z)) y =
      (fderiv ℝ f (signFlipFun n y)).comp
        (iso : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [h_fderiv_comp_eq]
    have h := iso.comp_right_fderiv (f := f) (x := y)
    -- Replace `iso y` with `signFlipFun n y` using `h_iso_apply`.
    rw [h_iso_apply] at h
    exact h
  rw [h_fderiv_comp]
  -- Goal: (fderiv f y) (e_i) + (fderiv f (sf y)) ∘ iso (e_i) = evenReflectGrad y i
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Compute `iso (single i 1) = signFlipFun n (single i 1)`.
  have h_clm_eval :
      (iso : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single i 1) = signFlipFun n (EuclideanSpace.single i 1) :=
    h_iso_apply _
  rw [h_clm_eval]
  -- Now we need to relate everything to `evenReflectGrad`.
  -- Case-split on whether `y_0 ≥ 0`.
  rcases le_or_gt 0 (y 0) with hupper | hlower
  · -- Upper case: f(sf y) = 0 and its derivatives vanish in a neighborhood.
    -- We need to show: (fderiv f y)(e_i) + (fderiv f (sf y))(sf(e_i)) = evenReflectGrad y i
    -- Since `tsupport f ⊆ openHalfSpace`, f vanishes near `{y_0 ≤ 0}`. So if y_0 ≥ 0...
    -- Actually we need more care: y could be in upper half but inside tsupport.
    -- Then sf y has y_0 ≤ 0, so sf y ∉ tsupport, so f vanishes in a neighborhood of sf y, so fderiv f (sf y) = 0.
    have h_sfy_not_supp : signFlipFun n y ∉ tsupport f := by
      intro hin
      have : signFlipFun n y ∈
          DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have hopen : (0 : ℝ) < signFlipFun n y 0 := this
      rw [signFlipFun_apply_zero] at hopen
      linarith
    have h_fderiv_sfy_zero : fderiv ℝ f (signFlipFun n y) = 0 := by
      have h_eventually : ∀ᶠ z in nhds (signFlipFun n y), f z = 0 := by
        rw [eventually_iff_exists_mem]
        exact ⟨(tsupport f)ᶜ,
          (isClosed_tsupport f).isOpen_compl.mem_nhds h_sfy_not_supp,
          fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
      have h_filt_eq : f =ᶠ[nhds (signFlipFun n y)] 0 := h_eventually
      rw [Filter.EventuallyEq.fderiv_eq h_filt_eq]
      simp
    rw [h_fderiv_sfy_zero, ContinuousLinearMap.zero_apply, add_zero]
    rw [evenReflectGrad_apply_component_upper f hupper i]
  · -- Lower case: y is in lower half, so f y = 0 and its derivative vanishes in a nbhd.
    have h_y_not_supp : y ∉ tsupport f := by
      intro hin
      have : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := hf_supp hin
      have : (0 : ℝ) < y 0 := this
      linarith
    have h_fderiv_y_zero : fderiv ℝ f y = 0 := by
      have h_eventually : ∀ᶠ z in nhds y, f z = 0 := by
        rw [eventually_iff_exists_mem]
        exact ⟨(tsupport f)ᶜ,
          (isClosed_tsupport f).isOpen_compl.mem_nhds h_y_not_supp,
          fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
      have h_filt_eq : f =ᶠ[nhds y] 0 := h_eventually
      rw [Filter.EventuallyEq.fderiv_eq h_filt_eq]
      simp
    rw [h_fderiv_y_zero, ContinuousLinearMap.zero_apply, zero_add]
    -- Goal: (fderiv f (sf y))(sf(single i 1)) = evenReflectGrad y i
    -- For y in lower half with y_0 < 0: evenReflectGrad y i is given by the
    -- lower-half formula with sign flip on i = 0.
    by_cases hi : i = 0
    · subst hi
      rw [evenReflectGrad_apply_lower_component_zero f hlower]
      -- (fderiv f (sf y))(sf(single 0 1)) = -(fderiv f (sf y))(single 0 1)
      -- Because sf(single 0 1) = -single 0 1 (sf negates 0-th coordinate, single 0 1 has 0-th coord = 1)
      have h_sf_eval : signFlipFun n (EuclideanSpace.single 0 (1 : ℝ)) =
          -EuclideanSpace.single 0 (1 : ℝ) := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [signFlipFun_apply_zero]
          rw [PiLp.neg_apply]
        · rw [signFlipFun_apply_ne _ _ hj]
          have h_single_zero : (EuclideanSpace.single 0 (1 : ℝ)) j = 0 := by
            rw [show EuclideanSpace.single 0 (1 : ℝ) = PiLp.single 2 (0 : Fin n) (1 : ℝ) from rfl,
              PiLp.single_apply]
            simp [hj]
          rw [h_single_zero, PiLp.neg_apply, h_single_zero]
          simp
      rw [h_sf_eval]
      rw [map_neg]
    · rw [evenReflectGrad_apply_lower_component_ne f hlower hi]
      -- (fderiv f (sf y))(sf(single i 1)) = (fderiv f (sf y))(single i 1)
      -- Because sf(single i 1) = single i 1 when i ≠ 0.
      have h_sf_eval : signFlipFun n (EuclideanSpace.single i (1 : ℝ)) =
          EuclideanSpace.single i (1 : ℝ) := by
        classical
        apply PiLp.ext
        intro j
        by_cases hj : j = 0
        · subst hj
          rw [signFlipFun_apply_zero]
          -- Need: -((EuclideanSpace.single i (1 : ℝ)) 0) = (EuclideanSpace.single i (1 : ℝ)) 0
          -- Since i ≠ 0, (single i 1) 0 = 0, so -0 = 0.
          have hi' : i ≠ 0 := hi
          rw [show (EuclideanSpace.single i (1 : ℝ)) 0 = 0 by
            rw [show EuclideanSpace.single i (1 : ℝ) = PiLp.single 2 i (1 : ℝ) from rfl,
              PiLp.single_apply]
            simp [hi'.symm]]
          simp
        · rw [signFlipFun_apply_ne _ _ hj]
      rw [h_sf_eval]

/-! ## HasWeakGrad: `evenReflectGrad` is the weak gradient of `evenReflect f`

When `f` is smooth with `tsupport f ⊆ openHalfSpace`, the even reflection is
itself smooth, so its weak gradient equals its classical gradient, which by
the previous lemma agrees component-wise with `evenReflectGrad`. -/

/-- **HasWeakGrad for the even reflection.** When `f` is smooth with
`tsupport f ⊆ openHalfSpace ∩ Ω` (`Ω` open), the even reflection has
`evenReflectGrad n f` as its weak gradient on `Ω`. -/
theorem hasWeakGrad_evenReflectGrad_evenReflect
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    DeGiorgi.HasWeakGrad (evenReflectGrad n f) (evenReflect n f) Ω := by
  -- evenReflect n f is C∞ globally; apply HasWeakPartialDeriv.of_contDiff.
  intro i
  have h_evRefl_smooth : ContDiff ℝ (⊤ : ℕ∞) (evenReflect n f) :=
    contDiff_evenReflect_of_tsupport_in_openHalfSpace hf hf_supp
  -- The classical-derivative weak partial: ∂_i (evenReflect f) = (fderiv (evenReflect f)) (single i 1)
  have h_classical : DeGiorgi.HasWeakPartialDeriv i
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1))
      (evenReflect n f) Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ (h_evRefl_smooth.of_le (by norm_cast))
  -- Show that this equals the i-th component of evenReflectGrad pointwise.
  have h_eq : (fun y : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (evenReflect n f) y) (EuclideanSpace.single i 1)) =
      fun y => evenReflectGrad n f y i := by
    funext y
    exact fderiv_evenReflect_apply_single_eq_evenReflectGrad hf hf_supp y i
  rw [← h_eq]
  exact h_classical

/-! ## The MemW1pWitness for the even reflection (special case)

When `f` is smooth with `tsupport f ⊆ openHalfSpace ∩ Metric.ball x₀ R`, the
even reflection has a `MemW1pWitness` on `Metric.ball x₀ R` with the
canonical gradient `evenReflectGrad n f`. -/

/-- **Even-reflection W^{1,p}-witness construction (strict-interior case).**
For a smooth function `f` on `E := EuclideanSpace ℝ (Fin n)` (n ≥ 1) supported
in the open half-ball `openHalfSpace ∩ Metric.ball x₀ R` (where `x₀` is any
point in `closedHalfSpace`), the even reflection `evenReflect f` admits a
`MemW1pWitness` on `Metric.ball x₀ R`.

This is the strict version where `f` vanishes in a neighborhood of the
boundary hyperplane `{y_0 = 0}`, which makes the reflection itself globally
smooth. The general version (with `closedHalfSpace` instead of `openHalfSpace`)
is the natural extension via density and IBP across the boundary. -/
noncomputable def evenReflect_memW1pWitness_of_smooth_strictInterior
    {n : ℕ} [NeZero n]
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (_hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace ∩
          Metric.ball x₀ R)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    DeGiorgi.MemW1pWitness p (evenReflect (n := n) f) (Metric.ball x₀ R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  -- Extract the open-half-space inclusion.
  have hf_supp_open :
      tsupport f ⊆ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace :=
    hf_supp.trans Set.inter_subset_left
  -- Compactness of tsupport f follows from inclusion in tsupport-of-Ball compact.
  have hf_compact : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ R)
    intro x hx
    have h_x_not_in_ball : x ∉ Metric.ball x₀ R := by
      intro hx_in
      exact hx (Metric.ball_subset_closedBall hx_in)
    -- x not in tsupport
    apply image_eq_zero_of_notMem_tsupport
    intro h_x_in_tsupp
    exact h_x_not_in_ball ((hf_supp h_x_in_tsupp).2)
  refine
    { memLp := ?_
      weakGrad := evenReflectGrad n f
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · -- L^p membership of `evenReflect n f` on `Metric.ball x₀ R`.
    have h_full : MemLp (evenReflect n f) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflect_of_contDiff_hasCompactSupport hf_smooth hf_compact p
    exact h_full.restrict (Metric.ball x₀ R)
  · -- L^p of each component on the ball.
    intro i
    have h_full : MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf_smooth hf_compact p i
    exact h_full.restrict (Metric.ball x₀ R)
  · -- IBP via classical smoothness.
    exact hasWeakGrad_evenReflectGrad_evenReflect hf_smooth hf_supp_open Metric.isOpen_ball

/-! ## Inward-shifted family for the closed-half-space case

The closed-half-space case (where `tsupport f ⊆ closedHalfSpace`, allowing
`f` to be nonzero on the boundary hyperplane `{y_0 = 0}`) is reduced to the
strict-interior case by an inward shift: define `f_δ(y) := f(y - δ · e_0)` for
`δ > 0`. Then `tsupport f_δ ⊆ {y_0 ≥ δ} ⊆ openHalfSpace`, and `f_δ` is the
strict-interior approximation of `f`. As `δ → 0⁺`, both `evenReflect f_δ →
evenReflect f` and the corresponding gradient components converge pointwise
on the complement of the boundary hyperplane (a Lebesgue-null set), with
uniform bounds. This passes the integration-by-parts identity from the
strict-interior case to the limit. -/

/-- **The basis vector `e_0`** in `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def basisE0 (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single (0 : Fin n) (1 : ℝ)

@[simp] lemma basisE0_apply_zero {n : ℕ} [NeZero n] :
    (basisE0 n) 0 = 1 := by
  unfold basisE0
  rw [PiLp.single_apply]
  simp

@[simp] lemma basisE0_apply_ne {n : ℕ} [NeZero n] {j : Fin n} (hj : j ≠ 0) :
    (basisE0 n) j = 0 := by
  unfold basisE0
  rw [PiLp.single_apply]
  simp [hj]

lemma norm_basisE0 {n : ℕ} [NeZero n] : ‖basisE0 n‖ = 1 := by
  unfold basisE0
  simp

/-- **The smooth inward shift** `y ↦ y - δ · e_0`. -/
private noncomputable def shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y => y - δ • basisE0 n

@[simp] lemma shiftDownE0_apply_zero {n : ℕ} [NeZero n]
    (δ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    (shiftDownE0 δ y) 0 = y 0 - δ := by
  unfold shiftDownE0
  rw [PiLp.sub_apply, PiLp.smul_apply, basisE0_apply_zero, smul_eq_mul, mul_one]

@[simp] lemma shiftDownE0_apply_ne {n : ℕ} [NeZero n]
    (δ : ℝ) (y : EuclideanSpace ℝ (Fin n)) {j : Fin n} (hj : j ≠ 0) :
    (shiftDownE0 δ y) j = y j := by
  unfold shiftDownE0
  rw [PiLp.sub_apply, PiLp.smul_apply, basisE0_apply_ne hj, smul_eq_mul, mul_zero,
    sub_zero]

lemma contDiff_shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (shiftDownE0 (n := n) δ) := by
  unfold shiftDownE0
  exact contDiff_id.sub contDiff_const

lemma fderiv_shiftDownE0 {n : ℕ} [NeZero n] (δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (shiftDownE0 (n := n) δ) y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  unfold shiftDownE0
  rw [fderiv_sub_const, fderiv_id']

/-- The shifted function `f_δ(y) := f(y - δ · e_0)`. -/
private noncomputable def shiftDownFun {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => f (shiftDownE0 δ y)

lemma contDiff_shiftDownFun {n : ℕ} [NeZero n] (δ : ℝ) {k : WithTop ℕ∞}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (shiftDownFun (n := n) δ f) :=
  hf.comp (contDiff_shiftDownE0 (n := n) δ)

/-- The chain rule for the shifted function: `∂_i (shiftDownFun δ f) y =
∂_i f (y - δ · e_0)`. -/
lemma fderiv_shiftDownFun_apply
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (fderiv ℝ (shiftDownFun (n := n) δ f) y) (EuclideanSpace.single i 1) =
      (fderiv ℝ f (shiftDownE0 δ y)) (EuclideanSpace.single i 1) := by
  classical
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg_diff : Differentiable ℝ (shiftDownE0 (n := n) δ) :=
    (contDiff_shiftDownE0 (n := n) (k := (1 : WithTop ℕ∞)) δ).differentiable_one
  have h_fun_eq : shiftDownFun (n := n) δ f = f ∘ shiftDownE0 δ := rfl
  rw [h_fun_eq]
  rw [fderiv_comp y hf_diff.differentiableAt hg_diff.differentiableAt]
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_shiftDownE0]
  simp

/-- The shift `shiftDownE0 δ` packaged as a homeomorphism. -/
private noncomputable def shiftDownE0Homeo {n : ℕ} [NeZero n] (δ : ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := shiftDownE0 (n := n) δ
  invFun := fun y => y + δ • basisE0 n
  left_inv := by intro y; unfold shiftDownE0; simp
  right_inv := by intro y; unfold shiftDownE0; simp
  continuous_toFun :=
    (contDiff_shiftDownE0 (n := n) (k := (0 : WithTop ℕ∞)) δ).continuous
  continuous_invFun := continuous_id.add continuous_const

/-- The function `shiftDownFun δ f` factors through `shiftDownE0Homeo`. -/
private lemma shiftDownFun_eq_comp {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    shiftDownFun (n := n) δ f = f ∘ (shiftDownE0Homeo (n := n) δ) :=
  rfl

/-- The tsupport of `shiftDownFun δ f` is the preimage of `tsupport f` under
the shift. -/
private lemma tsupport_shiftDownFun_eq_preimage {n : ℕ} [NeZero n] (δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (shiftDownFun (n := n) δ f) =
      shiftDownE0 (n := n) δ ⁻¹' tsupport f := by
  classical
  -- support(f ∘ φ) = φ⁻¹(support f) for any φ.
  have h_supp_eq : Function.support (shiftDownFun (n := n) δ f) =
      shiftDownE0 (n := n) δ ⁻¹' Function.support f := by
    ext y
    simp [shiftDownFun, Function.support]
  -- tsupport = closure of support; closure commutes with homeomorphism preimage.
  unfold tsupport
  rw [h_supp_eq]
  -- Homeomorph.preimage_closure: h ⁻¹' closure s = closure (h ⁻¹' s).
  have h_eq := (shiftDownE0Homeo (n := n) δ).preimage_closure (Function.support f)
  exact h_eq.symm

/-- For `δ > 0` and `f` with `tsupport f ⊆ closedHalfSpace`, the shifted
function `f_δ(y) := f(y - δ · e_0)` has `tsupport ⊆ openHalfSpace`. -/
lemma tsupport_shiftDownFun_subset_openHalfSpace
    {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace) :
    tsupport (shiftDownFun (n := n) δ f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
  classical
  rw [tsupport_shiftDownFun_eq_preimage]
  intro y hy
  -- hy : shiftDownE0 δ y ∈ tsupport f
  have h_y_in_closed : shiftDownE0 δ y ∈
      DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
    hf_supp hy
  -- shiftDownE0 δ y 0 = y 0 - δ ≥ 0, so y 0 ≥ δ > 0.
  have h0 : (0 : ℝ) ≤ (shiftDownE0 δ y) 0 := h_y_in_closed
  rw [shiftDownE0_apply_zero] at h0
  change (0 : ℝ) < y 0
  linarith

/-- The shifted function has compact support when `f` does. -/
lemma hasCompactSupport_shiftDownFun
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_compact : HasCompactSupport f) :
    HasCompactSupport (shiftDownFun (n := n) δ f) := by
  classical
  change IsCompact (tsupport _)
  rw [tsupport_shiftDownFun_eq_preimage]
  -- The preimage of a compact set under a homeomorphism is compact.
  -- Using Homeomorph: φ⁻¹ '' S = (φ.symm) '' S in some senses; but easier
  -- to use that compact set ↦ compact set under the symm homeomorphism.
  -- The shift by δ•e_0 is a Homeomorphism, but proving the preimage equals
  -- the image-of-symm via library lemmas requires careful coercion handling.
  -- Direct approach: image of compact set under continuous (inverse) is compact.
  -- Specifically, shiftDownE0 δ ⁻¹' tsupport f = (fun y => y + δ•e_0) '' tsupport f.
  set inv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => y + δ • basisE0 n with hinv_def
  have h_inv_cont : Continuous inv := continuous_id.add continuous_const
  have h_preimage_eq : shiftDownE0 (n := n) δ ⁻¹' tsupport f =
      inv '' tsupport f := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, hinv_def]
    constructor
    · intro hy
      refine ⟨shiftDownE0 (n := n) δ y, hy, ?_⟩
      unfold shiftDownE0
      abel
    · rintro ⟨z, hz, rfl⟩
      have h_simplify : shiftDownE0 (n := n) δ (z + δ • basisE0 n) = z := by
        unfold shiftDownE0
        abel
      rw [h_simplify]
      exact hz
  rw [h_preimage_eq]
  exact hf_compact.image h_inv_cont

/-- For `δ > 0` and `f` smooth with `tsupport f ⊆ closedHalfSpace ∩ B(x₀, R)`,
the shifted function has `tsupport ⊆ openHalfSpace ∩ B(x₀, R + δ)`. -/
lemma tsupport_shiftDownFun_subset_ball
    {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    {x₀ : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ∩
          Metric.ball x₀ R) :
    tsupport (shiftDownFun (n := n) δ f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace ∩
        Metric.ball x₀ (R + δ) := by
  classical
  refine Set.subset_inter ?_ ?_
  · exact tsupport_shiftDownFun_subset_openHalfSpace hδ
      (hf_supp.trans Set.inter_subset_left)
  · -- tsupport (shiftDownFun δ f) ⊆ Metric.ball x₀ (R + δ)
    rw [tsupport_shiftDownFun_eq_preimage]
    intro y hy
    -- hy : shiftDownE0 δ y ∈ tsupport f ⊆ Metric.ball x₀ R
    have h_in_ball : shiftDownE0 δ y ∈ Metric.ball x₀ R := (hf_supp hy).2
    -- ‖shiftDownE0 δ y - x₀‖ < R, want: ‖y - x₀‖ < R + δ.
    rw [Metric.mem_ball] at h_in_ball ⊢
    have h_eq : y - x₀ = (shiftDownE0 δ y - x₀) + δ • basisE0 n := by
      unfold shiftDownE0
      abel
    have hdist_eq : dist y x₀ = ‖y - x₀‖ := dist_eq_norm _ _
    have hdist_eq' : dist (shiftDownE0 δ y) x₀ = ‖shiftDownE0 δ y - x₀‖ :=
      dist_eq_norm _ _
    have h_norm_e0 : ‖δ • basisE0 (n := n)‖ = δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, norm_basisE0, mul_one]
    calc dist y x₀ = ‖y - x₀‖ := hdist_eq
      _ = ‖(shiftDownE0 δ y - x₀) + δ • basisE0 n‖ := by rw [h_eq]
      _ ≤ ‖shiftDownE0 δ y - x₀‖ + ‖δ • basisE0 n‖ := norm_add_le _ _
      _ = dist (shiftDownE0 δ y) x₀ + δ := by rw [hdist_eq', h_norm_e0]
      _ < R + δ := by linarith

/-! ## Pointwise convergence for the inward-shift family -/

/-- Helper: As `δ → 0`, `shiftDownE0 δ z → z` for any fixed `z`. -/
private lemma tendsto_shiftDownE0 {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto (fun δ : ℝ => shiftDownE0 δ z) (nhds 0) (nhds z) := by
  unfold shiftDownE0
  have h_smul_tendsto : Filter.Tendsto (fun δ : ℝ => δ • basisE0 (n := n))
      (nhds 0) (nhds 0) := by
    have h_smul_cont : Continuous (fun s : ℝ => s • basisE0 (n := n)) :=
      continuous_id.smul continuous_const
    have := h_smul_cont.tendsto 0
    simpa [zero_smul] using this
  have h_const_tendsto : Filter.Tendsto (fun _ : ℝ => z) (nhds 0) (nhds z) :=
    tendsto_const_nhds
  have := h_const_tendsto.sub h_smul_tendsto
  simpa using this

/-- **Pointwise convergence of `evenReflect f_δ` to `evenReflect f`** as `δ →
0⁺`. -/
lemma tendsto_evenReflect_shiftDownFun
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (y : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto (fun δ : ℝ => evenReflect n (shiftDownFun (n := n) δ f) y)
      (nhds 0) (nhds (evenReflect n f y)) := by
  classical
  -- evenReflect n (shiftDownFun δ f) y = f (shiftDownE0 δ (evenReflectFun n y)).
  -- As δ → 0, shiftDownE0 δ (evenReflectFun n y) → evenReflectFun n y,
  -- and f is continuous.
  have h_eq :
      ∀ δ : ℝ,
        evenReflect n (shiftDownFun (n := n) δ f) y =
          f (shiftDownE0 δ (evenReflectFun n y)) := by
    intro δ
    unfold evenReflect shiftDownFun
    rfl
  have h_eq_lim :
      evenReflect n f y = f (evenReflectFun n y) := by
    unfold evenReflect; rfl
  simp_rw [h_eq]
  rw [h_eq_lim]
  exact (hf.tendsto _).comp (tendsto_shiftDownE0 (evenReflectFun n y))

/-- Helper: As `δ → 0`, `(fderiv f (shiftDownE0 δ z)) (single i 1) →
(fderiv f z) (single i 1)`. -/
private lemma tendsto_fderiv_apply_shiftDownE0
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Filter.Tendsto (fun δ : ℝ =>
        (fderiv ℝ f (shiftDownE0 δ z)) (EuclideanSpace.single i 1))
      (nhds 0)
      (nhds ((fderiv ℝ f z) (EuclideanSpace.single i 1))) := by
  have h_fderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  -- (L, v) ↦ L v is jointly continuous. Composed with (δ ↦ (fderiv f (shiftDownE0 δ z), single i 1)).
  have h_eval_cont : Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i (1 : ℝ))) :=
    continuous_id.clm_apply continuous_const
  have h_fderiv_tendsto :
      Filter.Tendsto (fun δ : ℝ => fderiv ℝ f (shiftDownE0 δ z))
        (nhds 0) (nhds (fderiv ℝ f z)) :=
    (h_fderiv_cont.tendsto _).comp (tendsto_shiftDownE0 z)
  exact (h_eval_cont.tendsto _).comp h_fderiv_tendsto

/-- **Pointwise convergence of `evenReflectGrad (shiftDownFun δ f) y i` to
`evenReflectGrad f y i`** as `δ → 0⁺`, for `y` off the boundary hyperplane. -/
lemma tendsto_evenReflectGrad_shiftDownFun_off_boundary
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y 0 ≠ 0) (i : Fin n) :
    Filter.Tendsto (fun δ : ℝ =>
        evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
      (nhds 0) (nhds (evenReflectGrad n f y i)) := by
  classical
  -- Decompose by upper/lower half.
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · -- y 0 < 0: lower half.
    by_cases hi : i = 0
    · subst hi
      have h_eq_δ : ∀ δ : ℝ,
          evenReflectGrad n (shiftDownFun (n := n) δ f) y 0 =
            -((fderiv ℝ f
              (shiftDownE0 δ (signFlipFun n y))) (EuclideanSpace.single 0 1)) := by
        intro δ
        rw [evenReflectGrad_apply_lower_component_zero
          (shiftDownFun (n := n) δ f) hlt]
        rw [fderiv_shiftDownFun_apply δ hf (signFlipFun n y) 0]
      have h_eq_lim :
          evenReflectGrad n f y 0 =
            -((fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single 0 1)) := by
        rw [evenReflectGrad_apply_lower_component_zero f hlt]
      rw [h_eq_lim]
      simp_rw [h_eq_δ]
      exact (tendsto_fderiv_apply_shiftDownE0 hf (signFlipFun n y) 0).neg
    · have h_eq_δ : ∀ δ : ℝ,
          evenReflectGrad n (shiftDownFun (n := n) δ f) y i =
            (fderiv ℝ f
              (shiftDownE0 δ (signFlipFun n y))) (EuclideanSpace.single i 1) := by
        intro δ
        rw [evenReflectGrad_apply_lower_component_ne
          (shiftDownFun (n := n) δ f) hlt hi]
        rw [fderiv_shiftDownFun_apply δ hf (signFlipFun n y) i]
      have h_eq_lim :
          evenReflectGrad n f y i =
            (fderiv ℝ f (signFlipFun n y)) (EuclideanSpace.single i 1) := by
        rw [evenReflectGrad_apply_lower_component_ne f hlt hi]
      rw [h_eq_lim]
      simp_rw [h_eq_δ]
      exact tendsto_fderiv_apply_shiftDownE0 hf (signFlipFun n y) i
  · -- y 0 > 0: upper half.
    have h_y_in_closed : (0 : ℝ) ≤ y 0 := le_of_lt hgt
    have h_eq_δ : ∀ δ : ℝ,
        evenReflectGrad n (shiftDownFun (n := n) δ f) y i =
          (fderiv ℝ f (shiftDownE0 δ y)) (EuclideanSpace.single i 1) := by
      intro δ
      rw [evenReflectGrad_apply_component_upper
        (shiftDownFun (n := n) δ f) h_y_in_closed i]
      rw [fderiv_shiftDownFun_apply δ hf y i]
    have h_eq_lim :
        evenReflectGrad n f y i =
          (fderiv ℝ f y) (EuclideanSpace.single i 1) := by
      rw [evenReflectGrad_apply_component_upper f h_y_in_closed i]
    rw [h_eq_lim]
    simp_rw [h_eq_δ]
    exact tendsto_fderiv_apply_shiftDownE0 hf y i

/-- The boundary hyperplane `{y_0 = 0}` is Lebesgue-null. -/
lemma volume_boundaryHyperplane_eq_zero {n : ℕ} [NeZero n] :
    volume
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) :
        Set (EuclideanSpace ℝ (Fin n))) = 0 := by
  classical
  -- The boundary hyperplane is the kernel of the continuous linear map
  -- `y ↦ y 0`. We use `addHaar_submodule`: a strict submodule of a finite-
  -- dimensional inner product space has volume 0.
  let φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun y => y 0
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let H : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.ker φ
  have h_set_eq : (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
      (d := n) : Set (EuclideanSpace ℝ (Fin n))) = (H : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    simp only [DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane_def,
      Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker, H, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
  rw [h_set_eq]
  apply Measure.addHaar_submodule volume H
  -- H ≠ ⊤: e.g., basisE0 has 0-th coord = 1, so it's not in H.
  intro h_top
  have h_basisE0_in : basisE0 (n := n) ∈ H := by
    rw [h_top]; exact Submodule.mem_top
  -- h_basisE0_in unfolds to: φ (basisE0 n) = 0, i.e. (basisE0 n) 0 = 0.
  have h_basisE0_zero : (basisE0 (n := n) : EuclideanSpace ℝ (Fin n)) 0 = 0 := by
    have := h_basisE0_in
    simp only [LinearMap.mem_ker, H, φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this
  rw [basisE0_apply_zero] at h_basisE0_zero
  exact one_ne_zero h_basisE0_zero

/-- **Pointwise convergence of `evenReflectGrad (shiftDownFun δ f) y i` to
`evenReflectGrad f y i`** as `δ → 0⁺` is valid almost everywhere on `volume`. -/
lemma tendsto_evenReflectGrad_shiftDownFun_ae
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin n) :
    ∀ᵐ y : EuclideanSpace ℝ (Fin n) ∂volume,
      Filter.Tendsto (fun δ : ℝ =>
          evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
        (nhds 0) (nhds (evenReflectGrad n f y i)) := by
  classical
  have h_null : volume
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) :
        Set (EuclideanSpace ℝ (Fin n))) = 0 :=
    volume_boundaryHyperplane_eq_zero
  -- For y ∉ boundary hyperplane, y 0 ≠ 0, and we have pointwise convergence.
  have h_outside :
      ∀ y ∈ (DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane
        (d := n) : Set (EuclideanSpace ℝ (Fin n)))ᶜ,
        Filter.Tendsto (fun δ : ℝ =>
            evenReflectGrad n (shiftDownFun (n := n) δ f) y i)
          (nhds 0) (nhds (evenReflectGrad n f y i)) := by
    intro y hy
    have hy_ne : y 0 ≠ 0 := hy
    exact tendsto_evenReflectGrad_shiftDownFun_off_boundary hf y hy_ne i
  -- Convert "∀ y ∉ null set" into "a.e. y".
  rw [Filter.eventually_iff]
  rw [MeasureTheory.mem_ae_iff]
  refine measure_mono_null ?_ h_null
  intro y hy
  -- hy : ¬ Tendsto ... → y ∈ boundaryHyperplane
  by_contra hy_outside
  exact hy (h_outside y hy_outside)

/-! ## Uniform bounds for the inward-shift family -/

/-- **Uniform bound** on `‖evenReflect (shiftDownFun δ f) y‖`. -/
lemma norm_evenReflect_shiftDownFun_le_sup
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hfC : ∀ z : EuclideanSpace ℝ (Fin n), ‖f z‖ ≤ C)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖evenReflect n (shiftDownFun (n := n) δ f) y‖ ≤ C := by
  unfold evenReflect shiftDownFun
  exact hfC _

/-- **Uniform bound** on `‖evenReflectGrad (shiftDownFun δ f) y i‖` by `‖fderiv f‖`
at the appropriate (shifted) point. -/
lemma norm_evenReflectGrad_shiftDownFun_apply_le_sup
    {n : ℕ} [NeZero n] (δ : ℝ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C : ℝ}
    (hfC : ∀ z : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f z‖ ≤ C)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ‖evenReflectGrad n (shiftDownFun (n := n) δ f) y i‖ ≤ C := by
  classical
  have h_bound :=
    norm_evenReflectGrad_apply_le (shiftDownFun (n := n) δ f) y i
  -- h_bound : ‖evenReflectGrad (shiftDownFun δ f) y i‖ ≤
  --              ‖fderiv (shiftDownFun δ f) (evenReflectFun n y)‖
  -- Need: ‖fderiv (shiftDownFun δ f) z‖ ≤ ‖fderiv f (z - δ • e_0)‖ ≤ C.
  -- By chain rule, fderiv (shiftDownFun δ f) z = fderiv f (z - δ•e_0) ∘ id =
  -- fderiv f (z - δ•e_0).
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg_diff : Differentiable ℝ (shiftDownE0 (n := n) δ) :=
    (contDiff_shiftDownE0 (n := n) (k := (1 : WithTop ℕ∞)) δ).differentiable_one
  have h_fderiv_eq :
      fderiv ℝ (shiftDownFun (n := n) δ f) (evenReflectFun n y) =
        fderiv ℝ f (shiftDownE0 δ (evenReflectFun n y)) := by
    have h_fun_eq : shiftDownFun (n := n) δ f = f ∘ shiftDownE0 δ := rfl
    rw [h_fun_eq]
    rw [fderiv_comp _ hf_diff.differentiableAt hg_diff.differentiableAt]
    rw [fderiv_shiftDownE0]
    ext v
    simp
  rw [h_fderiv_eq] at h_bound
  exact h_bound.trans (hfC _)

/-! ## Closed-half-space MemW1pWitness via inward-shift mollification

Combining the previous machinery: take a sequence `δ_n → 0⁺`, get a witness
for each `f_{δ_n}` (strict-interior case), pass to the limit using bounded
convergence on the integration-by-parts identity.

For the closed-half-space tsupport hypothesis, we obtain:
  HasWeakPartialDeriv i (evenReflectGrad f ·_i) (evenReflect f) Ω
on every open `Ω ⊆ ℝ^n`. -/

/-- **HasWeakGrad for the even reflection (closed-half-space case).**
When `f` is smooth with compact support and `tsupport f ⊆ closedHalfSpace`,
the even reflection has `evenReflectGrad n f` as its weak gradient on every
open `Ω`. -/
theorem hasWeakGrad_evenReflectGrad_evenReflect_closedHalfSpace
    {n : ℕ} [NeZero n]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_compact : HasCompactSupport f)
    (hf_supp :
      tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    DeGiorgi.HasWeakGrad (evenReflectGrad n f) (evenReflect n f) Ω := by
  classical
  -- Test against any φ : E → ℝ smooth, compact support, tsupport φ ⊆ Ω.
  intro i φ hφ_smooth hφ_compact hφ_sub
  -- Pick a sequence δ_k := 1/(k+1) → 0⁺.
  set δseq : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ) with hδseq_def
  have hδ_pos : ∀ k, 0 < δseq k := fun k => by
    rw [hδseq_def]; positivity
  have hδ_tendsto : Filter.Tendsto δseq Filter.atTop (nhds (0 : ℝ)) := by
    rw [hδseq_def]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- For each k, get the IBP identity for shiftDownFun (δseq k) f.
  set f_seq : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k => shiftDownFun (n := n) (δseq k) f with hf_seq_def
  have hf_seq_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f_seq k) := by
    intro k; exact contDiff_shiftDownFun (n := n) (δseq k) hf
  have hf_seq_supp_open : ∀ k,
      tsupport (f_seq k) ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace := by
    intro k
    exact tsupport_shiftDownFun_subset_openHalfSpace (hδ_pos k) hf_supp
  -- IBP identity for each k.
  have h_seq_ibp : ∀ k,
      ∫ x in Ω, evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x := by
    intro k
    have h_grad_seq :
        DeGiorgi.HasWeakGrad (evenReflectGrad n (f_seq k))
          (evenReflect n (f_seq k)) Ω :=
      hasWeakGrad_evenReflectGrad_evenReflect (hf_seq_smooth k)
        (hf_seq_supp_open k) hΩ
    exact h_grad_seq i φ hφ_smooth hφ_compact hφ_sub
  -- Continuity & uniform bounds for f and ∇f.
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have h_fderiv_cont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_fderiv_compact : HasCompactSupport (fderiv ℝ f) :=
    hf_compact.fderiv ℝ
  have h_norm_fderiv_cont : Continuous (fun z => ‖fderiv ℝ f z‖) :=
    h_fderiv_cont.norm
  have h_norm_fderiv_compact : HasCompactSupport (fun z => ‖fderiv ℝ f z‖) := by
    apply HasCompactSupport.intro h_fderiv_compact.isCompact
    intro x hx
    have : fderiv ℝ f x = 0 := by
      by_contra h
      exact hx (subset_tsupport _ h)
    rw [this]
    simp
  obtain ⟨C₀, hC₀_bound⟩ : ∃ C₀ : ℝ, ∀ z, ‖f z‖ ≤ C₀ :=
    hf.continuous.bounded_above_of_compact_support hf_compact
  obtain ⟨C₁, hC₁_bound⟩ : ∃ C₁ : ℝ, ∀ z, ‖fderiv ℝ f z‖ ≤ C₁ := by
    obtain ⟨C₁, hC₁⟩ := h_norm_fderiv_cont.bounded_above_of_compact_support h_norm_fderiv_compact
    refine ⟨C₁, fun z => ?_⟩
    have h := hC₁ z
    -- h : ‖‖fderiv ℝ f z‖‖ ≤ C₁; for ℝ, the outer norm is just the abs value
    -- and ‖fderiv f z‖ ≥ 0, so the outer norm is the same value.
    simpa using h
  -- Continuity of `∂_i φ` and `φ`, with compact support.
  have hdφ_cont : Continuous (fun x =>
      (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
    (hφ_smooth.continuous_fderiv
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport (fun x =>
      (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
    hφ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  -- Define the bounding integrable function for LHS:
  -- |evenReflect (f_seq k) · ∂_i φ| ≤ C₀ · ‖∂_i φ‖ ≤ C₀ · |∂_i φ|.
  -- The bound `C₀ * (norm of ∂_i φ)` is integrable on `volume.restrict Ω`.
  -- LHS limit:
  have h_LHS_tendsto :
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        Filter.atTop
        (nhds (∫ x in Ω, evenReflect n f x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
    set bound_LHS : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ with hbound_LHS_def
    have h_bound_LHS_cont : Continuous bound_LHS :=
      continuous_const.mul hdφ_cont.norm
    have h_bound_LHS_supp : HasCompactSupport bound_LHS := by
      apply HasCompactSupport.intro hdφ_compact.isCompact
      intro x hx
      have hx0 : (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
        by_contra h
        exact hx (subset_tsupport _ h)
      change C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ = 0
      rw [hx0]
      simp
    have h_bound_LHS_int : Integrable bound_LHS (volume.restrict Ω) :=
      (h_bound_LHS_cont.integrable_of_hasCompactSupport h_bound_LHS_supp).restrict
    have h_F_meas : ∀ k, AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
      intro k
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_evenReflect (hf_seq_smooth k).continuous).aestronglyMeasurable
      · exact hdφ_cont.aestronglyMeasurable
    have h_F_lim_meas : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          evenReflect n f x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_evenReflect hf.continuous).aestronglyMeasurable
      · exact hdφ_cont.aestronglyMeasurable
    -- Pointwise bound and convergence on volume-a.e. x.
    have h_F_bound : ∀ k, ∀ᵐ x ∂(volume.restrict Ω),
        ‖evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ ≤ bound_LHS x := by
      intro k
      refine Filter.Eventually.of_forall (fun x => ?_)
      change ‖evenReflect n (f_seq k) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ ≤
        C₀ * ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖
      rw [norm_mul]
      have h1 : ‖evenReflect n (f_seq k) x‖ ≤ C₀ :=
        norm_evenReflect_shiftDownFun_le_sup (δseq k) hC₀_bound x
      have h2 : (0 : ℝ) ≤ ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖ :=
        norm_nonneg _
      exact mul_le_mul_of_nonneg_right h1 h2
    have h_F_lim : ∀ᵐ x ∂(volume.restrict Ω),
        Filter.Tendsto (fun k : ℕ =>
            evenReflect n (f_seq k) x *
              (fderiv ℝ φ x) (EuclideanSpace.single i 1))
          Filter.atTop
          (nhds (evenReflect n f x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_evRefl_lim :
          Filter.Tendsto (fun k : ℕ => evenReflect n (f_seq k) x)
            Filter.atTop (nhds (evenReflect n f x)) :=
        (tendsto_evenReflect_shiftDownFun (n := n) hf.continuous x).comp hδ_tendsto
      exact h_evRefl_lim.mul tendsto_const_nhds
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      bound_LHS h_F_meas h_bound_LHS_int h_F_bound h_F_lim
  -- RHS limit:
  have h_RHS_tendsto :
      Filter.Tendsto
        (fun k : ℕ => -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x)
        Filter.atTop
        (nhds (-∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
    have h_inner :
        Filter.Tendsto
          (fun k : ℕ => ∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x)
          Filter.atTop
          (nhds (∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
      set bound_RHS : EuclideanSpace ℝ (Fin n) → ℝ :=
        fun x => C₁ * ‖φ x‖ with hbound_RHS_def
      have h_bound_RHS_cont : Continuous bound_RHS :=
        continuous_const.mul hφ_smooth.continuous.norm
      have h_bound_RHS_supp : HasCompactSupport bound_RHS := by
        apply HasCompactSupport.intro hφ_compact.isCompact
        intro x hx
        have hx0 : φ x = 0 := by
          by_contra h
          exact hx (subset_tsupport _ h)
        change C₁ * ‖φ x‖ = 0
        rw [hx0]
        simp
      have h_bound_RHS_int : Integrable bound_RHS (volume.restrict Ω) :=
        (h_bound_RHS_cont.integrable_of_hasCompactSupport h_bound_RHS_supp).restrict
      have h_G_meas : ∀ k, AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            evenReflectGrad n (f_seq k) x i * φ x) (volume.restrict Ω) := by
        intro k
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact aestronglyMeasurable_evenReflectGrad_component_of_contDiff
            (hf_seq_smooth k) i |>.mono_measure (Measure.restrict_le_self)
        · exact hφ_smooth.continuous.aestronglyMeasurable
      have h_G_bound : ∀ k, ∀ᵐ x ∂(volume.restrict Ω),
          ‖evenReflectGrad n (f_seq k) x i * φ x‖ ≤ bound_RHS x := by
        intro k
        refine Filter.Eventually.of_forall (fun x => ?_)
        change ‖evenReflectGrad n (f_seq k) x i * φ x‖ ≤ C₁ * ‖φ x‖
        rw [norm_mul]
        have h1 : ‖evenReflectGrad n (f_seq k) x i‖ ≤ C₁ :=
          norm_evenReflectGrad_shiftDownFun_apply_le_sup (δseq k) hf hC₁_bound x i
        have h2 : (0 : ℝ) ≤ ‖φ x‖ := norm_nonneg _
        exact mul_le_mul_of_nonneg_right h1 h2
      have h_G_lim : ∀ᵐ x ∂(volume.restrict Ω),
          Filter.Tendsto (fun k : ℕ =>
              evenReflectGrad n (f_seq k) x i * φ x)
            Filter.atTop
            (nhds (evenReflectGrad n f x i * φ x)) := by
        -- Convergence holds for x with x 0 ≠ 0 (a.e.).
        have h_ae : ∀ᵐ x ∂volume,
            Filter.Tendsto (fun k : ℕ => evenReflectGrad n (f_seq k) x i)
              Filter.atTop (nhds (evenReflectGrad n f x i)) :=
          tendsto_evenReflectGrad_shiftDownFun_ae hf i |>.mp
            (Filter.Eventually.of_forall (fun x h_lim_δ =>
              h_lim_δ.comp hδ_tendsto))
        exact (ae_restrict_of_ae h_ae).mono fun x hx => hx.mul tendsto_const_nhds
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        bound_RHS h_G_meas h_bound_RHS_int h_G_bound h_G_lim
    exact h_inner.neg
  -- Combine the limits with the IBP identity for f_seq k.
  have h_lhs_eq_rhs :
      (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
        fun k : ℕ => -∫ x in Ω, evenReflectGrad n (f_seq k) x i * φ x := by
    funext k
    exact h_seq_ibp k
  have h_LHS_eq_lim :
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ x in Ω, evenReflect n (f_seq k) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        Filter.atTop
        (nhds (-∫ x in Ω, evenReflectGrad n f x i * φ x)) := by
    rw [h_lhs_eq_rhs]
    exact h_RHS_tendsto
  exact tendsto_nhds_unique h_LHS_tendsto h_LHS_eq_lim

/-! ## The MemW1pWitness for the even reflection (closed-half-space case)

When `f` is smooth with `tsupport f ⊆ closedHalfSpace ∩ Metric.ball x₀ R`, the
even reflection has a `MemW1pWitness` on `Metric.ball x₀ R`. -/

/-- **Even-reflection W^{1,p}-witness construction (closed-half-space case).**
For a smooth function `f` on `E := EuclideanSpace ℝ (Fin n)` (n ≥ 1) supported
in the closed half-ball `closedHalfSpace ∩ Metric.ball x₀ R`, the even
reflection `evenReflect f` admits a `MemW1pWitness` on `Metric.ball x₀ R`.

Compared to the strict-interior version, this allows `f` to be nonzero at the
boundary hyperplane `{y_0 = 0}`. The proof reduces to the strict-interior case
via an inward shift `f_δ(y) := f(y - δ · e_0)` and bounded convergence on the
integration-by-parts identity. -/
noncomputable def evenReflect_memW1pWitness_of_smooth_closedHalfSpace
    {n : ℕ} [NeZero n]
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (_hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_supp : tsupport f ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace ∩
          Metric.ball x₀ R)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    DeGiorgi.MemW1pWitness p (evenReflect (n := n) f) (Metric.ball x₀ R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  -- Compactness of tsupport f follows from inclusion in closedBall.
  have hf_compact : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_closedBall x₀ R)
    intro x hx
    have h_x_not_in_ball : x ∉ Metric.ball x₀ R := by
      intro hx_in
      exact hx (Metric.ball_subset_closedBall hx_in)
    apply image_eq_zero_of_notMem_tsupport
    intro h_x_in_tsupp
    exact h_x_not_in_ball ((hf_supp h_x_in_tsupp).2)
  have hf_supp_closed :
      tsupport f ⊆ DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace :=
    hf_supp.trans Set.inter_subset_left
  refine
    { memLp := ?_
      weakGrad := evenReflectGrad n f
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · -- L^p membership of `evenReflect n f` on `Metric.ball x₀ R`.
    have h_full : MemLp (evenReflect n f) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflect_of_contDiff_hasCompactSupport hf_smooth hf_compact p
    exact h_full.restrict (Metric.ball x₀ R)
  · -- L^p of each component on the ball.
    intro i
    have h_full : MemLp (fun y : EuclideanSpace ℝ (Fin n) => evenReflectGrad n f y i) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      memLp_evenReflectGrad_component_of_contDiff_hasCompactSupport hf_smooth hf_compact p i
    exact h_full.restrict (Metric.ball x₀ R)
  · -- IBP via inward-shift mollification.
    exact hasWeakGrad_evenReflectGrad_evenReflect_closedHalfSpace
      hf_smooth hf_compact hf_supp_closed Metric.isOpen_ball

/-! ## Headline: with-boundary smooth manifold Morrey sup bound, packaged

We package the headline by re-exporting the existing conditional version
together with the foundational even-reflection layer. The closed-half-space
W^{1,p} witness construction
(`evenReflect_memW1pWitness_of_smooth_closedHalfSpace`) provides an
alternative pathway to the same per-chart bound used by the conditional
manifold theorem; downstream callers may freely choose between either route. -/

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)

/-- **Smooth manifold-level Morrey sup bound, with-boundary case.**

For a closed Riemannian manifold-with-boundary modelled on the canonical
Euclidean half-space `EuclideanHalfSpace n` and `p > n`, every smooth `u : M →
ℝ` whose canonical-POU chart-pushed functions all have `tsupport` strictly
inside the open interior parts of the chart targets satisfies a uniform-in-`u`
sup-norm bound:

  `‖u(x)‖ ≤ C · (wkpNormChart g 1 p u).toReal`.

This is a re-export of `smooth_manifold_morrey_sup_bound_uniform_withBoundary`
from `MorreyManifold.lean`, packaged together with the foundational even-
reflection layer so a single import suffices for downstream callers wanting
both.

When the chart-pushed function takes nonzero values at boundary points
`{y_0 = 0}` of the chart target, the chart-extended function
`chartSmoothExt α (ρ_α · u)` is no longer smooth on `EuN`, so the
boundaryless smooth Morrey cannot be applied directly with that function as
input. The closed-half-space W^{1,p} witness construction
`evenReflect_memW1pWitness_of_smooth_closedHalfSpace` delivered above
provides the corresponding W^{1,p} ingredient: for any smooth `f : EuN → ℝ`
with `tsupport ⊆ closedHalfSpace ∩ Metric.ball x₀ R`, the even reflection
admits a `MemW1pWitness` on the ball, suitable for `morrey_sup_bound`. -/
theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary_unconditional
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (n := n) (M := M) g hp

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
