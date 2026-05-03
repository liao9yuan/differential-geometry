import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ModelBoundary
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Orientation
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# `HasSmoothBoundary` instance for the Euclidean half-space model

This file equips the canonical `n`-dimensional model with corners
`modelWithCornersEuclideanHalfSpace n : ModelWithCorners ℝ
  (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` with the
`HasSmoothBoundary` typeclass, for every `n : ℕ` with `[NeZero n]`.

The construction is concrete and entirely linear:

* The boundary normed model is `EuclideanSpace ℝ (Fin (n - 1))`.
* The boundary topological model is the same `EuclideanSpace ℝ (Fin (n - 1))`,
  treated via the boundaryless model `modelWithCornersSelf ℝ _`.
* The inclusion `inclEuclidean` maps a tuple `x : Fin (n - 1) → ℝ` to the
  tuple `Fin n → ℝ` whose `0`-th coordinate is `0` and whose `i`-th coordinate
  for `i ≠ 0` is the corresponding entry of `x`.
* The projection `projEuclidean` maps a tuple `y : Fin n → ℝ` to the tuple
  `Fin (n - 1) → ℝ` whose `i`-th coordinate is the `(i + 1)`-th coordinate of
  `y`.

These two maps are continuous-linear; the smoothness conditions of
`HasSmoothBoundary` follow at `C^∞`. The range identity
`Set.range (I ∘ inclH) = frontier (Set.range I)` reduces to
`{y : EuclideanSpace ℝ (Fin n) | y 0 = 0}` on both sides, using
`range_euclideanHalfSpace` and `frontier_halfSpace`.

The compatibility identity `projE ∘ I ∘ inclH = boundaryI` collapses to the
identity on `EuclideanSpace ℝ (Fin (n - 1))`, since `boundaryI` is the
self-model.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary
namespace EuclideanHalfSpaceInstance

/-! ## Helper arithmetic on `n - 1` for `[NeZero n]` -/

/-- For a positive natural number, `(n - 1) + 1 = n`. -/
private theorem n_sub_one_add_one (n : ℕ) [NeZero n] : (n - 1) + 1 = n :=
  Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

/-! ## Index-shift maps `Fin (n - 1) → Fin n` -/

/-- Given `[NeZero n]`, the index-shift map sending `j : Fin (n - 1)` to
`Fin n` by adding one (i.e., `j ↦ j.succ` after a length cast). -/
private def succIndex (n : ℕ) [NeZero n] : Fin (n - 1) → Fin n :=
  fun j => Fin.cast (n_sub_one_add_one n) j.succ

/-- The shifted index is never `0`. -/
private theorem succIndex_ne_zero (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    succIndex n j ≠ 0 := by
  intro h
  have hval : (succIndex n j).val = (0 : Fin n).val := by rw [h]
  -- `(succIndex n j).val = j.val + 1`, but `(0 : Fin n).val = 0`.
  have hsucc : (succIndex n j).val = j.val + 1 := rfl
  rw [hsucc, Fin.val_zero] at hval
  exact Nat.succ_ne_zero _ hval

/-- For any nonzero `i : Fin n`, the predecessor lives in `Fin (n - 1)`. -/
private def predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) : Fin (n - 1) :=
  ⟨i.val - 1, by
    have hi : i.val < n := i.isLt
    have hipos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
      · exact h0
    omega⟩

/-- `succIndex` is a left-inverse of `predIndex` (when applied at a nonzero index). -/
private theorem succIndex_predIndex (n : ℕ) [NeZero n] (i : Fin n) (h : i ≠ 0) :
    succIndex n (predIndex n i h) = i := by
  have hipos : 0 < i.val := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · exact absurd (Fin.ext (h0.trans rfl) : i = 0) h
    · exact h0
  apply Fin.ext
  -- `(succIndex n (predIndex n i h)).val = (Fin.cast _ (Fin.succ ⟨i.val - 1, _⟩)).val
  -- = (i.val - 1) + 1 = i.val`.
  change (i.val - 1) + 1 = i.val
  omega

/-- `predIndex` is a left-inverse of `succIndex`. -/
private theorem predIndex_succIndex (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    predIndex n (succIndex n j) (succIndex_ne_zero n j) = j := by
  apply Fin.ext
  -- `(predIndex n (succIndex n j) _).val = (succIndex n j).val - 1 = (j.val + 1) - 1 = j.val`.
  change (j.val + 1) - 1 = j.val
  omega

/-! ## Coordinate-level building blocks -/

/-- Coordinate-level inclusion: insert `0` at index `0`. Sends
`x : Fin (n - 1) → ℝ` to the function `Fin n → ℝ` defined by
`f 0 = 0`, `f (succIndex n j) = x j`. -/
private def consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i =>
    if h : i = (0 : Fin n) then 0
    else x (predIndex n i h)

/-- Coordinate-level projection: drop index `0`. Sends `y : Fin n → ℝ`
to `Fin (n - 1) → ℝ` defined by `f j = y (succIndex n j)`. -/
private def tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  fun j => y (succIndex n j)

/-- The 0-th coordinate of `consZeroFun n x` is `0`. -/
private theorem consZeroFun_zero (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroFun n x 0 = 0 := dif_pos rfl

/-- For any `j : Fin (n - 1)`, `consZeroFun n x (succIndex n j) = x j`. -/
private theorem consZeroFun_succIndex (n : ℕ) [NeZero n]
    (x : Fin (n - 1) → ℝ) (j : Fin (n - 1)) :
    consZeroFun n x (succIndex n j) = x j := by
  unfold consZeroFun
  rw [dif_neg (succIndex_ne_zero n j), predIndex_succIndex]

/-- The coordinate-level projection is left-inverse to the coordinate-level
inclusion: `tailFun (consZeroFun x) = x`. -/
private theorem tailFun_consZeroFun (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    tailFun n (consZeroFun n x) = x := by
  funext j
  exact consZeroFun_succIndex n x j

/-- The coordinate-level inclusion recovers any function whose value at `0`
is `0` from its tail. -/
private theorem consZeroFun_tailFun (n : ℕ) [NeZero n] (y : Fin n → ℝ)
    (hy : y 0 = 0) :
    consZeroFun n (tailFun n y) = y := by
  funext i
  unfold consZeroFun tailFun
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, h]; exact hy.symm
  · rw [dif_neg h, succIndex_predIndex]

/-! ## The continuous-linear inclusion / projection on the unwrapped pi-types -/

/-- The continuous linear inclusion `(Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ)`
inserting a `0` at index `0`. -/
private def consZeroCLM (n : ℕ) [NeZero n] :
    (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    if h : i = (0 : Fin n) then 0
    else
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - 1) => ℝ)
        (predIndex n i h)

/-- `consZeroCLM` agrees with `consZeroFun` as a function. -/
private theorem consZeroCLM_apply (n : ℕ) [NeZero n] (x : Fin (n - 1) → ℝ) :
    consZeroCLM n x = consZeroFun n x := by
  funext i
  unfold consZeroCLM consZeroFun
  rw [ContinuousLinearMap.pi_apply]
  by_cases h : i = (0 : Fin n)
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

/-- The continuous linear projection `(Fin n → ℝ) →L[ℝ] (Fin (n - 1) → ℝ)`
dropping index `0`. -/
private def tailCLM (n : ℕ) [NeZero n] :
    (Fin n → ℝ) →L[ℝ] (Fin (n - 1) → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (succIndex n j)

/-- `tailCLM` agrees with `tailFun` as a function. -/
private theorem tailCLM_apply (n : ℕ) [NeZero n] (y : Fin n → ℝ) :
    tailCLM n y = tailFun n y := by
  funext j
  unfold tailCLM tailFun
  rw [ContinuousLinearMap.pi_apply]
  rfl

/-! ## The continuous-linear inclusion / projection on `EuclideanSpace` -/

/-- The continuous linear inclusion of `EuclideanSpace ℝ (Fin (n - 1))` into
`EuclideanSpace ℝ (Fin n)` inserting a `0` at index `0`. -/
def inclEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ((consZeroCLM n).comp
      (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)

/-- The continuous linear projection of `EuclideanSpace ℝ (Fin n)` onto
`EuclideanSpace ℝ (Fin (n - 1))` dropping index `0`. -/
def projEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
  (EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
    ((tailCLM n).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)

/-- Plain-function form of the inclusion: insert `0` at index `0`. -/
def inclEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanSpace ℝ (Fin n) :=
  inclEuclideanCLM n

/-- Plain-function form of the projection: drop index `0`. -/
def projEuclidean (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) :=
  projEuclideanCLM n

/-! ## Coordinate-level identities on `EuclideanSpace`

These identities use the fact that, for `y : EuclideanSpace ℝ (Fin n)`,
the application `y i` is `ofLp y i`, and the round-trip
`(EuclideanSpace.equiv _ _).symm ((EuclideanSpace.equiv _ _) y) = y` is
definitional.
-/

/-- Coordinate-access agreement: `inclEuclideanCLM n x i` (treating both
sides as functions of `Fin n`) equals `consZeroFun n (ofLp x) i`, where
`ofLp x : Fin (n - 1) → ℝ` is the underlying tuple of `x`. -/
private theorem inclEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin (n - 1))) (i : Fin n) :
    (inclEuclideanCLM n x) i = consZeroFun n x i := by
  -- Unfold the composition. The output of `inclEuclideanCLM n x` lives in
  -- `EuclideanSpace ℝ (Fin n)`. Coordinate access on it is `ofLp` evaluation.
  change (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
          ((consZeroCLM n).comp
            (EuclideanSpace.equiv (Fin (n - 1)) ℝ).toContinuousLinearMap)) x) i
        = consZeroFun n x i
  -- The application of the symm-of-equiv is `WithLp.toLp 2`. After that,
  -- coordinate access is just the underlying function.
  -- We rewrite using `ContinuousLinearMap.coe_comp'` and the explicit
  -- coercion of `ContinuousLinearEquiv` symm.
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  -- Now the LHS is `((EuclideanSpace.equiv (Fin n) ℝ).symm
  --   ((consZeroCLM n) ((EuclideanSpace.equiv (Fin (n - 1)) ℝ) x))) i`.
  -- Coordinate-access on `EuclideanSpace.equiv.symm _ : EuclideanSpace _ _` reduces to
  -- the underlying function:
  rw [consZeroCLM_apply]
  -- And the round-trip `EuclideanSpace.equiv x` is `ofLp x = x` (as a function).
  rfl

/-- Coordinate-access agreement for the projection. -/
private theorem projEuclideanCLM_apply_coord (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin n)) (j : Fin (n - 1)) :
    (projEuclideanCLM n y) j = tailFun n y j := by
  change (((EuclideanSpace.equiv (Fin (n - 1)) ℝ).symm.toContinuousLinearMap.comp
          ((tailCLM n).comp
            (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap)) y) j
        = tailFun n y j
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [tailCLM_apply]
  rfl

/-- The 0-th coordinate of `inclEuclidean n x` is `0`. -/
theorem inclEuclidean_zero_coord (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    inclEuclidean n x 0 = 0 := by
  change (inclEuclideanCLM n x) (0 : Fin n) = 0
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_zero n _

/-- The plain-function inverse identity: `projEuclidean (inclEuclidean x) = x`. -/
theorem projEuclidean_inclEuclidean (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    projEuclidean n (inclEuclidean n x) = x := by
  -- We compute coordinate by coordinate.
  apply (EuclideanSpace.equiv (Fin (n - 1)) ℝ).injective
  funext j
  -- The goal is to show `(EuclideanSpace.equiv) (projEuclidean (inclEuclidean x)) j = (EuclideanSpace.equiv) x j`.
  -- The left side reduces to `tailFun (inclEuclideanCLM x : as function)`.
  change (projEuclideanCLM n (inclEuclideanCLM n x)) j = (x : Fin (n - 1) → ℝ) j
  rw [projEuclideanCLM_apply_coord]
  -- LHS is now `tailFun n (inclEuclideanCLM n x) j = (inclEuclideanCLM n x) (succIndex n j)`.
  unfold tailFun
  rw [inclEuclideanCLM_apply_coord]
  exact consZeroFun_succIndex n _ _

/-! ## Smoothness of `inclEuclidean` and `projEuclidean` -/

/-- The inclusion `inclEuclidean` is `C^∞`. -/
theorem inclEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (inclEuclidean n) :=
  (inclEuclideanCLM n).contDiff

/-- The projection `projEuclidean` is `C^∞`. -/
theorem projEuclidean_contDiff (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (projEuclidean n) :=
  (projEuclideanCLM n).contDiff

/-- The inclusion `inclEuclidean` is continuous. -/
theorem inclEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (inclEuclidean n) :=
  (inclEuclideanCLM n).continuous

/-- The projection `projEuclidean` is continuous. -/
theorem projEuclidean_continuous (n : ℕ) [NeZero n] :
    Continuous (projEuclidean n) :=
  (projEuclideanCLM n).continuous

/-! ## Topological properties of `inclEuclidean` -/

/-- The inclusion `inclEuclidean` is injective. -/
theorem inclEuclidean_injective (n : ℕ) [NeZero n] :
    Function.Injective (inclEuclidean n) := by
  intro x y hxy
  have hx := projEuclidean_inclEuclidean n x
  have hy := projEuclidean_inclEuclidean n y
  rw [hxy] at hx
  exact hx.symm.trans hy

/-- The image of `inclEuclidean` is exactly the hyperplane `{y | y 0 = 0}`. -/
theorem range_inclEuclidean (n : ℕ) [NeZero n] :
    Set.range (inclEuclidean n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact inclEuclidean_zero_coord n x
  · intro hy
    refine ⟨projEuclidean n y, ?_⟩
    -- Need: `inclEuclidean (projEuclidean y) = y`. Coordinate-wise check.
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    change (inclEuclideanCLM n (projEuclideanCLM n y)) i = (y : Fin n → ℝ) i
    rw [inclEuclideanCLM_apply_coord]
    -- Now the goal is `consZeroFun n (projEuclideanCLM n y) i = (y : Fin n → ℝ) i`,
    -- where on the LHS the `consZeroFun` argument is implicitly converted via
    -- the `CoeFun` instance on `EuclideanSpace`.
    -- Replace `consZeroFun n (projEuclideanCLM n y)` with the value of `tailFun`
    -- applied to `y` at the appropriate index.
    by_cases h : i = (0 : Fin n)
    · rw [h, consZeroFun_zero]
      exact hy.symm
    · -- Use the inverse `consZeroFun_tailFun`.
      -- We need to show `consZeroFun n (projEuclideanCLM n y) i = y i` when `i ≠ 0`.
      -- Unfold `consZeroFun`:
      unfold consZeroFun
      rw [dif_neg h]
      -- Goal: `(projEuclideanCLM n y) (predIndex n i h) = (y : Fin n → ℝ) i`.
      rw [projEuclideanCLM_apply_coord]
      -- `tailFun n y (predIndex n i h) = y (succIndex n (predIndex n i h)) = y i`
      unfold tailFun
      rw [succIndex_predIndex]

/-- The image of `inclEuclidean` is closed in `EuclideanSpace ℝ (Fin n)`. -/
theorem inclEuclidean_isClosed_range (n : ℕ) [NeZero n] :
    IsClosed (Set.range (inclEuclidean n)) := by
  rw [range_inclEuclidean]
  -- The hyperplane `{y | y 0 = 0}` is the preimage of `{0}` under coordinate `0`.
  have heq : {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
      = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
  rw [heq]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact (PiLp.continuous_apply 2 _ 0)

/-- The inclusion `inclEuclidean` is a topological inducing map. -/
theorem inclEuclidean_isInducing (n : ℕ) [NeZero n] :
    IsInducing (inclEuclidean n) := by
  refine ⟨?_⟩
  apply le_antisymm
  · exact (inclEuclidean_continuous n).le_induced
  · intro U hU
    refine ⟨(projEuclidean n)⁻¹' U,
        (projEuclidean_continuous n).isOpen_preimage U hU, ?_⟩
    ext x
    simp [projEuclidean_inclEuclidean]

/-! ## The lifted inclusion `EuclideanSpace ℝ (Fin (n - 1)) → EuclideanHalfSpace n` -/

/-- The boundary inclusion lifted to `EuclideanHalfSpace n`. -/
def inclH (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (Fin (n - 1)) → EuclideanHalfSpace n :=
  fun x => ⟨inclEuclidean n x, by
    rw [inclEuclidean_zero_coord]⟩

/-- Subtype-value identity: `(inclH n x).val = inclEuclidean n x`. -/
theorem inclH_val (n : ℕ) [NeZero n] (x : EuclideanSpace ℝ (Fin (n - 1))) :
    (inclH n x).val = inclEuclidean n x := rfl

/-- `inclH` is continuous. -/
theorem inclH_continuous (n : ℕ) [NeZero n] : Continuous (inclH n) :=
  Continuous.subtype_mk (inclEuclidean_continuous n) _

/-- `inclH` is injective. -/
theorem inclH_injective (n : ℕ) [NeZero n] : Function.Injective (inclH n) := by
  intro x y hxy
  have hval : (inclH n x).val = (inclH n y).val := by rw [hxy]
  rw [inclH_val, inclH_val] at hval
  exact inclEuclidean_injective n hval

/-- `inclH` is a topological inducing map. -/
theorem inclH_isInducing (n : ℕ) [NeZero n] : IsInducing (inclH n) := by
  -- `Subtype.val ∘ inclH n = inclEuclidean n` (definitionally).
  -- The composition `Subtype.val ∘ inclH n` is inducing (via
  -- `inclEuclidean_isInducing`), and `Subtype.val` is itself inducing.
  -- By `IsInducing.of_comp`, `inclH n` is inducing.
  have h_comp_inducing :
      IsInducing ((Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
                    ∘ inclH n) := by
    -- Definitionally `Subtype.val ∘ inclH n = inclEuclidean n`.
    change IsInducing (inclEuclidean n)
    exact inclEuclidean_isInducing n
  -- `IsInducing.of_comp (hf : Continuous f) (hg : Continuous g)
  --   (hgf : IsInducing (g ∘ f)) : IsInducing f`, with `f := inclH n`, `g := Subtype.val`.
  exact IsInducing.of_comp (inclH_continuous n) continuous_subtype_val h_comp_inducing

/-! ## Range identity in `EuclideanSpace ℝ (Fin n)` -/

/-- The image of `inclH` after `modelWithCornersEuclideanHalfSpace n` is
exactly the hyperplane `{y | y 0 = 0}`. -/
theorem range_modelWithCorners_comp_inclH (n : ℕ) [NeZero n] :
    Set.range (modelWithCornersEuclideanHalfSpace n ∘ inclH n) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  ext y
  simp only [mem_range, Function.comp_apply, mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    change inclEuclidean n x 0 = 0
    exact inclEuclidean_zero_coord n x
  · intro hy
    have hin : y ∈ Set.range (inclEuclidean n) := by
      rw [range_inclEuclidean]; exact hy
    obtain ⟨x, hx⟩ := hin
    refine ⟨x, ?_⟩
    change (inclH n x).val = y
    rw [inclH_val]
    exact hx

/-! ## The model frontier reduces to a hyperplane -/

/-- The frontier of the range of `modelWithCornersEuclideanHalfSpace n` is the
hyperplane `{y | y 0 = 0}`. This packages
`frontier_range_modelWithCornersEuclideanHalfSpace` from Mathlib in the
`y 0 = 0` orientation. -/
theorem frontier_range_modelWithCornersEuclideanHalfSpace_eq (n : ℕ) [NeZero n] :
    frontier (Set.range (modelWithCornersEuclideanHalfSpace n)) =
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  ext y
  exact eq_comm

/-! ## Smoothness of the composition `I ∘ inclH ∘ boundaryI.symm` -/

/-- The composite `I ∘ inclH ∘ boundaryI.symm` agrees with `inclEuclidean`.
Because `boundaryI = modelWithCornersSelf ℝ _` is the identity model, the
composition collapses to `Subtype.val ∘ inclH n = inclEuclidean n`. -/
theorem comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm (n : ℕ) [NeZero n] :
    (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
        ∘ inclH n
        ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm
    = inclEuclidean n := by
  funext x
  rfl

/-! ## The standard inward direction `e_0 = EuclideanSpace.single 0 1`

We use the `0`-th standard basis vector of `EuclideanSpace ℝ (Fin n)` as the
inward direction. Concretely, this is `EuclideanSpace.single 0 1`, the vector
whose `0`-th coordinate is `1` and whose other coordinates are `0`. It is
transverse to the boundary hyperplane `{y | y 0 = 0}` because its `0`-th
coordinate is non-zero. -/

/-- The `0`-th coordinate of the standard inward direction is `1`. -/
private theorem single_zero_one_apply_zero (n : ℕ) [NeZero n] :
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 := by
  rw [show (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
        PiLp.single 2 (0 : Fin n) (1 : ℝ) from rfl]
  rw [PiLp.single_apply]
  simp

/-- The standard inward direction is not in the hyperplane `{y | y 0 = 0}`. -/
private theorem single_zero_one_notMem_hyperplane (n : ℕ) [NeZero n] :
    EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} := by
  intro hmem
  have : (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 = 1 :=
    single_zero_one_apply_zero n
  have : (1 : ℝ) = 0 := this ▸ hmem
  exact one_ne_zero this

/-- The Fréchet derivative of the inclusion `inclEuclidean n` is the constant
continuous linear map `inclEuclideanCLM n`. -/
private theorem fderiv_inclEuclidean (n : ℕ) [NeZero n]
    (y : EuclideanSpace ℝ (Fin (n - 1))) :
    fderiv ℝ (inclEuclidean n) y = inclEuclideanCLM n := by
  -- `inclEuclidean n` is the underlying function of the CLM `inclEuclideanCLM n`.
  change fderiv ℝ (inclEuclideanCLM n : EuclideanSpace ℝ (Fin (n - 1)) →
      EuclideanSpace ℝ (Fin n)) y = inclEuclideanCLM n
  exact (inclEuclideanCLM n).fderiv

/-- The range of the continuous-linear inclusion `inclEuclideanCLM` equals the
range of the underlying function `inclEuclidean`. -/
private theorem range_inclEuclideanCLM (n : ℕ) [NeZero n] :
    Set.range (inclEuclideanCLM n) = Set.range (inclEuclidean n) := rfl

/-- The standard inward direction `e_0` is transverse to the boundary
hyperplane: it does not lie in the image of the inclusion's derivative. -/
private theorem single_zero_one_transverse (n : ℕ) [NeZero n] :
    ∀ y : EuclideanSpace ℝ (Fin (n - 1)),
      EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∉
        Set.range (fderiv ℝ
          ((modelWithCornersEuclideanHalfSpace n :
              EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n))
            ∘ inclH n
            ∘ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).symm) y) := by
  intro y
  rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm,
      fderiv_inclEuclidean n y, range_inclEuclideanCLM, range_inclEuclidean]
  exact single_zero_one_notMem_hyperplane n

/-! ## The boundary hyperplane is Haar-null -/

/-- The hyperplane `{y : EuclideanSpace ℝ (Fin n) | y 0 = 0}` is the kernel of
the continuous linear functional `EuclideanSpace.proj 0`. As a strict linear
subspace of a finite-dim normed space, it has zero additive Haar measure (for
any choice of additive Haar measure on the space). -/
private theorem hyperplane_basisAddHaar_zero (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      {y : EuclideanSpace ℝ (Fin n) | y 0 = 0} = 0 := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  -- Express the hyperplane as the kernel of `EuclideanSpace.proj 0`.
  set ker : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.proj 0 :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm : ({y : EuclideanSpace ℝ (Fin n) | y 0 = 0} :
        Set (EuclideanSpace ℝ (Fin n))) = (ker : Set _) := by
    ext y
    simp [hker_def, LinearMap.mem_ker, EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar) ker ?_
  -- Show ker ≠ ⊤. The vector `e_0` is not in the kernel.
  intro hker_eq
  -- Membership of `e_0` in `⊤` is automatic; transport it to membership in ker.
  have h_in_top : EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∈
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  -- Membership in ker means `proj 0` of it is 0.
  have h_proj_zero : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
    exact this
  -- But proj 0 evaluates to coordinate 0 of the vector.
  have h_eval : (EuclideanSpace.proj (0 : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0 := rfl
  rw [single_zero_one_apply_zero n] at h_eval
  -- Contradiction: `proj 0 e_0 = 1` but is also `0`.
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

/-- The model-level boundary `frontier (Set.range (modelWithCornersEuclideanHalfSpace n))`
has zero `Module.finBasis`-Haar measure. Combines the explicit identification
of the frontier as the hyperplane `{y | y 0 = 0}` with the strict-subspace
null-measure fact. -/
private theorem frontier_range_modelWithCorners_basisAddHaar_zero
    (n : ℕ) [NeZero n] :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ((Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).addHaar :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      (frontier (Set.range (modelWithCornersEuclideanHalfSpace n))) = 0 := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  haveI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  rw [frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  exact hyperplane_basisAddHaar_zero n

/-! ## The `HasSmoothBoundary` instance -/

/-- The Euclidean half-space `EuclideanHalfSpace n` (for any `n` with `[NeZero n]`)
is a model with smooth boundary, with boundary modelled on the boundaryless
`EuclideanSpace ℝ (Fin (n - 1))` via the self-model. -/
instance instHasSmoothBoundary (n : ℕ) [NeZero n] :
    HasSmoothBoundary
      (EuclideanSpace ℝ (Fin n))
      (EuclideanHalfSpace n)
      (modelWithCornersEuclideanHalfSpace n) where
  boundaryE := EuclideanSpace ℝ (Fin (n - 1))
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := EuclideanSpace ℝ (Fin (n - 1))
  boundaryHTopologicalSpace := inferInstance
  boundaryI := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))
  boundaryIBoundaryless := inferInstance
  inclH := inclH n
  inclH_continuous := inclH_continuous n
  inclH_injective := inclH_injective n
  inclH_isInducing := inclH_isInducing n
  inclH_isClosed_image := by
    rw [range_modelWithCorners_comp_inclH]
    have heq :
        {y : EuclideanSpace ℝ (Fin n) | y 0 = 0}
          = (fun y : EuclideanSpace ℝ (Fin n) => y 0) ⁻¹' {0} := rfl
    rw [heq]
    refine IsClosed.preimage ?_ isClosed_singleton
    exact PiLp.continuous_apply 2 _ 0
  projE := projEuclidean n
  projE_continuous := projEuclidean_continuous n
  projE_contDiff := projEuclidean_contDiff n
  I_inclH_boundaryI_symm_contDiff := by
    rw [comp_modelWithCornersEuclideanHalfSpace_inclH_self_symm]
    exact inclEuclidean_contDiff n
  range_I_inclH := by
    rw [range_modelWithCorners_comp_inclH,
        frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  proj_inclH_compat := by
    intro x
    change projEuclidean n (inclEuclidean n x) = x
    exact projEuclidean_inclEuclidean n x
  inwardCoordE := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  inwardCoordE_transverse := single_zero_one_transverse n
  range_frontier_basis_addHaar_zero := by
    intro _
    exact frontier_range_modelWithCorners_basisAddHaar_zero n
  finrank_boundaryE_succ := by
    intro _
    -- `Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) + 1
    --     = (n - 1) + 1 = n = Module.finrank ℝ (EuclideanSpace ℝ (Fin n))`.
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    exact Nat.sub_one_add_one_eq_of_pos (Nat.pos_of_neZero n)

/-! ## Test: usability of the instance

The instance is genuinely usable. We verify that the boundary type and model
projections have the expected shape, and that the boundary chart structure is
recoverable from the typeclass.
-/

/-- Test: the boundary normed model of the half-space instance is the
`(n - 1)`-dimensional Euclidean space. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelE
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

/-- Test: the boundary topological model of the half-space instance is the
same `(n - 1)`-dimensional Euclidean space. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModelH
      (modelWithCornersEuclideanHalfSpace n)
      = EuclideanSpace ℝ (Fin (n - 1)) := rfl

/-- Test: the boundary model with corners is the boundaryless self-model. -/
example (n : ℕ) [NeZero n] :
    HasSmoothBoundary.boundaryModel
      (modelWithCornersEuclideanHalfSpace n)
      = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1))) := rfl

/-- Test: the projection drops the first coordinate, as a `C^∞` map. -/
example (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (instHasSmoothBoundary n).projE := projEuclidean_contDiff n

/-! ## `HasOrientableBoundary` instance for the Euclidean half-space model

The orientation typeclass `HasOrientableBoundary M` (defined in
`Orientation.lean`) records that, for any two manifold base points
`α₀, α₁ : BoundaryManifold I M` and any common boundary point `y` in their
chart sources, the chart-α₀ inward-direction representative
`inwardCoordAt α₀ y` and the chart-α₁ inward-direction representative
`inwardCoordAt α₁ y` differ by a strictly positive scalar modulo a
boundary-tangent vector.

For `M` self-charted by `EuclideanHalfSpace n` (the canonical model space
itself), the chart structure is trivial: all charts are the identity, and
chart transitions are the identity. Hence `inwardCoordAt α y = inwardCoordE`
for every base `α` and every boundary point `y`, and the orientation property
holds trivially with `c = 1`.

The general case for arbitrary `M` modelled on `EuclideanHalfSpace n` (with
non-trivial chart structure) reduces to the standard result that smooth
diffeomorphisms of half-space neighborhoods preserve the inward-pointing
direction at boundary points, with strictly positive `e_0`-component. The
present file provides the canonical self-charted instance; downstream code
producing non-trivially-charted manifolds-with-boundary can either supply the
typeclass instance manually or invoke the general theorem once it is
formalised.
-/

/-- The "trivial" base-coordinate identification on the canonical self-charted
model `EuclideanHalfSpace n`. The inverse trivialisation of the tangent bundle
at any base point, evaluated at any other point in the chart source, sends
`inwardCoordE` back to `inwardCoordE` (under the type alias
`TangentSpace (𝓡∂ n) y = EuclideanSpace ℝ (Fin n)`). -/
private theorem inwardCoordAt_self_charted_eq
    (n : ℕ) [NeZero n]
    (α y : DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.BoundaryManifold
      (modelWithCornersEuclideanHalfSpace n) (EuclideanHalfSpace n))
    (hy : (y : EuclideanHalfSpace n) ∈
      (chartAt (EuclideanHalfSpace n) (α : EuclideanHalfSpace n)).source) :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt
      (M := EuclideanHalfSpace n) α y =
      (instHasSmoothBoundary n).inwardCoordE := by
  -- `inwardCoordAt α y = (trivializationAt E (TangentSpace I) α.val).symm y inwardCoordE`.
  -- For self-charted `M = EuclideanHalfSpace n`, the chart-at-x is the identity,
  -- so `extChartAt = I` (essentially) and the chart transition collapses to the
  -- identity on `range I`. Hence `coordChange = id` and the symm-trivialization
  -- acts as the identity on the model-side input.
  -- The cleanest path: use `tangentCoordChange_self`. Here `α.val` and `y.val`
  -- are points in `EuclideanHalfSpace n`, and y.val ∈ chartAt α.val.source by
  -- hypothesis. The `tangentCoordChange` for `M = H` (self-charted) at α.val
  -- vs α.val coincides with the identity (`tangentCoordChange_self`). To get
  -- the cross-base case (`α.val` to `y.val`), we use `tangentCoordChange_comp`.
  change ((trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (modelWithCornersEuclideanHalfSpace n)) (α : EuclideanHalfSpace n)).symm
        (y : EuclideanHalfSpace n)) (instHasSmoothBoundary n).inwardCoordE =
      (instHasSmoothBoundary n).inwardCoordE
  -- Use `symmL_trivializationAt_eq_core`: when y.val ∈ chart-source α.val,
  -- the inverse trivialisation equals the `coordChange` at the base from
  -- `achart (EHS n) α.val` to `achart (EHS n) y.val`.
  have h_symmL :
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (modelWithCornersEuclideanHalfSpace n))
          (α : EuclideanHalfSpace n)).symmL ℝ (y : EuclideanHalfSpace n)) =
        (tangentBundleCore (modelWithCornersEuclideanHalfSpace n) (EuclideanHalfSpace n)).coordChange
          (achart (EuclideanHalfSpace n) (α : EuclideanHalfSpace n))
          (achart (EuclideanHalfSpace n) (y : EuclideanHalfSpace n))
          (y : EuclideanHalfSpace n) :=
    TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) hy
  -- Both `achart (EuclideanHalfSpace n) p` for any `p` is the identity chart
  -- (because `EuclideanHalfSpace n` is self-charted by `chartedSpaceSelf`),
  -- so the coordChange between them at any point equals the identity.
  -- Concretely: `(tangentBundleCore I H).coordChange (achart H α.val) (achart H y.val) z`
  --   = `fderivWithin ℝ (extChartAt I y.val ∘ (extChartAt I α.val).symm) (range I) (extChartAt I α.val z)`.
  -- For self-charted `H`, both `extChartAt I α.val` and `extChartAt I y.val` are equal to `I` (as functions),
  -- so the composition is `I ∘ I.symm = id` on `range I`. Hence the fderivWithin equals `id`.
  -- The cleanest way: use `tangentCoordChange_self` after rewriting the second `achart` to coincide.
  -- But the two acharts have different base points; in the self-charted setting they agree as functions
  -- but may not be defeq.
  -- We unfold to fderivWithin and compute directly.
  -- Step 1: `(triv α.val).symm y v = ((triv α.val).symmL y) v` (definitional).
  have h_symm_to_symmL :
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (modelWithCornersEuclideanHalfSpace n))
          (α : EuclideanHalfSpace n)).symm
            (y : EuclideanHalfSpace n)) (instHasSmoothBoundary n).inwardCoordE =
        ((trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace (modelWithCornersEuclideanHalfSpace n))
            (α : EuclideanHalfSpace n)).symmL ℝ (y : EuclideanHalfSpace n))
              (instHasSmoothBoundary n).inwardCoordE := rfl
  rw [h_symm_to_symmL, h_symmL]
  -- Now we have: `coordChange (achart α.val) (achart y.val) y.val inwardCoordE = inwardCoordE`.
  -- Express via fderivWithin: this equals fderivWithin ℝ φ (range I) (extChartAt I α.val y.val) inwardCoordE,
  -- where φ = extChartAt I y.val ∘ (extChartAt I α.val).symm.
  rw [tangentBundleCore_coordChange_achart]
  -- For `M = H` self-charted: extChartAt I p = I (as functions on H, agreeing on the source = univ).
  -- So φ = I ∘ I.symm = id on range I.
  -- The fderivWithin of the identity (more precisely: a function eventually-equal to the identity on
  -- range I at the chart-point) is the identity.
  -- We use `Filter.EventuallyEq.fderivWithin_eq` after establishing the eventually-equal.
  -- Strategy: use `fderivWithin_extChartAt_comp_extChartAt_symm_range` from Mathlib's
  -- MFDeriv.Atlas. That lemma says: fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) = id
  -- but we have extChartAt I y.val ∘ (extChartAt I α.val).symm with different basepoints.
  -- For self-charted M = H: `(extChartAt I p).symm = I.symm` (as a function, on the target), and
  -- `extChartAt I p = I` (as a function, on the source). Both agree as functions because the
  -- identity-chart's extension has source = range I, target = univ, and acts as I (resp. I.symm).
  -- Hence the composition `extChartAt I y.val ∘ (extChartAt I α.val).symm = I ∘ I.symm`, which equals
  -- the identity on the range of I.
  -- We compute: at `extChartAt I α.val y.val = I y.val` (in range I), the fderivWithin equals id.
  -- Use `fderivWithin_id` after showing the function eventually equals `id` near this point in `range I`.
  --
  -- Step: show `extChartAt I y.val ∘ (extChartAt I α.val).symm` and `id` are eventually-equal at the
  -- relevant point.
  -- Specifically, on the entire range I, both the LHS and id agree (LHS is I ∘ I.symm, restricted to
  -- range I, which is the identity).
  set z₀ : EuclideanSpace ℝ (Fin n) := extChartAt (modelWithCornersEuclideanHalfSpace n)
                                          (α : EuclideanHalfSpace n) (y : EuclideanHalfSpace n)
  have h_z₀_in_range :
      z₀ ∈ Set.range (modelWithCornersEuclideanHalfSpace n :
                        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) := by
    -- z₀ = extChartAt I α.val y.val = I (chartAt H α.val y.val) = I y.val (since chart is identity)
    -- Hence z₀ ∈ range I.
    show z₀ ∈ Set.range (modelWithCornersEuclideanHalfSpace n)
    refine ⟨(y : EuclideanHalfSpace n), ?_⟩
    -- need: I y = z₀ where z₀ = extChartAt I α y.
    -- For self-charted M=H: extChartAt I α y = (chartAt H α).extend I y = I (chartAt H α y) = I y
    -- (since chartAt H α is identity on its source and y is in the source).
    change (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n) = z₀
    -- z₀ unfolds to extChartAt I α.val y.val
    change (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n) =
        extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)
          (y : EuclideanHalfSpace n)
    -- For the self-charted EHS n, chartAt H α = OpenPartialHomeomorph.refl
    -- and extChartAt I α y = I (chartAt H α y) = I y
    rfl
  -- Now show: fderivWithin ℝ φ (range I) z₀ = id, where φ = extChartAt I y.val ∘ (extChartAt I α.val).symm.
  -- For self-charted EHS n: φ = I ∘ I.symm. The composition equals id on range I.
  have h_phi_eq_id_on_range :
      ∀ z ∈ Set.range (modelWithCornersEuclideanHalfSpace n :
                        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)),
        ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm) z = z := by
    intro z hz
    rcases hz with ⟨h, rfl⟩
    -- z = I h. Compute (extChartAt I y.val).symm (I h) = h (since extChartAt = I for self-charted).
    change (modelWithCornersEuclideanHalfSpace n) ((modelWithCornersEuclideanHalfSpace n).symm
            (modelWithCornersEuclideanHalfSpace n h)) =
          (modelWithCornersEuclideanHalfSpace n) h
    rw [(modelWithCornersEuclideanHalfSpace n).left_inv h]
  -- We can now compute the fderivWithin.
  -- The function φ = extChartAt I y.val ∘ (extChartAt I α.val).symm equals id on range I.
  -- Hence fderivWithin ℝ φ (range I) z₀ = fderivWithin ℝ id (range I) z₀ = id.
  have h_eq_on_range :
      Set.EqOn ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
                  (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm)
                (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
                (Set.range (modelWithCornersEuclideanHalfSpace n)) := by
    intro z hz
    exact h_phi_eq_id_on_range z hz
  -- The fderivWithin of φ on `range I` at z₀ equals the fderivWithin of id on `range I` at z₀,
  -- which equals the identity (since `range I` has unique-diff at every interior-type point).
  have h_fderiv_phi :
      fderivWithin ℝ ((extChartAt (modelWithCornersEuclideanHalfSpace n) (y : EuclideanHalfSpace n)) ∘
                       (extChartAt (modelWithCornersEuclideanHalfSpace n) (α : EuclideanHalfSpace n)).symm)
        (Set.range (modelWithCornersEuclideanHalfSpace n)) z₀ =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h_unique :
        UniqueDiffWithinAt ℝ (Set.range (modelWithCornersEuclideanHalfSpace n)) z₀ :=
      (modelWithCornersEuclideanHalfSpace n).uniqueDiffOn z₀ h_z₀_in_range
    rw [fderivWithin_congr h_eq_on_range (h_eq_on_range h_z₀_in_range), fderivWithin_id h_unique]
  -- Apply the result: the coordChange equals identity, so its action on inwardCoordE returns inwardCoordE.
  rw [h_fderiv_phi]
  rfl

/-- The orientation property holds for the canonical self-charted
`EuclideanHalfSpace n`: for any two boundary base points `α₀, α₁` and any
boundary point `y` in their chart sources, the chart-α₀ and chart-α₁
inward-direction representatives at `y` agree. Hence `c = 1` realises the
orientation. -/
instance instHasOrientableBoundary_self_EuclideanHalfSpace
    (n : ℕ) [NeZero n] :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.HasOrientableBoundary
      (E := EuclideanSpace ℝ (Fin n))
      (H := EuclideanHalfSpace n)
      (I := modelWithCornersEuclideanHalfSpace n)
      (EuclideanHalfSpace n) where
  inwardCoord_chart_consistent := by
    intro α₀ α₁ y hα₀ hα₁
    refine ⟨1, by norm_num, ?_⟩
    -- We want: `inwardCoordAt α₀ y - 1 • inwardCoordAt α₁ y ∈ range (dincl y).toLinearMap`.
    -- For self-charted `EuclideanHalfSpace n`, both `inwardCoordAt α₀ y` and `inwardCoordAt α₁ y`
    -- equal `inwardCoordE`, so the difference is zero.
    have h₀ := inwardCoordAt_self_charted_eq n α₀ y hα₀
    have h₁ := inwardCoordAt_self_charted_eq n α₁ y hα₁
    rw [h₀, h₁]
    simp only [one_smul, sub_self]
    exact ⟨0, map_zero _⟩

/-! ## Documented gap: orientation for the general case

For arbitrary `M` with `[ChartedSpace (EuclideanHalfSpace n) M]` and
`[IsManifold (𝓡∂ n) ∞ M]`, the orientation property is the standard fact
that smooth diffeomorphisms between half-space neighborhoods preserve the
inward direction at boundary points (with strictly positive `e_0`-component).

The formal proof reduces to the following Mathlib-style key lemma:

> For a smooth invertible map `φ : U → V` between open subsets of
> `range I = {z : EuclideanSpace ℝ (Fin n) | 0 ≤ z 0}` mapping `U ∩ frontier`
> bijectively to `V ∩ frontier`, and any boundary point `z₀ ∈ U ∩ frontier`,
> the `fderivWithin ℝ φ (range I) z₀` applied to `EuclideanSpace.single 0 1`
> has strictly positive 0-th component.

Steps for a Mathlib-style proof:

1. The chart transition `extChartAt I y.val ∘ (extChartAt I α.val).symm`, restricted
   to `range I`, is a smooth invertible map between open subsets of `range I`.
   (Available: `Mathlib.Geometry.Manifold.IsManifold.ExtChartAt` provides
   `contDiffOn_extendCoordChange` and `isInvertible_fderivWithin_extendCoordChange`.)

2. The chart transition maps the boundary `frontier (range I)` bijectively
   to itself. (Follows from `IsLocalDiffeomorphAt.isBoundaryPoint_iff` in
   `Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary`, line 394.)

3. By a Taylor-expansion argument: for `z₀` on the boundary and `e_0 = (1,0,…,0)`,
   the path `t ↦ z₀ + t · e_0` enters the half-space for `t > 0`. Its image under
   `φ` enters the half-space for small `t > 0`. Differentiating gives
   `(fderivWithin ℝ φ (range I) z₀ e_0) 0 ≥ 0`.

4. Strict positivity follows by combining (3) for `φ` and (3) for `φ⁻¹`,
   using the chain rule and invertibility of the derivative.

Once this key lemma is available in Mathlib, the general instance follows
algebraically: with `c_α := ((dincl-projection-of-inwardCoordAt α y))-coefficient
of inwardCoord y`, set `c := c_α₀ / c_α₁ > 0`. The specifically-required
strict positivity result is currently not in Mathlib. Until it is added (or
formalised here), the typeclass `HasOrientableBoundary` must be supplied
manually for non-self-charted manifolds-with-boundary modelled on
`EuclideanHalfSpace n`.

This file therefore provides the canonical self-charted instance
(`instHasOrientableBoundary_self_EuclideanHalfSpace`) but leaves the general
instance for downstream code or future Mathlib API additions.
-/

end EuclideanHalfSpaceInstance

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
