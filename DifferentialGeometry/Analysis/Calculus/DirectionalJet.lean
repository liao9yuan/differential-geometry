import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

/-!
# Directional iterated derivatives

This file relates ordinary iterated derivatives along affine lines to repeated
directional evaluations of iterated Fréchet derivatives.
-/

noncomputable section

open Set
open scoped ContDiff Pointwise

namespace DifferentialGeometry

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Analysis

/-- A fixed directional derivative commutes with every iterated derivative of a
`C∞` map on a regular unique-differentiability set. Equivalently, the new
leading derivative slot can be moved to the trailing slot. -/
theorem fderivWithin_iteratedFDerivWithin_apply_eq {G W : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set G} (hs : UniqueDiffOn ℝ s) (hs' : s ⊆ closure (interior s))
    (n : ℕ) {f : G → W} (hf : ContDiffOn ℝ ∞ f s) (u : G) :
    ∀ x ∈ s,
      fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x u =
        iteratedFDerivWithin ℝ n
          (fun y => fderivWithin ℝ f s y u) s x := by
  induction n with
  | zero =>
      intro x hx
      rw [iteratedFDerivWithin_zero_eq_comp,
        LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
      ext m
      rw [ContinuousLinearMap.comp_apply, iteratedFDerivWithin_zero_apply]
      rfl
  | succ n ih =>
      intro x hx
      set H := iteratedFDerivWithin ℝ n f s with hH_def
      set e :=
        (continuousMultilinearCurryLeftEquiv
          ℝ (fun _ : Fin (n + 1) => G) W).symm with he_def
      have hLHS :
          fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x u =
            e (fderivWithin ℝ (fderivWithin ℝ H s) s x u) := by
        rw [iteratedFDerivWithin_succ_eq_comp_left]
        rw [e.comp_fderivWithin (f := fderivWithin ℝ H s) (hs x hx)]
        rfl
      have hIHeq :
          Set.EqOn
            (iteratedFDerivWithin ℝ n
              (fun y => fderivWithin ℝ f s y u) s)
            (fun y => fderivWithin ℝ H s y u) s :=
        fun y hy => (ih y hy).symm
      have hRHS :
          iteratedFDerivWithin ℝ (n + 1)
              (fun y => fderivWithin ℝ f s y u) s x =
            e (fderivWithin ℝ
              (fun y => fderivWithin ℝ H s y u) s x) := by
        rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
          fderivWithin_congr hIHeq (hIHeq hx)]
      rw [hLHS, hRHS]
      congr 1
      have hHC2 : ContDiffWithinAt ℝ 2 H s x := by
        refine (hf x hx).iteratedFDerivWithin_right hs ?_ hx
        have h2n :
            (2 : WithTop ℕ∞) + (n : WithTop ℕ∞) =
              ((2 + n : ℕ∞) : WithTop ℕ∞) := by
          norm_cast
        rw [h2n]
        exact_mod_cast le_top
      have hn2 : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) :=
        le_of_eq minSmoothness_of_isRCLikeNormedField
      have hsymH : IsSymmSndFDerivWithinAt ℝ H s x :=
        hHC2.isSymmSndFDerivWithinAt hn2 hs (hs' hx) hx
      have hHdiff :
          DifferentiableWithinAt ℝ (fderivWithin ℝ H s) s x :=
        (hHC2.fderivWithin_right hs (m := 1) le_rfl hx)
          .differentiableWithinAt (by simp)
      have hflip :
          fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x =
            (fderivWithin ℝ (fderivWithin ℝ H s) s x).flip u := by
        rw [fderivWithin_clm_apply (hs x hx) hHdiff
            (differentiableWithinAt_const u),
          fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add]
      refine ContinuousLinearMap.ext (fun v => ?_)
      rw [hflip, ContinuousLinearMap.flip_apply]
      exact hsymH.eq u v

end Analysis

/-- Restricting a smooth germ to the affine line `x + t • v` evaluates each
iterated Fréchet derivative on the repeated direction `v`. -/
theorem iteratedDeriv_line
    {f : E → F} {x v : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 =
      iteratedFDeriv ℝ n f x (fun _ => v) := by
  have hfn : ContDiffAt ℝ n f x :=
    hf.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)
  obtain ⟨u, hu, hfu⟩ := hfn.contDiffOn le_rfl (by simp)
  let U : Set E := interior u
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hu
  have hfU : ContDiffOn ℝ n f U := hfu.mono interior_subset
  let S : Set E := (fun y : E => x + y) ⁻¹' U
  have hS_open : IsOpen S :=
    hU_open.preimage (continuous_const.add continuous_id)
  have hzeroS : (0 : E) ∈ S := by
    simpa only [S, Set.mem_preimage, add_zero] using hxU
  have hxS : x +ᵥ S = U := by
    ext y
    simp only [Set.mem_vadd_set]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [S, Set.mem_preimage, vadd_eq_add] using hz
    · intro hy
      refine ⟨y - x, ?_, ?_⟩
      · have hxy : x + (y - x) = y := by abel
        simpa only [S, Set.mem_preimage, hxy] using hy
      · rw [vadd_eq_add]
        abel
  let q : E → F := fun y => f (x + y)
  have hq : ContDiffOn ℝ n q S :=
    hfU.comp (contDiff_const.add contDiff_id).contDiffOn
      (fun y hy => hy)
  let L : ℝ →L[ℝ] E :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let T : Set ℝ := L ⁻¹' S
  have hT_open : IsOpen T := hS_open.preimage L.continuous
  have hzeroT : (0 : ℝ) ∈ T := by
    simpa only [T, Set.mem_preimage, L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, zero_smul] using hzeroS
  have hLzero : L (0 : ℝ) ∈ S := by
    exact hzeroT
  have hLzero_eq : L (0 : ℝ) = 0 := by
    simp only [L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, zero_smul]
  have hcomp :=
    L.iteratedFDerivWithin_comp_right hq hS_open.uniqueDiffOn
      hT_open.uniqueDiffOn hLzero (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hT_open hzeroT] at hcomp
  have hshift :=
    iteratedFDerivWithin_comp_add_left
      (𝕜 := ℝ) (f := f) (s := S) n x (0 : E)
  rw [add_zero, hxS,
    iteratedFDerivWithin_of_isOpen n hU_open hxU] at hshift
  change iteratedFDerivWithin ℝ n q S 0 =
    iteratedFDeriv ℝ n f x at hshift
  rw [hLzero_eq, hshift] at hcomp
  have hline : q ∘ L = fun t : ℝ => f (x + t • v) := by
    funext t
    simp only [q, Function.comp_apply, L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply]
  rw [hline] at hcomp
  have happ := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) F =>
      A (fun _ => (1 : ℝ))) hcomp
  simpa only [iteratedDeriv_eq_iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Function.comp_apply, L, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul] using happ

/-- Postcomposition by a continuous linear map commutes with ordinary
iterated derivatives. -/
theorem iteratedDeriv_clm
    {f : ℝ → F} {x : ℝ} (L : F →L[ℝ] G)
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    iteratedDeriv n (fun t => L (f t)) x =
      L (iteratedDeriv n f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv,
    show (fun t => L (f t)) = L ∘ f from rfl,
    L.iteratedFDeriv_comp_left hf (by exact_mod_cast le_top)]
  rfl

end DifferentialGeometry

end
