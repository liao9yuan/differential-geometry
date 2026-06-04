import DifferentialGeometry.Analysis.ODE.Flow.JointContinuity

/-!
# The inhomogeneous parametric linear ODE

The solution operator for `Z'(t) = A(x, t) Z(t) + b(x, t)`, built from the homogeneous
operator via the augmented-coefficient device on `G × ℝ`.

## Main definitions

* `inhomogAugmentedCoeff A b` — augmented coefficient on `G × ℝ` encoding the inhomogeneity.
* `HasInhomogLinearODESolution` — per-parameter existence predicate for the inhomogeneous ODE.
* `inhomogLinearODESolution A b a b' h₀ Z₀` — the inhomogeneous parametric solution, the first
  component of the augmented-system solution.

## Main results

* `inhomogLinearODESolution_init` — initial condition.
* `inhomogLinearODESolution_hasDerivAt` — ODE clause under joint continuity of `A` and `b`.
* `inhomogLinearODESolution_continuousOn` — joint continuity of the inhomogeneous solution.

`[CompleteSpace G]` is required throughout.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section Inhomogeneous

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Augmented coefficient** of an inhomogeneous linear ODE.

For `A : F → ℝ → (G →L[ℝ] G)` and `b : F → ℝ → G`, this is the continuous
linear map `AHat(x, t) : (G × ℝ) →L[ℝ] (G × ℝ)` sending `(g, c)` to
`(A(x, t) g + c • b(x, t), 0)`.  Its first component combines the linear part
on `G` with the inhomogeneity scaled by the auxiliary scalar component; its
second component is identically zero, so the auxiliary scalar component of any
solution of the associated homogeneous system has zero derivative. -/
noncomputable def inhomogAugmentedCoeff
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G) (x : F) (t : ℝ) :
    (G × ℝ) →L[ℝ] (G × ℝ) :=
  (((A x t).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
    ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b x t))).prod 0

@[simp] lemma inhomogAugmentedCoeff_apply
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G) (x : F) (t : ℝ) (gc : G × ℝ) :
    inhomogAugmentedCoeff A b x t gc = (A x t gc.1 + gc.2 • b x t, 0) := by
  simp [inhomogAugmentedCoeff]

private lemma inhomogAugmentedCoeff_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {U : Set F} {a b' : ℝ}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b')) :
    ContinuousOn (Function.uncurry (inhomogAugmentedCoeff A b))
      (U ×ˢ Set.Ioo a b') := by
  have h_first : ContinuousOn
      (fun p : F × ℝ => (A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ))
      (U ×ˢ Set.Ioo a b') := by
    exact hA_cont.clm_comp (continuousOn_const)
  have h_second : ContinuousOn
      (fun p : F × ℝ =>
        (ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
    have h_smul_cont :
        Continuous (fun y : G => (ContinuousLinearMap.snd ℝ G ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (G × ℝ) G
        (ContinuousLinearMap.snd ℝ G ℝ)).continuous
    exact h_smul_cont.comp_continuousOn hb_cont
  have h_sum : ContinuousOn
      (fun p : F × ℝ =>
        ((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)))
      (U ×ˢ Set.Ioo a b') := h_first.add h_second
  have h_prodL_cont :
      Continuous (fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) =>
        q.1.prod q.2) :=
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × ℝ) (F := G) (G := ℝ)
      ℝ).continuous
  have h_pair : ContinuousOn
      (fun p : F × ℝ =>
        (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
        (0 : (G × ℝ) →L[ℝ] ℝ)))
      (U ×ˢ Set.Ioo a b') := h_sum.prodMk continuousOn_const
  have hcomp : ContinuousOn
      ((fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) => q.1.prod q.2) ∘
        (fun p : F × ℝ =>
          (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
            ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
          (0 : (G × ℝ) →L[ℝ] ℝ))))
      (U ×ˢ Set.Ioo a b') :=
    h_prodL_cont.comp_continuousOn h_pair
  exact hcomp

/-- **Per-parameter existence predicate** for the inhomogeneous linear ODE.
`HasInhomogLinearODESolution A b a b' h₀ Z₀ x` asserts that for the fixed
parameter `x : F`, there exists a curve `Z : ℝ → G` with `Z h₀ = Z₀ x` and
`HasDerivAt Z (A x t (Z t) + b x t) t` for every `t ∈ Ioo a b'`. -/
def HasInhomogLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧
    ∀ t ∈ Set.Ioo a b', HasDerivAt Z (A x t (Z t) + b x t) t

/-- **Parametric solution of the inhomogeneous linear ODE**
`Z'(t) = A(x, t) Z(t) + b(x, t)` with initial condition `Z(x, h₀) = Z₀ x` on
the open interval `Ioo a b'`.

Defined as the first component of the augmented-system solution
`linearODESolution (inhomogAugmentedCoeff A b) a b' h₀ (fun x => (Z₀ x, 1)) x t`.
This is total: when joint continuity of `A` and `b` holds, it satisfies both
the initial-condition and ODE clauses; otherwise it falls back via the
underlying `linearODESolution` fallback. -/
noncomputable def inhomogLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) : F → ℝ → G :=
  fun x t =>
    (linearODESolution (inhomogAugmentedCoeff A b) a b' h₀
      (fun y => (Z₀ y, (1 : ℝ))) x t).1

/-- **Initial condition** for `inhomogLinearODESolution`.  At `t = h₀`, the
parametric solution equals the initial datum `Z₀ x`. -/
theorem inhomogLinearODESolution_init
    (A : F → ℝ → (G →L[ℝ] G)) (b : F → ℝ → G)
    (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) :
    inhomogLinearODESolution A b a b' h₀ Z₀ x h₀ = Z₀ x := by
  unfold inhomogLinearODESolution
  rw [linearODESolution_init]

/-- **Auxiliary scalar component stays at one**.

If the augmented coefficient is continuous on `U ×ˢ Ioo a b'`, then the second
component of the augmented solution is identically `1` on `Ioo a b'`.  Its
derivative is `0` (second component of `AHat`) and its value at `h₀` is `1`. -/
private theorem inhomogLinearODESolution_second_eq_one
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    (linearODESolution (inhomogAugmentedCoeff A b) a b' h₀
        (fun y => (Z₀ y, (1 : ℝ))) x t).2 = 1 := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  set ZHat : ℝ → G × ℝ := fun s =>
    linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ))) x s with hZHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat_deriv : ∀ s ∈ Set.Ioo a b',
      HasDerivAt ZHat (AHat x s (ZHat s)) s :=
    fun s hs => linearODESolution_hasDerivAt hab_lt h₀_mem hU hAHat_cont hx hs
  have hZHat_init : ZHat h₀ = (Z₀ x, (1 : ℝ)) := linearODESolution_init _ _ _ _ _ _
  set w : ℝ → ℝ := fun s => (ZHat s).2 with hw_def
  have hw_init : w h₀ = 1 := by
    change (ZHat h₀).2 = 1
    rw [hZHat_init]
  have hw_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt w 0 s := by
    intro s hs
    have hd : HasDerivAt ZHat (AHat x s (ZHat s)) s := hZHat_deriv s hs
    have h_snd_eq : (AHat x s (ZHat s)).2 = 0 := by
      simp [hAHat_def, inhomogAugmentedCoeff_apply]
    have h_fderiv_snd : HasFDerivAt (Prod.snd : G × ℝ → ℝ)
        (ContinuousLinearMap.snd ℝ G ℝ) (ZHat s) := hasFDerivAt_snd
    have h_comp := h_fderiv_snd.comp_hasDerivAt s hd
    have h_eq_w : (Prod.snd : G × ℝ → ℝ) ∘ ZHat = w := rfl
    rw [h_eq_w] at h_comp
    have h_eq_val :
        (ContinuousLinearMap.snd ℝ G ℝ) (AHat x s (ZHat s)) = (AHat x s (ZHat s)).2 := rfl
    rw [h_eq_val, h_snd_eq] at h_comp
    exact h_comp
  have h_diff : DifferentiableOn ℝ w (Set.Ioo a b') := by
    intro s hs
    exact ((hw_deriv s hs).differentiableAt).differentiableWithinAt
  have h_deriv_zero : Set.EqOn (deriv w) 0 (Set.Ioo a b') := by
    intro s hs
    have hd : HasDerivAt w 0 s := hw_deriv s hs
    simp [hd.deriv]
  have h_open : IsOpen (Set.Ioo a b' : Set ℝ) := isOpen_Ioo
  have h_preconn : IsPreconnected (Set.Ioo a b' : Set ℝ) := isPreconnected_Ioo
  have h_const := h_open.is_const_of_deriv_eq_zero h_preconn h_diff h_deriv_zero ht h₀_mem
  change w t = 1
  rw [h_const, hw_init]

/-- **ODE clause** for `inhomogLinearODESolution` under joint continuity.

When `A` and `b` are jointly continuous on `U ×ˢ Ioo a b'`, the parametric
solution at any `x ∈ U` satisfies the inhomogeneous linear ODE pointwise on
`Ioo a b'`. -/
theorem inhomogLinearODESolution_hasDerivAt
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasDerivAt (inhomogLinearODESolution A b a b' h₀ Z₀ x ·)
      (A x t (inhomogLinearODESolution A b a b' h₀ Z₀ x t) + b x t) t := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  set ZHat : ℝ → G × ℝ := fun s =>
    linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ))) x s with hZHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat_deriv : HasDerivAt ZHat (AHat x t (ZHat t)) t :=
    linearODESolution_hasDerivAt hab_lt h₀_mem hU hAHat_cont hx ht
  have h_snd_one : (ZHat t).2 = 1 :=
    inhomogLinearODESolution_second_eq_one
      hab_lt h₀_mem hU hA_cont hb_cont hx ht
  have h_fst_eq : (AHat x t (ZHat t)).1 = A x t (ZHat t).1 + (ZHat t).2 • b x t := by
    simp [hAHat_def, inhomogAugmentedCoeff_apply]
  have h_fderiv_fst : HasFDerivAt (Prod.fst : G × ℝ → G)
      (ContinuousLinearMap.fst ℝ G ℝ) (ZHat t) := hasFDerivAt_fst
  have h_comp := h_fderiv_fst.comp_hasDerivAt t hZHat_deriv
  have h_proj : (Prod.fst : G × ℝ → G) ∘ ZHat =
      (inhomogLinearODESolution A b a b' h₀ Z₀ x ·) := by
    funext s
    rfl
  rw [h_proj] at h_comp
  have h_fst_val :
      (ContinuousLinearMap.fst ℝ G ℝ) (AHat x t (ZHat t)) = (AHat x t (ZHat t)).1 := rfl
  rw [h_fst_val, h_fst_eq, h_snd_one, one_smul] at h_comp
  have h_ZHat_fst : (ZHat t).1 = inhomogLinearODESolution A b a b' h₀ Z₀ x t := rfl
  rw [h_ZHat_fst] at h_comp
  exact h_comp

/-- **Joint continuity of `inhomogLinearODESolution` in `(x, t)`**.

If `A` and `b` are jointly continuous on `U × Ioo a b'` and `Z₀` is continuous
on `U`, then the parametric solution
`(x, t) ↦ inhomogLinearODESolution A b a b' h₀ Z₀ x t` is jointly continuous on
`U × Ioo a b'`. -/
theorem inhomogLinearODESolution_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {a b' h₀ : ℝ} {Z₀ : F → G}
    (hab_lt : a < b') (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb_cont : ContinuousOn (Function.uncurry b) (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (Function.uncurry (inhomogLinearODESolution A b a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  set AHat : F → ℝ → (G × ℝ) →L[ℝ] (G × ℝ) := inhomogAugmentedCoeff A b with hAHat_def
  have hAHat_cont : ContinuousOn (Function.uncurry AHat) (U ×ˢ Set.Ioo a b') :=
    inhomogAugmentedCoeff_continuousOn hA_cont hb_cont
  have hZHat₀_cont : ContinuousOn (fun y => (Z₀ y, (1 : ℝ))) U :=
    hZ₀_cont.prodMk continuousOn_const
  have h_aug_cont : ContinuousOn
      (Function.uncurry
        (linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ)))))
      (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn hab_lt h₀_mem hU hAHat_cont hZHat₀_cont
  have h_eq : Function.uncurry (inhomogLinearODESolution A b a b' h₀ Z₀) =
      Prod.fst ∘
        Function.uncurry
          (linearODESolution AHat a b' h₀ (fun y => (Z₀ y, (1 : ℝ)))) := by
    funext p
    rfl
  rw [h_eq]
  exact continuous_fst.comp_continuousOn h_aug_cont

end Inhomogeneous

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
