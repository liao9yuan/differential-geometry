import DifferentialGeometry.Topology.Morse.Taylor
import DifferentialGeometry.Topology.Morse.LocalNormalForm
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace DifferentialGeometry.Topology.Morse

-- Pullback of a bilinear form along a linear map.
noncomputable def bilinPullback {n : ℕ}
    (H : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (L : MorseModel n →L[ℝ] MorseModel (n + 1)) : MorseModel n →L[ℝ] MorseModel n →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun u => ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ (H (L u)) L
        map_add' := by
          intro u v
          ext w
          simp [map_add]
        map_smul' := by
          intro c u
          ext w
          simp [map_smul] }
    cont := by
      fun_prop }

open Filter
open scoped Topology

namespace Completion

variable {n : ℕ}

-- View a continuous bilinear family as a LinearMap.BilinForm family.
noncomputable def clmBilin {n : ℕ}
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ) :
    MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)) :=
  fun x =>
    { toFun := fun u => { toFun := fun v => a x u v
                          map_add' := by intro v w; simp [map_add]
                          map_smul' := by intro c v; simp [map_smul] }
      map_add' := by intro u₁ u₂; ext v; simp [map_add]
      map_smul' := by intro c u; ext v; simp [map_smul] }

-- Hessian of a composition at a critical point of the outer function:
-- d²(f∘σ)(0) = (d²f(0)) ∘ (dσ 0, dσ 0).
theorem hessian_pullback_at_critical (f : MorseModel (n + 1) → ℝ)
    (σ : MorseModel n → MorseModel (n + 1))
    (hf : ContDiff ℝ 2 f) (hσ : ContDiff ℝ 2 σ)
    (hσ0 : σ (0 : MorseModel n) = 0) (hcrit : fderiv ℝ f 0 = 0)
    (u v : MorseModel n) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (σ x'))) (0 : MorseModel n)) u v =
    (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n) u)
        (fderiv ℝ σ (0 : MorseModel n) v) := by
  -- fderiv (f∘σ) x = (fderiv f (σ x)).comp (fderiv σ x)
  have hfd : ∀ x : MorseModel n, fderiv ℝ (fun x' : MorseModel n => f (σ x')) x =
      ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
        (fderiv ℝ f (σ x)) (fderiv ℝ σ x) := by
    intro x
    have hdf : DifferentiableAt ℝ f (σ x) :=
      (hf.contDiffAt (x := σ x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    have hdσ : DifferentiableAt ℝ σ x :=
      (hσ.contDiffAt (x := x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    have h := fderiv_comp x (g := f) (f := σ) (hg := hdf) (hf := hdσ)
    calc
      fderiv ℝ (fun x' : MorseModel n => f (σ x')) x = fderiv ℝ (f ∘ σ) x := by
        rfl
      _ = (fderiv ℝ f (σ x)).comp (fderiv ℝ σ x) := h
      _ = ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ x)) (fderiv ℝ σ x) := by
        rw [ContinuousLinearMap.compL_apply]
  -- the derivative of x ↦ fderiv f (σ x) at 0
  have hdf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (σ (0 : MorseModel n)) :=
    by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
        hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ f) (σ (0 : MorseModel n)) :=
        ((h1 (σ (0 : MorseModel n)) (Set.mem_univ _)).differentiableWithinAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
      exact hd.hasFDerivAt
  have hdσ' : HasFDerivAt σ (fderiv ℝ σ (0 : MorseModel n)) (0 : MorseModel n) :=
    ((hσ.contDiffAt (x := (0 : MorseModel n))).differentiableAt
      (by decide : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  -- the derivative of x ↦ fderiv σ x at 0
  have hd2 : HasFDerivAt (fun x : MorseModel n => fderiv ℝ σ x)
      (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) (0 : MorseModel n) :=
    by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ σ) Set.univ :=
        hσ.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ σ) (0 : MorseModel n) :=
        ((h1 (0 : MorseModel n) (Set.mem_univ _)).differentiableWithinAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
      exact hd.hasFDerivAt
  have hcomp' : HasFDerivAt (fun y : MorseModel n =>
        ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
      (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
        ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n)))
            (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
              (fderiv ℝ σ (0 : MorseModel n))))
      (0 : MorseModel n) := by
    have hg : HasFDerivAt (fun x : MorseModel n => fderiv ℝ f (σ x))
        (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
          (fderiv ℝ σ (0 : MorseModel n)))
        (0 : MorseModel n) :=
      HasFDerivAt.comp (0 : MorseModel n) (g := fderiv ℝ f)
        (g' := fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (f := σ)
        (f' := fderiv ℝ σ (0 : MorseModel n)) (hg := hdf') (hf := hdσ')
    have hh : HasFDerivAt (fun y : MorseModel n =>
        ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
        (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
          ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
            (fderiv ℝ σ (0 : MorseModel n)))
              (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
                (fderiv ℝ σ (0 : MorseModel n))))
        (0 : MorseModel n) := by
      have hc : DifferentiableAt ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) :=
        hg.differentiableAt
      have hd : DifferentiableAt ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) :=
        hd2.differentiableAt
      have hmain := fderiv_clm_comp (𝕜 := ℝ) (E := MorseModel n) (F := MorseModel n)
        (G := MorseModel (n + 1)) (H := ℝ) (c := fun x : MorseModel n => fderiv ℝ f (σ x))
        (d := fun x : MorseModel n => fderiv ℝ σ x) (x := (0 : MorseModel n)) hc hd
      have hfderiv : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
          ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n)) := hg.fderiv
      have hdderiv : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
          fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
      rw [hfderiv, hdderiv] at hmain
      have hhmain : HasFDerivAt (fun y : MorseModel n =>
          ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
            (fderiv ℝ f (σ y)) (fderiv ℝ σ y))
          (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
              (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
            ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
              (fderiv ℝ σ (0 : MorseModel n)))
                (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
                  (fderiv ℝ σ (0 : MorseModel n))))
          (0 : MorseModel n) :=
        by
          have hfun : (fun y : MorseModel n =>
              ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
                (fderiv ℝ f (σ y)) (fderiv ℝ σ y)) = fun y : MorseModel n =>
                  (fderiv ℝ f (σ y)).comp (fderiv ℝ σ y) := by
            funext y
            simp [ContinuousLinearMap.compL_apply]
          simpa [hfun, hmain] using (hg.clm_comp hd2 : HasFDerivAt
            (fun y : MorseModel n => (fderiv ℝ f (σ y)).comp (fderiv ℝ σ y))
            (((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ)
                (fderiv ℝ f (σ (0 : MorseModel n)))).comp (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
              ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
                (fderiv ℝ σ (0 : MorseModel n))).comp
                  ((fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))).comp (fderiv ℝ σ (0 : MorseModel n))))
            0)
      simpa [ContinuousLinearMap.comp_apply] using hhmain
    simpa [hfd] using hh
  -- combine: at the critical point the second compL term vanishes
  -- at the critical point the first compL term vanishes; the second is the pullback
  have hg' : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
      ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
        (fderiv ℝ σ (0 : MorseModel n)) := by
    exact (by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ :=
        hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      have hd : DifferentiableAt ℝ (fderiv ℝ f) (σ (0 : MorseModel n)) :=
        ((h1 (σ (0 : MorseModel n)) (Set.mem_univ _)).differentiableWithinAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
      have hc : HasFDerivAt (fun x : MorseModel n => fderiv ℝ f (σ x))
          (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n))) (0 : MorseModel n) :=
        HasFDerivAt.comp (0 : MorseModel n) (g := fderiv ℝ f)
          (g' := fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n))) (f := σ)
          (f' := fderiv ℝ σ (0 : MorseModel n)) (hg := hd.hasFDerivAt) (hf := hdσ')
      exact hc.fderiv)
  have hd2' : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
      fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
  have hh0 : ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))).comp
            (fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n)) +
        ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n))).comp
            (fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n))) =
      bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) := by
    rw [hσ0, hcrit, hg', hd2']
    apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro z
    simp [bilinPullback, hσ0, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  have hmain' : HasFDerivAt (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x)
      (bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)))
      (0 : MorseModel n) := by
    -- the function: by hfd
    have hfun' : (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x) =
        fun y : MorseModel n => ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y) := by
      funext x
      exact hfd x
    have hfun'' : (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x) =
        fun y : MorseModel n => ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ y)) (fderiv ℝ σ y) := hfun'
    have hderiv' : (ContinuousLinearMap.comp (ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ
          (fderiv ℝ f (σ (0 : MorseModel n)))) (fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n)) +
        ContinuousLinearMap.comp ((ContinuousLinearMap.compL ℝ (MorseModel n) (MorseModel (n + 1)) ℝ).flip
          (fderiv ℝ σ (0 : MorseModel n)))
            (ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
              (fderiv ℝ σ (0 : MorseModel n)))) =
        bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) := by
      have hg2 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ f (σ x)) (0 : MorseModel n) =
          ContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) (σ (0 : MorseModel n)))
            (fderiv ℝ σ (0 : MorseModel n)) := hg'
      have hd2_3 : fderiv ℝ (fun x : MorseModel n => fderiv ℝ σ x) (0 : MorseModel n) =
          fderiv ℝ (fderiv ℝ σ) (0 : MorseModel n) := rfl
      rw [← hd2_3, ← hg2]
      exact hh0
    rw [hfun'']
    rw [hderiv'] at hcomp'
    exact hcomp'
  have hfinal : fderiv ℝ (fun x : MorseModel n => fderiv ℝ (fun x' : MorseModel n => f (σ x')) x)
      (0 : MorseModel n) = bilinPullback (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ σ (0 : MorseModel n)) :=
    hmain'.fderiv
  -- apply both sides to u v
  have := congrArg (fun L : (MorseModel n) →L[ℝ] (MorseModel n →L[ℝ] ℝ) => L u v) hfinal
  simpa [bilinPullback, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply] using this

-- The critical section as a map on the tail space.
noncomputable def morseSection
    {n : ℕ} (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel n → MorseModel (n + 1) :=
  fun x' => φ.symm (morseCons (0 : ℝ) x')

theorem morseSection_tail {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hy : morseCons (0 : ℝ) x' ∈ φ.target) :
    morseTail (morseSection φ x') = x' :=
  morseCriticalSection_tail f φ hφ hy

theorem morseSection_zero {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hcrit : fderiv ℝ f 0 = 0) (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source) :
    morseSection φ (0 : MorseModel n) = 0 :=
  morseCriticalSection_zero f φ hφ hcrit hsrc

theorem morseSection_head_critical {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (_hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (_hy : morseCons (0 : ℝ) x' ∈ φ.target) :
    morseHead (morseSection φ x') = morseCriticalSection φ x' := by
  rfl

-- The completed-square head coordinate along the section.
noncomputable def morseSectionHead {n : ℕ}
    (a : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)))
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel n → ℝ :=
  fun x' => morseHead (morseCompletionMap a (morseSection φ x'))

-- Reduction identity along the section:
-- f(σ x') = f 0 + 1/2 σ(x') h(x')² + 1/2 (reduced family at σ x')(x', x').
theorem morseReduction_identity (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x' : MorseModel n} (hx' : morseCons (0 : ℝ) x' ∈ φ.target)
    (hpiv : morsePivot (clmBilin a) (morseSection φ x') ≠ 0) :
    f (morseSection φ x') - f 0 =
      (1 / 2 : ℝ) * SignType.sign (morsePivot (clmBilin a) (morseSection φ x')) *
          (morseSectionHead (clmBilin a) φ x') ^ 2 +
        (1 / 2 : ℝ) * morseReducedFamily (clmBilin a) (morseSection φ x') x' x' := by
  have hsec := morseCriticalSection_eq f φ hφ hx'
  have htail : morseTail (morseSection φ x') = x' := morseSection_tail f φ hφ hx'
  have hhead : morseHead (morseSection φ x') = morseCriticalSection φ x' :=
    morseSection_head_critical f φ hφ hx'
  let b : MorseModel (n + 1) → LinearMap.BilinForm ℝ (MorseModel (n + 1)) := clmBilin a
  have htaylor := second_order_taylor_bilin f hg (morseSection φ x')
  have htaylor' : f (morseSection φ x') - f 0 =
      (morseTaylorBilin f (morseSection φ x')) (morseSection φ x') (morseSection φ x') := by
    rw [htaylor, hcrit]
    simp
  have hquad : (morseTaylorBilin f (morseSection φ x')) (morseSection φ x') (morseSection φ x') =
      (1 / 2 : ℝ) * (a (morseSection φ x') (morseSection φ x') (morseSection φ x')) := by
    rw [ha (morseSection φ x')]
    simp
  have hsym' : ∀ x y z : MorseModel (n + 1), b x y z = b x z y := by
    intro x y z
    simpa [b, clmBilin] using hsym x y z
  have hpiv' : morsePivot b (morseSection φ x') ≠ 0 := by
    simpa [b, clmBilin, morsePivot] using hpiv
  have hcs := morse_complete_square_sqrt b hsym' (morseSection φ x') hpiv'
  have htail' : morseTail (morseSection φ x') = x' := htail
  have hab : a (morseSection φ x') (morseSection φ x') (morseSection φ x') =
      b (morseSection φ x') (morseSection φ x') (morseSection φ x') := by
    simp [b, clmBilin]
  rw [htaylor', hquad, hab, hcs, morseSectionHead]
  rw [htail]
  rw [morseReducedFamily_apply]
  simp [b]
  ring_nf

-- The inverse of the Morse partial derivative preserves tails:
-- for tail vectors the tail is unchanged.
theorem morsePartialDerivCLE_symm_tail {n : ℕ}
    (p' : MorseModel (n + 1) →L[ℝ] ℝ) (h₀ : p' morseE0 ≠ 0) (u : MorseModel n) :
    morseTail ((morsePartialDerivCLE p' h₀).symm (morseCons (0 : ℝ) u)) = u := by
  -- use the explicit preimage from the surjectivity proof
  let v : MorseModel (n + 1) :=
    morseCons ((0 : ℝ) - p' (morseCons (0 : ℝ) u) / p' morseE0) u
  have hpre : morsePartialDeriv p' v = morseCons (0 : ℝ) u := by
    have hlin : p' v = morseHead v * p' morseE0 + p' (morseCons (0 : ℝ) (morseTail v)) := by
      conv_lhs =>
        rw [morse_cons_decompose v, morse_cons_smul' (morseHead v) (morseTail v)]
      simp [map_add, map_smul, smul_eq_mul]
    have hmv : morseHead v = (0 : ℝ) - p' (morseCons (0 : ℝ) u) / p' morseE0 := by
      simp [v, morseHead, morseCons]
    have htv : morseTail v = u := by
      funext j
      simp [v, morseTail, morseCons, Fin.cons_succ]
    funext i
    cases i using Fin.cases with
    | zero =>
        simp [morsePartialDeriv, morseCons, hlin, hmv, htv]
        field_simp [h₀]
        ring_nf
    | succ j =>
        simp [morsePartialDeriv, v, morseTail, morseCons, Fin.cons_succ]
  have hleft : (morsePartialDerivCLE p' h₀).symm (morseCons (0 : ℝ) u) = v := by
    have hcle : morseCons (0 : ℝ) u = (morsePartialDerivCLE p' h₀) v := by
      simpa [morsePartialDerivCLE] using hpre.symm
    exact (morsePartialDerivCLE p' h₀).symm_apply_eq.mpr hcle
  rw [hleft]
  funext j
  simp [v, morseTail, morseCons, Fin.cons_succ]

-- The derivative of the section at 0 preserves the tail:
-- dσ(0) u has tail u.
theorem morseSection_fderiv_tail {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcrit : fderiv ℝ f 0 = 0)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    {u : MorseModel n} (_hu : morseCons (0 : ℝ) u ∈ φ.target) :
    morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u := by
  -- the tail of the section is the identity near 0: morseTail (σ x') = x'
  have htail' : (fun x' : MorseModel n => morseTail (morseSection φ x')) =ᶠ[nhds (0 : MorseModel n)]
      (fun x' : MorseModel n => x') := by
    have hc : Continuous (fun x' : MorseModel n => morseCons (0 : ℝ) x') := by
      have hc' : Continuous (fun p : ℝ × MorseModel n => morseConsLinearCLM p) :=
        morseConsLinearCLM.cont
      exact hc'.comp (continuous_const.prodMk continuous_id)
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hmem : ∀ᶠ y : MorseModel n in nhds (0 : MorseModel n), morseCons (0 : ℝ) y ∈ φ.target := by
      have hφ0 : φ 0 = 0 := by
        have hφm : φ 0 = morsePartialMap f 0 := by rw [hφ]
        rw [hφm]
        funext i
        cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, hcrit, morseCons, morseTail]
      have hφt0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
        rw [← hφ0]
        exact φ.map_source hsrc
      have hnhds : φ.target ∈ nhds (0 : MorseModel (n + 1)) := φ.open_target.mem_nhds hφt0
      have hca : ContinuousAt (fun x' : MorseModel n => morseCons (0 : ℝ) x') (0 : MorseModel n) :=
        hc.continuousAt
      have hnhds' : φ.target ∈ nhds (morseCons (0 : ℝ) (0 : MorseModel n)) := by
        rw [hz]
        exact hnhds
      exact hca.preimage_mem_nhds hnhds'
    filter_upwards [hmem] with y hy
    exact morseSection_tail f φ hφ hy
  -- fderiv of both sides at 0
  have hfd : fderiv ℝ (fun x' : MorseModel n => morseTail (morseSection φ x')) (0 : MorseModel n) =
      fderiv ℝ (fun x' : MorseModel n => x') (0 : MorseModel n) :=
    htail'.fderiv_eq
  -- left: fderiv (morseTail ∘ σ) 0 = morseTailProj.comp (fderiv σ 0) by the chain rule
  have hchain : fderiv ℝ (fun x' : MorseModel n => morseTail (morseSection φ x')) (0 : MorseModel n) =
      (fderiv ℝ morseTail (morseSection φ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ) (0 : MorseModel n)) := by
    have hdt : DifferentiableAt ℝ (morseTail : MorseModel (n + 1) → MorseModel n)
        (morseSection φ (0 : MorseModel n)) := by
      have hdiff : DifferentiableAt ℝ (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)
          (morseSection φ (0 : MorseModel n)) :=
        (morseTailProj.contDiff.contDiffAt (x := morseSection φ (0 : MorseModel n))).differentiableAt
          (by decide : (1 : WithTop ℕ∞) ≠ 0)
      simpa [morseTailProj] using hdiff
    have hsec' : DifferentiableAt ℝ (morseSection φ : MorseModel n → MorseModel (n + 1))
        (0 : MorseModel n) := hdf
    exact fderiv_comp (𝕜 := ℝ) (x := (0 : MorseModel n))
      (g := (morseTail : MorseModel (n + 1) → MorseModel n))
      (f := (morseSection φ : MorseModel n → MorseModel (n + 1))) (hg := hdt) (hf := hsec')
  have hdtailproj : fderiv ℝ morseTail (morseSection φ (0 : MorseModel n)) = morseTailProj := by
    change fderiv ℝ (fun x : MorseModel (n + 1) => morseTailProj x) (morseSection φ (0 : MorseModel n)) =
      morseTailProj
    exact (morseTailProj.hasFDerivAt).fderiv
  have hid : fderiv ℝ (fun x' : MorseModel n => x') (0 : MorseModel n) = (1 : MorseModel n →L[ℝ] MorseModel n) := by
    exact (hasFDerivAt_id (x := (0 : MorseModel n))).fderiv
  -- apply to u
  have happ : (morseTailProj.comp (fderiv ℝ (morseSection φ) (0 : MorseModel n))) u = u := by
    rw [← hdtailproj]
    rw [← hchain, hfd, hid]
    simp
  simpa [ContinuousLinearMap.comp_apply] using happ

-- The completed-square head coordinate at the origin vanishes on the section derivative:
-- h₀(dσ(0) u) = 0, where h₀(x) = head x + cross₀(tail x)/p₀.
-- This follows from differentiating morsePartial f (σ x') = 0 at 0.
theorem morseSection_fderiv_complete {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (_a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcrit : fderiv ℝ f 0 = 0)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    {u : MorseModel n} (_hu : morseCons (0 : ℝ) u ∈ φ.target) :
    (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
      (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = 0 := by
  -- morsePartial f (σ x') = 0 near 0
  have hsec : (fun x' : MorseModel n => morsePartial f (morseSection φ x')) =ᶠ[nhds (0 : MorseModel n)]
      (fun _ : MorseModel n => 0) := by
    have hφ0 : φ 0 = 0 := by
      have hφm : φ 0 = morsePartialMap f 0 := by rw [hφ]
      rw [hφm]
      funext i
      cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, hcrit, morseCons, morseTail]
    have hφt0 : (0 : MorseModel (n + 1)) ∈ φ.target := by
      rw [← hφ0]
      exact φ.map_source hsrc
    have hnhds : φ.target ∈ nhds (0 : MorseModel (n + 1)) := φ.open_target.mem_nhds hφt0
    have hc : Continuous (fun x' : MorseModel n => morseCons (0 : ℝ) x') := by
      have hc' : Continuous (fun p : ℝ × MorseModel n => morseConsLinearCLM p) :=
        morseConsLinearCLM.cont
      exact hc'.comp (continuous_const.prodMk continuous_id)
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hca : ContinuousAt (fun x' : MorseModel n => morseCons (0 : ℝ) x') (0 : MorseModel n) :=
      hc.continuousAt
    have hnhds' : φ.target ∈ nhds (morseCons (0 : ℝ) (0 : MorseModel n)) := by
      rw [hz]
      exact hnhds
    have hmem : ∀ᶠ y : MorseModel n in nhds (0 : MorseModel n), morseCons (0 : ℝ) y ∈ φ.target :=
      hca.preimage_mem_nhds hnhds'
    filter_upwards [hmem] with y hy
    have hsec' : morsePartial f (morseSection φ y) = 0 := by
      have htail' : morseTail (morseSection φ y) = y := morseSection_tail f φ hφ hy
      have hhead' : morseHead (morseSection φ y) = morseCriticalSection φ y :=
        morseSection_head_critical f φ hφ hy
      have hdec : morseSection φ y = morseCons (morseCriticalSection φ y) y := by
        rw [morse_cons_decompose (morseSection φ y)]
        rw [hhead']
        exact congrArg (morseCons (morseCriticalSection φ y)) htail'
      rw [hdec]
      exact morseCriticalSection_eq f φ hφ hy
    exact hsec'
  -- differentiate at 0
  have hfd : fderiv ℝ (fun x' : MorseModel n => morsePartial f (morseSection φ x')) (0 : MorseModel n) =
      fderiv ℝ (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) :=
    hsec.fderiv_eq
  have hchain' : fderiv ℝ (fun x' : MorseModel n => morsePartial f (morseSection φ x')) (0 : MorseModel n) =
      (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))).comp
        (fderiv ℝ (morseSection φ) (0 : MorseModel n)) := by
    exact fderiv_comp (𝕜 := ℝ) (x := (0 : MorseModel n))
      (g := (morsePartial f : MorseModel (n + 1) → ℝ))
      (f := (morseSection φ : MorseModel n → MorseModel (n + 1)))
      (hg := hdfp) (hf := hdf)
  have hzero : fderiv ℝ (fun _ : MorseModel n => (0 : ℝ)) (0 : MorseModel n) = 0 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) (x := (0 : MorseModel n)) (c := (0 : ℝ))).fderiv
  have happ' : ((fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))).comp
      (fderiv ℝ (morseSection φ) (0 : MorseModel n))) u = 0 := by
    rw [← hchain', hfd, hzero]
    simp
  simpa [ContinuousLinearMap.comp_apply] using happ'

-- The derivative of the Morse partial function at 0 evaluates to the Hessian
-- applied to the e0 direction.
theorem fderiv_morsePartial_e0 {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f) :
    ⇑(fderiv ℝ (morsePartial f) 0) =
      (fun w : MorseModel (n + 1) => (fderiv ℝ (fderiv ℝ f) 0) w morseE0) := by
  rw [show (⇑(fderiv ℝ (morsePartial f) 0)) =
      ⇑(fderiv ℝ (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0) 0) by rfl]
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Set.univ := by
    exact hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hc : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x)
      (fderiv ℝ (fderiv ℝ f) 0) 0 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
      ((h1 0 (Set.mem_univ _)).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
    exact hd.hasFDerivAt
  have hcst : HasFDerivAt (fun _ : MorseModel (n + 1) => morseE0) 0 0 :=
    hasFDerivAt_const (𝕜 := ℝ) (x := (0 : MorseModel (n + 1))) (c := (morseE0 : MorseModel (n + 1)))
  have hca' : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0)
      ((fderiv ℝ f 0).comp (0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) +
        (fderiv ℝ (fderiv ℝ f) 0).flip morseE0) 0 :=
    hc.clm_apply hcst
  have hkill : (fderiv ℝ f 0).comp (0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) = 0 := by
    ext w
    simp
  have hca : HasFDerivAt (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0)
      ((fderiv ℝ (fderiv ℝ f) 0).flip morseE0) 0 := by
    simpa [hkill] using hca'
  have hd : fderiv ℝ (fun x : MorseModel (n + 1) => fderiv ℝ f x morseE0) 0 =
      (fderiv ℝ (fderiv ℝ f) 0).flip morseE0 := hca.fderiv
  rw [hd]
  funext w
  exact (ContinuousLinearMap.flip_apply (fderiv ℝ (fderiv ℝ f) 0) w morseE0).symm

-- A symmetric bilinear form evaluated on vectors whose completed head vanishes
-- reduces to the Schur-complement form on the tails.
theorem bilin_completed_head_zero {n : ℕ}
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    {x y : MorseModel (n + 1)}
    (hx : morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
        (clmBilin a 0 morseE0 morseE0) = 0)
    (hy : morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
        (clmBilin a 0 morseE0 morseE0) = 0) :
    a 0 x y = morseReducedFamily (clmBilin a) 0 (morseTail x) (morseTail y) := by
  have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
    dsimp [morsePivot, clmBilin]
    exact hpiv
  have hcrossx : (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) =
      -(morseHead x) * (clmBilin a 0 morseE0 morseE0) := by
    have hmul : (morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
        (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) = 0 := by
      rw [hx, zero_mul]
    have hrel : morseHead x * (clmBilin a 0 morseE0 morseE0) +
        (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) = 0 := by
      have hmm : (morseHead x + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) /
          (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) =
          morseHead x * (clmBilin a 0 morseE0 morseE0) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail x))) hpiv']
      rwa [hmm] at hmul
    linarith
  have hcrossy : (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) =
      -(morseHead y) * (clmBilin a 0 morseE0 morseE0) := by
    have hmul : (morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
        (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) = 0 := by
      rw [hy, zero_mul]
    have hrel : morseHead y * (clmBilin a 0 morseE0 morseE0) +
        (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) = 0 := by
      have hmm : (morseHead y + (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) /
          (clmBilin a 0 morseE0 morseE0)) * (clmBilin a 0 morseE0 morseE0) =
          morseHead y * (clmBilin a 0 morseE0 morseE0) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail y))) hpiv']
      rwa [hmm] at hmul
    linarith
  have hxdec : x = morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x) := by
    conv_lhs =>
      rw [morse_cons_decompose x]
    rw [morse_cons_smul' (morseHead x) (morseTail x)]
  have hydec : y = morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y) := by
    conv_lhs =>
      rw [morse_cons_decompose y]
    rw [morse_cons_smul' (morseHead y) (morseTail y)]
  rw [hxdec, hydec]
  let F : MorseModel (n + 1) →L[ℝ] ℝ :=
    morseHead x • (a 0) morseE0 + (a 0) (morseCons (0 : ℝ) (morseTail x))
  have hF : (a 0) (morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x)) = F := by
    rw [map_add (a 0), map_smul (a 0)]
  rw [hF]
  have hadd : F (morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y)) =
      F (morseHead y • morseE0) + F (morseCons (0 : ℝ) (morseTail y)) :=
    map_add F (morseHead y • morseE0) (morseCons (0 : ℝ) (morseTail y))
  have hsmul : F (morseHead y • morseE0) = morseHead y • F morseE0 :=
    map_smul F (morseHead y) morseE0
  rw [hadd, hsmul]
  have hFe0 : F morseE0 = morseHead x • (a 0 morseE0 morseE0) + (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 := by
    dsimp [F]
  have hFtail : F (morseCons (0 : ℝ) (morseTail y)) =
      morseHead x • (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) +
        (a 0) (morseCons (0 : ℝ) (morseTail x)) (morseCons (0 : ℝ) (morseTail y)) := by
    dsimp [F]
  rw [hFe0, hFtail]
  -- symmetrize the cross terms before simplifying the tails
  have hsymCLM0 : ∀ z w, (a 0) z w = (a 0) w z := by
    intro z w
    exact hsym 0 z w
  -- both cross terms should have morseE0 on the left
  rw [← hsymCLM0 morseE0 (morseCons (0 : ℝ) (morseTail x))]
  rw [hsymCLM0 morseE0 (morseCons (0 : ℝ) (morseTail y))]
  -- simplify the tails on the RHS
  have htailx' : morseTail (morseHead x • morseE0 + morseCons (0 : ℝ) (morseTail x)) = morseTail x := by
    rw [← morse_cons_smul' (morseHead x) (morseTail x)]
    exact morseCons_tail (morseHead x) (morseTail x)
  have htainly' : morseTail (morseHead y • morseE0 + morseCons (0 : ℝ) (morseTail y)) = morseTail y := by
    rw [← morse_cons_smul' (morseHead y) (morseTail y)]
    exact morseCons_tail (morseHead y) (morseTail y)
  rw [htailx', htainly']
  have hcrossxCLM : (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 =
      -(morseHead x) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) (morseCons (0 : ℝ) (morseTail x)) morseE0 = (a 0) morseE0 (morseCons (0 : ℝ) (morseTail x)) :=
      hsym 0 (morseCons (0 : ℝ) (morseTail x)) morseE0
    rw [hswap]
    simpa [clmBilin] using hcrossx
  have hcrossyCLM : (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 =
      -(morseHead y) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 = (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) :=
      hsym 0 (morseCons (0 : ℝ) (morseTail y)) morseE0
    rw [hswap]
    simpa [clmBilin] using hcrossy
  -- the x-cross term is now in the form (a 0) morseE0 (cons 0 (tail x)); rewrite it directly
  have hcrossx0 : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail x)) = -(morseHead x) * (a 0 morseE0 morseE0) := by
    simpa [clmBilin] using hcrossx
  rw [hcrossx0]
  rw [hcrossyCLM]
  rw [morseReducedFamily_apply]
  simp [clmBilin]
  -- simplify the RHS cross term
  rw [hcrossxCLM]
  have hcrossy0 : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) = -(morseHead y) * (a 0 morseE0 morseE0) := by
    have hswap : (a 0) morseE0 (morseCons (0 : ℝ) (morseTail y)) = (a 0) (morseCons (0 : ℝ) (morseTail y)) morseE0 :=
      hsym 0 morseE0 (morseCons (0 : ℝ) (morseTail y))
    rw [hswap]
    exact hcrossyCLM
  simp [hcrossy0]
  have hpiv2 : morsePivot (clmBilin a) 0 = (a 0 morseE0 morseE0) := rfl
  simp [hpiv2]
  field_simp [hpiv']
  ring_nf

-- The Hessian of the reduced function f₁(x') = f(σ x') at 0 is the reduced family at 0.
theorem hessian_morseReducedFn (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (ha : ∀ x, a x = 2 • morseTaylorBilin f x)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcont : ContDiff ℝ 2 (morseSection φ))
    (u v : MorseModel n)
    (hu : morseCons (0 : ℝ) u ∈ φ.target) (hv : morseCons (0 : ℝ) v ∈ φ.target) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (morseSection φ x'))) (0 : MorseModel n)) u v =
      morseReducedFamily (clmBilin a) 0 u v := by
  -- pullback lemma
  have hpull := hessian_pullback_at_critical f (morseSection φ) hg hcont
    (morseSection_zero f φ hφ hcrit hsrc) hcrit u v
  -- completed-square identity at 0
  have hcs := morse_complete_square_sqrt (clmBilin a) (by
    intro x y z
    simpa [clmBilin] using hsym x y z) (0 : MorseModel (n + 1)) (by
      simpa [morsePivot, clmBilin] using hpiv)
  -- the section derivative kills the completed-square head term
  have hmain : (fun w : MorseModel (n + 1) =>
      (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n))) w) =
      fun w : MorseModel (n + 1) => (clmBilin a 0) morseE0 w := by
    have hσ0 : morseSection φ (0 : MorseModel n) = 0 :=
      morseSection_zero f φ hφ hcrit hsrc
    rw [hσ0]
    have hfd0 := fderiv_morsePartial_e0 (n := n) f hg
    funext w
    have hw : (fderiv ℝ (fderiv ℝ f) 0) w morseE0 = clmBilin a 0 morseE0 w := by
      have ha0 : a 0 = 2 • morseTaylorBilin f 0 := ha 0
      have htb : morseTaylorBilin f 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
        morseTaylorBilin_zero f
      have h2 : (fderiv ℝ (fderiv ℝ f) 0) w morseE0 = a 0 morseE0 w := by
        have hsymw : a 0 morseE0 w = a 0 w morseE0 := (hsym 0 w morseE0).symm
        rw [hsymw, ha0, htb]
        simp [smul_eq_mul]
      simpa [clmBilin] using h2
    exact (congrFun hfd0 w).trans hw
  have hhead : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
      (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))) /
        morsePivot (clmBilin a) 0) = 0 := by
    have hp0 : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
        (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = 0 :=
      morseSection_fderiv_complete f a φ hφ hsrc hcrit hdf hdfp hu
    have happ0 : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) = 0 := by
      have hpt : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
          (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) =
          (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) := by
        exact congrFun hmain (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
      exact hpt.symm.trans hp0
    -- decompose fderiv σ 0 u = morseCons h t with t = u
    have ht : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u :=
      morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hu
    have hdec : fderiv ℝ (morseSection φ) (0 : MorseModel n) u =
        morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u := by
      rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)]
      exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))) ht
    -- happ0 gives head * pivot + cross = 0, hence head + cross / pivot = 0
    have hh0' : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) = 0 := happ0
    have hcross : clmBilin a 0 morseE0
        (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) • morseE0 + morseCons (0 : ℝ) u) =
        morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) * (clmBilin a 0 morseE0 morseE0) +
          clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) := by
      rw [map_add, map_smul]
      simp [smul_eq_mul]
    have hmain0 : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) *
          (clmBilin a 0 morseE0 morseE0) +
        clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) = 0 := by
      rw [hdec, morse_cons_smul' (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u] at hh0'
      rw [hcross] at hh0'
      exact hh0'
    have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
      simpa [clmBilin, morsePivot] using hpiv
    have hdiv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
        clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) / (clmBilin a 0 morseE0 morseE0) = 0 := by
      have hmul : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
          clmBilin a 0 morseE0 (morseCons (0 : ℝ) u) / (clmBilin a 0 morseE0 morseE0)) *
          (clmBilin a 0 morseE0 morseE0) = 0 := by
        rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) u)) hpiv']
        exact hmain0
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right hpiv'
    simpa [ht] using hdiv
  rw [hpull]
  -- completed-square identity at 0 applied to x = dσ(0)u, y = dσ(0)v
  have ht' : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u :=
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hu
  have ht'' : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) = v :=
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hv
  -- hcs is the completed-square identity at 0; use its polarization on x,y
  have hsq : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
      (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
      morseReducedFamily (clmBilin a) 0 u v := by
    -- derive from the quadratic identity by polarization or by direct expansion
    -- using the bilinear decomposition d²f(0)(x,y) = head-part + reduced part
    have hdecomp : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
          (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
        (morseReducedFamily (clmBilin a) 0 (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))
          (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v))) := by
      -- The completed-square identity at 0 (quadratic form version) is
      -- Q(x) = s·h(x)² + R(tail x, tail x); polarizing with h(x)=h(y)=0 gives
      -- B(x,y) = R(tail x, tail y).  We use the bilinear form directly:
      -- B(x,y) = (B(x+y,x+y) - B(x-y,x-y))/4 by symmetry.
      have hxy : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
          (morseReducedFamily (clmBilin a) 0 u v) := by
        -- completed-square identity at 0 in the CLM form:
        -- a0(x,x) = sign(p)·h₀(x)² + Rfam0(tail x, tail x), where
        -- h₀(x) = head x + a0(e0, tail x)/p, and h₀(dσ(0)u) = 0 by hhead.
        -- Polarizing: a0(x,y) = Rfam0(tail x, tail y) when h₀(x) = h₀(y) = 0.
        have ha0 : ∀ x y, (fderiv ℝ (fderiv ℝ f) 0) x y = (clmBilin a 0) x y := by
          intro x y
          have hx : (fderiv ℝ (fderiv ℝ f) 0) x y = a 0 x y := by
            rw [ha 0, morseTaylorBilin_zero f]
            simp [smul_eq_mul]
          rw [hx]
          rfl
        -- h₀(dσ(0)u) = 0 and h₀(dσ(0)v) = 0 by hhead
        have hhu : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))) /
              morsePivot (clmBilin a) 0 = 0 := by
          simpa [ht'] using hhead
        have hhv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
            (clmBilin a 0 morseE0 (morseCons (0 : ℝ) (morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))) /
              morsePivot (clmBilin a) 0 = 0 := by
          -- hhead restated for v: repeat the same proof with v
          have hp0v := morseSection_fderiv_complete f a φ hφ hsrc hcrit hdf hdfp hv
          have hptv : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
              (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
              (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) :=
            congrFun hmain (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)
          have hhapp0v : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) = 0 :=
            hptv.symm.trans hp0v
          have hdv : fderiv ℝ (morseSection φ) (0 : MorseModel n) v =
              morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v := by
            rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
            exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))
              (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hv)
          have hh0v : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) = 0 := hhapp0v
          rw [hdv, morse_cons_smul' (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v] at hh0v
          rw [map_add, map_smul] at hh0v
          have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
            simpa [clmBilin, morsePivot] using hpiv
          have hmain0v : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) *
                (clmBilin a 0 morseE0 morseE0) +
              clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) = 0 := by
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hh0v
          have hdivv : morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
              clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) / (clmBilin a 0 morseE0 morseE0) = 0 := by
            have hmulv : (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) +
                clmBilin a 0 morseE0 (morseCons (0 : ℝ) v) / (clmBilin a 0 morseE0 morseE0)) *
                (clmBilin a 0 morseE0 morseE0) = 0 := by
              rw [add_mul, div_mul_cancel₀ (clmBilin a 0 morseE0 (morseCons (0 : ℝ) v)) hpiv']
              exact hmain0v
            exact (eq_zero_or_eq_zero_of_mul_eq_zero hmulv).resolve_right hpiv'
          simpa [ht''] using hdivv
        -- expand the bilinear form via the completed-square decomposition
        -- B(x,y) = s·h₀(x)·h₀(y) + Rfam0(tail x, tail y)
        have hdu : fderiv ℝ (morseSection φ) (0 : MorseModel n) u =
            morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) u := by
          rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)]
          exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)))
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hu)
        have hdv : fderiv ℝ (morseSection φ) (0 : MorseModel n) v =
            morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v := by
          rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
          exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf hv)
        have hbhz := bilin_completed_head_zero a hsym hpiv hhu hhv
        rw [ha0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
        change ((clmBilin a 0) (fderiv ℝ (morseSection φ) (0 : MorseModel n) u))
            (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) =
          morseReducedFamily (clmBilin a) 0 u v
        simpa [clmBilin, ht', ht''] using hbhz
      simpa [ht', ht''] using hxy
    rw [hdecomp, ht', ht'']
  exact hsq

-- The reduced family at 0 is nondegenerate when the full Hessian is and the pivot is nonzero.
theorem morseReducedFamily_separating (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (hsym : ∀ x y z, a x y z = a x z y)
    (hpiv : morsePivot (clmBilin a) 0 ≠ 0)
    (hsep : (QuadraticMap.associated (R := ℝ) (clmBilin a 0).toQuadraticMap).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (morseReducedFamily (clmBilin a) 0).toQuadraticMap).SeparatingLeft := by
  unfold LinearMap.SeparatingLeft
  intro u hu
  have hu' : ∀ v : MorseModel n, morseReducedFamily (clmBilin a) 0 u v = 0 := by
    intro v
    -- hu : (associated (morseReducedFamily ...).toQuadraticMap) u v = 0
    -- and associated B.toQuadraticMap = B for symmetric B
    have hmain : (QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)) u v =
        morseReducedFamily (clmBilin a) 0 u v := by
      rw [QuadraticMap.associated_apply]
      -- Q(z) = B z z; expand Q(u+v) - Q u - Q v
      have hq : (morseReducedFamily (clmBilin a) 0) (u + v) (u + v) -
          (morseReducedFamily (clmBilin a) 0) u u -
          (morseReducedFamily (clmBilin a) 0) v v =
          2 * (morseReducedFamily (clmBilin a) 0) u v := by
        have hsym' : ∀ x y, (morseReducedFamily (clmBilin a) 0) x y =
            (morseReducedFamily (clmBilin a) 0) y x :=
          morseReducedFamily_sym (clmBilin a) (by
            intro x y z
            simpa [clmBilin] using hsym x y z) 0
        simp [map_add, hsym']
        ring_nf
      have hinv : (⅟(2 : ℝ) : ℝ) * (2 * (morseReducedFamily (clmBilin a) 0) u v) =
          morseReducedFamily (clmBilin a) 0 u v := by
        norm_num
        ring
      simpa [hq, hinv, smul_eq_mul] using (show (⅟(2 : ℝ) : ℝ) *
        ((morseReducedFamily (clmBilin a) 0) (u + v) (u + v) -
          (morseReducedFamily (clmBilin a) 0) u u -
          (morseReducedFamily (clmBilin a) 0) v v) =
        morseReducedFamily (clmBilin a) 0 u v by
          rw [hq]
          exact hinv)
    have hu'' : (QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)) u v = 0 :=
      hu v
    rwa [hmain] at hu''
  -- the Schur-complement witness: w = cons 0 u − (cross_u / p) • e0
  let cross_u : ℝ := (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u)
  let w : MorseModel (n + 1) := morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0
  have hpiv' : (clmBilin a 0 morseE0 morseE0) ≠ 0 := by
    simpa [morsePivot] using hpiv
  -- (clmBilin a 0) w z = 0 for all z
  have hfull : ∀ z : MorseModel (n + 1), (clmBilin a 0) w z = 0 := by
    intro z
    have hz : z = morseHead z • morseE0 + morseCons (0 : ℝ) (morseTail z) := by
      calc
        z = morseCons (morseHead z) (morseTail z) := morse_cons_decompose z
        _ = morseHead z • morseE0 + morseCons (0 : ℝ) (morseTail z) :=
          morse_cons_smul' (morseHead z) (morseTail z)
    -- (clmBilin a 0) w vanishes on e0 and on tails
    have hwe0 : (clmBilin a 0) w morseE0 = 0 := by
      dsimp [w, cross_u]
      have h1 : (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
          (clmBilin a 0) (morseCons (0 : ℝ) u) -
            (cross_u / (clmBilin a 0 morseE0 morseE0)) • (clmBilin a 0) morseE0 := by
        rw [map_sub, map_smul]
      rw [h1]
      change (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 -
        (cross_u / (clmBilin a 0 morseE0 morseE0)) •
          (clmBilin a 0) morseE0 morseE0 = 0
      have hcu' : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = cross_u := by
        dsimp [cross_u]
        exact hsym 0 (morseCons (0 : ℝ) u) morseE0
      rw [hcu']
      simp [smul_eq_mul]
      field_simp [hpiv']
      ring
    have hwt : ∀ v : MorseModel n, (clmBilin a 0) w (morseCons (0 : ℝ) v) = 0 := by
      intro v
      dsimp [w, cross_u]
      have h1 : (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
          (clmBilin a 0) (morseCons (0 : ℝ) u) -
            (cross_u / (clmBilin a 0 morseE0 morseE0)) • (clmBilin a 0) morseE0 := by
        rw [map_sub, map_smul]
      change (clmBilin a 0) (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0)
          (morseCons (0 : ℝ) v) = 0
      rw [h1]
      change (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) -
        (cross_u / (clmBilin a 0 morseE0 morseE0)) •
          (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) = 0
      -- Rfam0(u, v) = 0 gives the tail identity
      have hru := hu' v
      have hfam : (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) =
          (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) *
            (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) /
              (clmBilin a 0 morseE0 morseE0) := by
        have hru' : morseReducedFamily (clmBilin a) 0 u v = 0 := hru
        rw [morseReducedFamily_apply] at hru'
        have hsym0 : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 =
            (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) :=
          hsym 0 (morseCons (0 : ℝ) u) morseE0
        rw [hsym0] at hru'
        have hpiv2 : morsePivot (clmBilin a) 0 = (clmBilin a 0 morseE0 morseE0) := rfl
        rw [hpiv2] at hru'
        linear_combination hru'
      rw [hfam]
      have hcu' : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = (clmBilin a 0) morseE0 (morseCons (0 : ℝ) u) :=
        hsym 0 (morseCons (0 : ℝ) u) morseE0
      simp [smul_eq_mul]
      field_simp [hpiv']
      ring
    -- combine: z = head • e0 + cons 0 (tail z)
    rw [hz]
    rw [map_add, map_smul]
    rw [hwe0, hwt]
    simp
  have hzero : w = 0 := by
    apply hsep
    intro z
    -- hsep uses the associated bilinear map; for symmetric clmBilin a 0 the
    -- associated form agrees up to a scalar with clmBilin a 0.
    have hz : (QuadraticMap.associated (R := ℝ) ((clmBilin a 0).toQuadraticMap)) w z =
        (clmBilin a 0) w z := by
      rw [QuadraticMap.associated_apply]
      have hsym0 : ∀ x y, (clmBilin a 0) x y = (clmBilin a 0) y x := by
        intro x y
        simpa [clmBilin] using hsym 0 x y
      simp [map_add, hsym0]
      ring_nf
    rw [hz]
    exact hfull z
  -- w = 0 forces u = 0 (tails of w and of cons 0 u agree)
  have htailw : morseTail w = morseTail (morseCons (0 : ℝ) u) := by
    change morseTail (morseCons (0 : ℝ) u - (cross_u / (clmBilin a 0 morseE0 morseE0)) • morseE0) =
      morseTail (morseCons (0 : ℝ) u)
    have hlin : ∀ x y : MorseModel (n + 1), morseTail (x - y) = morseTail x - morseTail y := by
      intro x y
      calc
        morseTail (x - y) = morseTail (x + (-1 : ℝ) • y) := by
          rw [sub_eq_add_neg]
          rw [← neg_one_smul ℝ y]
        _ = morseTail x + morseTail ((-1 : ℝ) • y) := morseTail_add x ((-1 : ℝ) • y)
        _ = morseTail x + (-1 : ℝ) • morseTail y := by
          rw [morseTail_smul (-1 : ℝ) y]
        _ = morseTail x - morseTail y := by
          simp [sub_eq_add_neg]
    rw [hlin]
    rw [morseTail_smul]
    have htailE0 : morseTail morseE0 = (0 : MorseModel n) := by
      funext i
      simp [morseTail, morseE0]
    rw [htailE0]
    simp [morseCons_tail]
  have htail0 : morseTail w = u := by
    rw [htailw]
    exact morseCons_tail (0 : ℝ) u
  have hu0 : u = 0 := by
    rw [← htail0]
    exact congrArg morseTail hzero
  exact hu0

end Completion

end DifferentialGeometry.Topology.Morse
