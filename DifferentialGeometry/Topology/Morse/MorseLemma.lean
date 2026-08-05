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
    {u : MorseModel n} :
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
    {u : MorseModel n} :
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
    (u v : MorseModel n) :
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
      morseSection_fderiv_complete f a φ hφ hsrc hcrit hdf hdfp
    have happ0 : (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) = 0 := by
      have hpt : (fderiv ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
          (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) =
          (clmBilin a 0 morseE0 (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)) := by
        exact congrFun hmain (fderiv ℝ (morseSection φ) (0 : MorseModel n) u)
      exact hpt.symm.trans hp0
    -- decompose fderiv σ 0 u = morseCons h t with t = u
    have ht : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) u) = u :=
      morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
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
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
  have ht'' : morseTail (fderiv ℝ (morseSection φ) (0 : MorseModel n) v) = v :=
    morseSection_fderiv_tail f φ hφ hsrc hcrit hdf
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
          have hp0v := morseSection_fderiv_complete (u := v) f a φ hφ hsrc hcrit hdf hdfp
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
              (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
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
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
        have hdv : fderiv ℝ (morseSection φ) (0 : MorseModel n) v =
            morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)) v := by
          rw [morse_cons_decompose (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)]
          exact congrArg (morseCons (morseHead (fderiv ℝ (morseSection φ) (0 : MorseModel n) v)))
            (morseSection_fderiv_tail f φ hφ hsrc hcrit hdf)
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

theorem morseReducedFn_nondegenerate (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
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
    (hsep : (QuadraticMap.associated (R := ℝ) (chartHessianAt f 0)).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (fun x' : MorseModel n => f (morseSection φ x')) 0)).SeparatingLeft := by
  have hbilin0 : chartHessianBilinAt f 0 = (clmBilin a 0) := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have hA : a 0 = fderiv ℝ (fderiv ℝ f) 0 := by
      rw [ha 0, morseTaylorBilin_zero f]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      simp [smul_eq_mul]
    simp [chartHessianBilinAt, clmBilin, hA]
  have hchart : chartHessianAt f 0 = (clmBilin a 0).toQuadraticMap := by
    change (chartHessianBilinAt f 0).toQuadraticMap = (clmBilin a 0).toQuadraticMap
    rw [hbilin0]
  have hsepFull : (QuadraticMap.associated (R := ℝ) ((clmBilin a 0).toQuadraticMap)).SeparatingLeft := by
    rw [← hchart]
    exact hsep
  have hsepRed := morseReducedFamily_separating a hsym hpiv hsepFull
  have hbilin : chartHessianBilinAt (fun x' : MorseModel n => f (morseSection φ x')) 0 =
      morseReducedFamily (clmBilin a) 0 := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simpa [chartHessianBilinAt] using
      (hessian_morseReducedFn f hg hcrit a ha hsym hpiv φ hφ hsrc hdf hdfp hcont u v)
  have hQ : QuadraticMap.associated (R := ℝ)
        (chartHessianAt (fun x' : MorseModel n => f (morseSection φ x')) 0) =
      QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap) := by
    change QuadraticMap.associated (R := ℝ)
        ((chartHessianBilinAt (fun x' : MorseModel n => f (morseSection φ x')) 0).toQuadraticMap) =
      QuadraticMap.associated (R := ℝ) ((morseReducedFamily (clmBilin a) 0).toQuadraticMap)
    rw [hbilin]
  rwa [hQ]

theorem section_second_order (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x : MorseModel (n + 1)} (hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ.target) :
    f x - f (morseSection φ (morseTail x)) =
      (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 *
        (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0 morseE0 := by
  let σ : MorseModel (n + 1) := morseSection φ (morseTail x)
  let d : ℝ := morseHead x - morseCriticalSection φ (morseTail x)
  have hlin := second_order_taylor_bilin_at f hg σ x
  have hx : x = morseCons (morseHead x) (morseTail x) := morse_cons_decompose x
  have hσ : σ = morseCons (morseCriticalSection φ (morseTail x)) (morseTail x) := by
    dsimp [σ]
    rw [morse_cons_decompose (morseSection φ (morseTail x))]
    rw [morseSection_head_critical f φ hφ (x' := morseTail x) hx']
    rw [morseSection_tail f φ hφ hx']
  have hsub : ∀ (a b : ℝ) (t : MorseModel n),
      morseCons a t - morseCons b t = morseCons (a - b) (0 : MorseModel n) := by
    intro a b t
    calc
      morseCons a t - morseCons b t = morseCons a t + (-1 : ℝ) • morseCons b t := by
        simp [sub_eq_add_neg]
      _ = morseCons a t + morseCons (-b) ((-1 : ℝ) • t) := by
        rw [← morseCons_smul (-1 : ℝ) b t]
        simp
      _ = morseCons (a - b) (0 : MorseModel n) := by
        rw [← morseCons_add a (-b) t ((-1 : ℝ) • t)]
        simp [sub_eq_add_neg]
  have hvec : x - σ = d • morseE0 := by
    rw [hx, hσ]
    rw [hsub (morseHead x) (morseCriticalSection φ (morseTail x)) (morseTail x)]
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    have hsmul : morseCons d (0 : MorseModel n) = d • morseE0 := by
      rw [morse_cons_smul' d (0 : MorseModel n)]
      simp [hz]
    simpa [d] using hsmul
  have hfd : (fderiv ℝ f σ) (x - σ) = 0 := by
    rw [hvec]
    have hp : (fderiv ℝ f σ) morseE0 = 0 := by
      have hσ' : σ = morseCons (morseCriticalSection φ (morseTail x)) (morseTail x) := hσ
      rw [hσ']
      have hp' := morseCriticalSection_eq f φ hφ hx'
      simpa [morsePartial] using hp'
    rw [map_smul]
    simp [hp, smul_eq_mul]
  have hquad : (morseTaylorBilinAt f σ x) (x - σ) (x - σ) =
      d ^ 2 * (morseTaylorBilinAt f σ x) morseE0 morseE0 := by
    rw [hvec]
    simp [map_smul, smul_eq_mul]
    ring
  rw [hfd, hquad] at hlin
  simpa [σ, d] using hlin

theorem hessian_diagonal_pivot {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    (fderiv ℝ (fderiv ℝ f) 0) morseE0 morseE0 = w 0 := by
  have h := hdiag morseE0 morseE0
  have hsum : (∑ i : Fin (n + 1), w i * morseE0 i * morseE0 i) = w 0 := by
    rw [Fin.sum_univ_succ]
    simp [morseE0]
  simpa [hsum] using h

theorem hessian_diagonal_reduced {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
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
    (w : Fin (n + 1) → ℝ)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (u v : MorseModel n) :
    (fderiv ℝ (fderiv ℝ (fun x' : MorseModel n => f (morseSection φ x'))) (0 : MorseModel n)) u v =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
  rw [hessian_morseReducedFn f hg hcrit a ha hsym hpiv φ hφ hsrc hdf hdfp hcont u v]
  have hclm : ∀ u v : MorseModel (n + 1), (clmBilin a 0) u v = (a 0 u) v := by
    intro u v
    rfl
  have hA : a 0 = fderiv ℝ (fderiv ℝ f) 0 := by
    rw [ha 0, morseTaylorBilin_zero f]
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp [smul_eq_mul]
  have hcross1 : (clmBilin a 0) (morseCons (0 : ℝ) u) morseE0 = 0 := by
    rw [hclm]
    have hd := hdiag (morseCons (0 : ℝ) u) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (morseCons (0 : ℝ) u) i * morseE0 i) = 0 := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseCons]
    rw [hA]
    rw [hd, hsum]
  have hcross2 : (clmBilin a 0) morseE0 (morseCons (0 : ℝ) v) = 0 := by
    rw [hclm]
    have hswap : (a 0) morseE0 (morseCons (0 : ℝ) v) = (a 0) (morseCons (0 : ℝ) v) morseE0 :=
      hsym 0 morseE0 (morseCons (0 : ℝ) v)
    rw [hswap]
    have hd := hdiag (morseCons (0 : ℝ) v) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (morseCons (0 : ℝ) v) i * morseE0 i) = 0 := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseCons]
    rw [hA]
    rw [hd, hsum]
  have hmain : (clmBilin a 0) (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v) =
      ∑ j : Fin n, w (Fin.succ j) * u j * v j := by
    rw [hclm]
    rw [hA]
    rw [hdiag (morseCons (0 : ℝ) u) (morseCons (0 : ℝ) v)]
    rw [Fin.sum_univ_succ]
    simp [morseCons]
  rw [morseReducedFamily_apply]
  rw [hcross1, hcross2]
  simp [hmain]

noncomputable def morseSectionB (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : ℝ :=
  (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0 morseE0

noncomputable def morseSectionCompletion (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (x : MorseModel (n + 1)) : MorseModel (n + 1) :=
  morseCons (Real.sqrt (2 * |morseSectionB f φ x|) *
      (morseHead x - morseCriticalSection φ (morseTail x))) (morseTail x)

theorem contDiffAt_morseSectionB {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n)) :
    ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
  have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hσtail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    simpa using (ContDiffAt.comp 0 hcontσ htail)
  have hg : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail (contDiffAt_id : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    simpa using (morseSection_zero f φ hφ hcrit hsrc : morseSection φ (0 : MorseModel n) = 0)
  have hfam : ContDiffAt ℝ 1 (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
      morseTaylorBilinAt f p.1 p.2) (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt f hf 0 0
  have hfam' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    simpa [hσ0] using
      (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg))
  have happly : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      (morseTaylorBilinAt f (morseSection φ (morseTail x)) x) morseE0) 0 :=
    hfam'.clm_apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0)
  simpa [morseSectionB] using
    (happly.clm_apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => morseE0) 0))

theorem contDiffAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ContDiffAt ℝ 1 (morseSectionCompletion f φ) 0 := by
  have htail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseTail x) 0 := by
    simpa [morseTail, morseTailProj] using
      ((morseTailProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseTailProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hσtail : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSection φ (morseTail x)) 0 := by
    simpa using (ContDiffAt.comp 0 hcontσ htail)
  have hg : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x)) 0 := by
    exact ContDiffAt.prodMk hσtail (contDiffAt_id : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => x) 0)
  have hσ0 : morseSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    simpa using (morseSection_zero f φ hφ hcrit hsrc : morseSection φ (0 : MorseModel n) = 0)
  have hfam : ContDiffAt ℝ 1 (fun p : MorseModel (n + 1) × MorseModel (n + 1) =>
      morseTaylorBilinAt f p.1 p.2) (morseSection φ (morseTail (0 : MorseModel (n + 1))), 0) := by
    rw [hσ0]
    exact contDiffAt_morseTaylorBilinAt f hf 0 0
  have hfam' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseTaylorBilinAt f (morseSection φ (morseTail x)) x) 0 := by
    simpa [hσ0] using
      (ContDiffAt.comp (x := 0)
        (g := fun p : MorseModel (n + 1) × MorseModel (n + 1) => morseTaylorBilinAt f p.1 p.2)
        (f := fun x : MorseModel (n + 1) => (morseSection φ (morseTail x), x))
        (hg := hfam) (hf := hg))
  have hB : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 := by
    exact contDiffAt_morseSectionB f hf hcrit φ hφ hsrc hcontσ
  have hsqrt : ContDiffAt ℝ 1 (fun x => Real.sqrt (2 * |morseSectionB f φ x|)) 0 := by
    have habs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) 0 :=
      ContDiffAt.comp 0 (contDiffAt_abs hB0) hB
    have hBcont : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) 0 :=
      ContDiffAt.mul (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => (2 : ℝ)) 0) habs
    have hne : (2 * |morseSectionB f φ 0|) ≠ 0 := by
      have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
      positivity
    exact (Real.contDiffAt_sqrt hne).comp 0 hBcont
  have hhead : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseHead x) 0 := by
    simpa [morseHead, morseHeadProj] using
      ((morseHeadProj.contDiff.contDiffAt : ContDiffAt ℝ ⊤ (fun x => morseHeadProj x) 0).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x)) 0 := by
    have hhead0 : ContDiffAt ℝ 1 (fun y : MorseModel (n + 1) => morseHead y)
        (morseSection φ (morseTail (0 : MorseModel (n + 1)))) := by
      simpa [hσ0] using hhead
    have h' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x))) 0 := by
      exact (ContDiffAt.comp (x := 0)
        (g := fun y : MorseModel (n + 1) => morseHead y)
        (f := fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        (hg := hhead0) (hf := hσtail))
    simpa [morseCriticalSection] using h'
  have hheadsub : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) =>
      morseHead x - morseCriticalSection φ (morseTail x)) 0 :=
    hhead.sub hs
  have hprod : ContDiffAt ℝ 1 (fun x =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x))) 0 :=
    ContDiffAt.mul hsqrt hheadsub
  have hpair : ContDiffAt ℝ 1 (fun x =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0 :=
    ContDiffAt.prodMk hprod htail
  have hcons : ContDiffAt ℝ 1 (fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (Real.sqrt (2 * |morseSectionB f φ (0 : MorseModel (n + 1))|) *
          (morseHead (0 : MorseModel (n + 1)) - morseCriticalSection φ (morseTail (0 : MorseModel (n + 1)))),
        morseTail (0 : MorseModel (n + 1))) := by
    exact ((morseConsLinearCLM.contDiff.contDiffAt :
        ContDiffAt ℝ ⊤ (fun p => morseConsLinearCLM p) _).of_le
      (by decide : (1 : WithTop ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ 1 (fun x =>
      morseConsLinearCLM (Real.sqrt (2 * |morseSectionB f φ x|) *
        (morseHead x - morseCriticalSection φ (morseTail x)), morseTail x)) 0 :=
    ContDiffAt.comp 0 hcons hpair
  change ContDiffAt ℝ 1
    (fun x : MorseModel (n + 1) => morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x)) 0
  simpa [morseSectionB] using hcomp

theorem morseSection_fderiv_head_zero {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i) :
    (morseHeadProj.comp (fderiv ℝ (morseSection φ) (0 : MorseModel n))) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hcomplete := morseSection_fderiv_complete f a φ hφ hsrc hcrit hdf hdfp (u := v)
  have hσ0 : morseSection φ (0 : MorseModel n) = 0 := morseSection_zero f φ hφ hcrit hsrc
  rw [hσ0] at hcomplete
  have hfd0 := fderiv_morsePartial_e0 (n := n) f hg
  have hh : (fderiv ℝ (fderiv ℝ f) 0) (fderiv ℝ (morseSection φ) 0 v) morseE0 =
      w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) := by
    have hd := hdiag (fderiv ℝ (morseSection φ) 0 v) morseE0
    have hsum : (∑ i : Fin (n + 1), w i * (fderiv ℝ (morseSection φ) 0 v) i * morseE0 i) =
        w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) := by
      rw [Fin.sum_univ_succ]
      simp [morseE0, morseHead]
    rw [hd, hsum]
  have happ : (fderiv ℝ (morsePartial f) 0) (fderiv ℝ (morseSection φ) 0 v) = 0 := hcomplete
  have hmul : w 0 * morseHead (fderiv ℝ (morseSection φ) 0 v) = 0 := by
    rw [← hh]
    exact (congrFun hfd0 (fderiv ℝ (morseSection φ) 0 v)).symm.trans hcomplete
  have hw0 : w 0 ≠ 0 := by
    rcases hw 0 with h | h <;> simp [h]
  have hhead0 : morseHead (fderiv ℝ (morseSection φ) 0 v) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hw0
  simpa [ContinuousLinearMap.comp_apply, morseHeadProj, morseHead] using hhead0

noncomputable def morseSectionCompletionDeriv {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) :
    MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) :=
  (morseConsLinearCLM : (ℝ × MorseModel n) →L[ℝ] MorseModel (n + 1)).comp
    ((Real.sqrt (2 * |morseSectionB f φ 0|) •
        (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
      (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))

theorem morseSectionCompletionDeriv_apply {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1))) (v : MorseModel (n + 1)) :
    morseSectionCompletionDeriv f φ v =
      morseCons (Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead v) (morseTail v) := by
  simp [morseSectionCompletionDeriv, morseConsLinearCLM, morseConsLinear, morseHeadProj,
    morseTailProj, morseHead, morseCons, ContinuousLinearMap.comp_apply]

theorem morseSectionCompletionDeriv_injective {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    Function.Injective (morseSectionCompletionDeriv f φ) := by
  intro u v h
  have hu := congrArg morseHead h
  have hv := congrArg morseTail h
  have hq : Real.sqrt (2 * |morseSectionB f φ 0|) ≠ 0 := by
    have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
    positivity
  have hu' : morseHead u = morseHead v := by
    rw [morseSectionCompletionDeriv_apply f φ u, morseSectionCompletionDeriv_apply f φ v] at hu
    have hmul : Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead u =
        Real.sqrt (2 * |morseSectionB f φ 0|) * morseHead v := by
      simpa [morseCons, morseHead] using hu
    exact mul_left_cancel₀ hq hmul
  have hv' : morseTail u = morseTail v := by
    rw [morseSectionCompletionDeriv_apply f φ u, morseSectionCompletionDeriv_apply f φ v] at hv
    simpa [morseCons, morseTail] using hv
  rw [morse_cons_decompose u, morse_cons_decompose v]
  rw [hu', hv']

theorem morseSectionCompletionDeriv_surjective {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    Function.Surjective (morseSectionCompletionDeriv f φ) := by
  intro y
  let s : ℝ := Real.sqrt (2 * |morseSectionB f φ 0|)
  have hs : s ≠ 0 := by
    have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
    positivity
  let v : MorseModel (n + 1) := morseCons (morseHead y / s) (morseTail y)
  refine ⟨v, ?_⟩
  rw [morseSectionCompletionDeriv_apply f φ v]
  have hmv : morseHead v = morseHead y / s := by simp [v, morseHead, morseCons]
  have htv : morseTail v = morseTail y := by
    simp [v, morseCons_tail]
  rw [hmv, htv]
  dsimp [s]
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [morseCons, morseHead]
      field_simp [hs]
  | succ j =>
      simp [morseCons, morseTail, Fin.cons_succ]

noncomputable def morseSectionCompletionDerivCLE {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hB0 : morseSectionB f φ 0 ≠ 0) : MorseModel (n + 1) ≃L[ℝ] MorseModel (n + 1) :=
  (LinearEquiv.ofBijective (morseSectionCompletionDeriv f φ)
    (show Function.Bijective (morseSectionCompletionDeriv f φ) from
      ⟨morseSectionCompletionDeriv_injective f φ hB0,
        morseSectionCompletionDeriv_surjective f φ hB0⟩)).toContinuousLinearEquiv

theorem hasFDerivAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    HasFDerivAt (morseSectionCompletion f φ)
      (morseSectionCompletionDerivCLE f φ hB0 : MorseModel (n + 1) →L[ℝ] MorseModel (n + 1)) 0 := by
  have hBcont : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0 :=
    contDiffAt_morseSectionB f hf hcrit φ hφ hsrc hcontσ
  have hB' : HasFDerivAt (fun x : MorseModel (n + 1) => morseSectionB f φ x)
      (fderiv ℝ (fun x : MorseModel (n + 1) => morseSectionB f φ x) 0) 0 :=
    (hBcont.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hsd : HasFDerivAt (fun x : MorseModel (n + 1) => morseCriticalSection φ (morseTail x))
      (0 : MorseModel (n + 1) →L[ℝ] ℝ) 0 := by
    have hσd : HasFDerivAt (fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)) 0 :=
      HasFDerivAt.comp (x := 0) (g := morseSection φ)
        (g' := fderiv ℝ (morseSection φ) (0 : MorseModel n))
        (f := fun x : MorseModel (n + 1) => morseTail x) (f' := morseTailProj)
        (hg := hdf.hasFDerivAt) (hf := hasFDerivAt_morseTailProj)
    have hheadc : HasFDerivAt (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x)))
        (morseHeadProj.comp ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))) 0 :=
      HasFDerivAt.comp (x := 0) (g := fun y : MorseModel (n + 1) => morseHead y) (g' := morseHeadProj)
        (f := fun x : MorseModel (n + 1) => morseSection φ (morseTail x))
        (f' := (fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp
          (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))
        (hg := by simpa [morseHead, morseHeadProj] using
          (morseHeadProj.hasFDerivAt : HasFDerivAt (fun y : MorseModel (n + 1) => morseHeadProj y)
            morseHeadProj (morseSection φ (morseTail (0 : MorseModel (n + 1))))))
        (hf := hσd)
    have hh := morseSection_fderiv_head_zero f
      (hf.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))) hcrit a φ hφ hsrc hdf hdfp w hw hdiag
    have hzero : morseHeadProj.comp ((fderiv ℝ (morseSection φ) (0 : MorseModel n)).comp morseTailProj) = 0 := by
      rw [← ContinuousLinearMap.comp_assoc, hh]
      simp
    have hsc : HasFDerivAt (fun x : MorseModel (n + 1) => morseHead (morseSection φ (morseTail x)))
        (0 : MorseModel (n + 1) →L[ℝ] ℝ) 0 := by
      simpa [hzero] using hheadc
    convert hsc using 1
  have hgsub : HasFDerivAt (fun x : MorseModel (n + 1) =>
      morseHead x - morseCriticalSection φ (morseTail x)) morseHeadProj 0 := by
    have hsub := HasFDerivAt.sub hasFDerivAt_morseHead hsd
    simpa using hsub
  have hsqrt' : HasFDerivAt (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|))
      (fderiv ℝ (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|)) 0) 0 := by
    have habs : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => |morseSectionB f φ x|) 0 :=
      ContDiffAt.comp 0 (contDiffAt_abs hB0) hBcont
    have hBcont' : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => 2 * |morseSectionB f φ x|) 0 :=
      ContDiffAt.mul (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : MorseModel (n + 1) => (2 : ℝ)) 0) habs
    have hne : (2 * |morseSectionB f φ 0|) ≠ 0 := by
      have : |morseSectionB f φ 0| ≠ 0 := abs_ne_zero.mpr hB0
      positivity
    have hsqrtc : ContDiffAt ℝ 1 (fun x : MorseModel (n + 1) => Real.sqrt (2 * |morseSectionB f φ x|)) 0 :=
      (Real.contDiffAt_sqrt hne).comp 0 hBcont'
    exact (hsqrtc.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
  have hg0 : morseHead (0 : MorseModel (n + 1)) - morseCriticalSection φ (morseTail (0 : MorseModel (n + 1))) = 0 := by
    have htail0 : morseTail (0 : MorseModel (n + 1)) = 0 := by
      funext i
      simp [morseTail]
    have hsec : φ.symm (morseCons (0 : ℝ) (morseTail (0 : MorseModel (n + 1)))) = 0 := by
      rw [htail0]
      simpa [morseSection] using (morseSection_zero f φ hφ hcrit hsrc : morseSection φ (0 : MorseModel n) = 0)
    simp [morseCriticalSection, hsec]
  have hmul' : HasFDerivAt (fun x : MorseModel (n + 1) =>
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)))
      (Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)) 0 := by
    have hmul0 := HasFDerivAt.mul hsqrt' hgsub
    simpa [hg0, smul_zero, add_zero, zero_add] using hmul0
  have hpair : HasFDerivAt (fun x : MorseModel (n + 1) =>
      (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
        morseTail x))
      ((Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n)) 0 :=
    hmul'.prodMk hasFDerivAt_morseTailProj
  have hcons' : HasFDerivAt (fun p : ℝ × MorseModel n => morseConsLinearCLM p) morseConsLinearCLM
      (Real.sqrt (2 * |morseSectionB f φ 0|) * (morseHead (0 : MorseModel (n + 1)) -
        morseCriticalSection φ (morseTail (0 : MorseModel (n + 1)))), morseTail (0 : MorseModel (n + 1))) := by
    exact morseConsLinearCLM.hasFDerivAt
  have hcomp' : HasFDerivAt (morseSectionCompletion f φ)
      (morseConsLinearCLM.comp ((Real.sqrt (2 * |morseSectionB f φ 0|) •
        (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))) 0 := by
    have hc := HasFDerivAt.comp 0 (g := fun p : ℝ × MorseModel n => morseConsLinearCLM p)
      (g' := morseConsLinearCLM)
      (f := fun x : MorseModel (n + 1) =>
        (Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)),
          morseTail x))
      (f' := (Real.sqrt (2 * |morseSectionB f φ 0|) • (morseHeadProj : MorseModel (n + 1) →L[ℝ] ℝ)).prod
        (morseTailProj : MorseModel (n + 1) →L[ℝ] MorseModel n))
      (hg := hcons') (hf := hpair)
    simpa [morseSectionCompletion, morseSectionB, Function.comp_def] using hc
  simpa [morseSectionCompletionDerivCLE, morseSectionCompletionDeriv, ContinuousLinearMap.comp_apply]
    using hcomp'

theorem morseSectionCompletion_value {n : ℕ} (f : MorseModel (n + 1) → ℝ) (hg : ContDiff ℝ 2 f)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    {x : MorseModel (n + 1)} (hx' : morseCons (0 : ℝ) (morseTail x) ∈ φ.target)
    (hBx : morseSectionB f φ x ≠ 0) :
    f x - f (morseSection φ (morseTail x)) =
      (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
        (morseHead (morseSectionCompletion f φ x)) ^ 2 := by
  have hso := section_second_order f hg φ hφ (x := x) hx'
  have hhead : morseHead (morseSectionCompletion f φ x) =
      Real.sqrt (2 * |morseSectionB f φ x|) * (morseHead x - morseCriticalSection φ (morseTail x)) := by
    simp [morseSectionCompletion, morseHead, morseCons]
  have hBabs : |morseSectionB f φ x| ≠ 0 := abs_ne_zero.mpr hBx
  have hmul : (morseHead (morseSectionCompletion f φ x)) ^ 2 =
      2 * |morseSectionB f φ x| * (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 := by
    rw [hhead]
    rw [mul_pow]
    have hsq : (Real.sqrt (2 * |morseSectionB f φ x|)) ^ 2 = 2 * |morseSectionB f φ x| := by
      rw [Real.sq_sqrt]
      positivity
    rw [hsq]
  have hsign : morseSectionB f φ x = SignType.sign (morseSectionB f φ x) * |morseSectionB f φ x| := by
    rw [sign_mul_abs]
  calc
    f x - f (morseSection φ (morseTail x)) =
        (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 * morseSectionB f φ x := hso
    _ = (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2 *
          (SignType.sign (morseSectionB f φ x) * |morseSectionB f φ x|) := by
      conv_lhs =>
        rw [hsign]
    _ = (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
          (2 * |morseSectionB f φ x| * (morseHead x - morseCriticalSection φ (morseTail x)) ^ 2) := by ring
    _ = (1 / 2 : ℝ) * SignType.sign (morseSectionB f φ x) *
          (morseHead (morseSectionCompletion f φ x)) ^ 2 := by
      rw [← hmul]

theorem isLocalHomeomorphAt_morseSectionCompletion {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hf : ContDiff ℝ 3 f) (hcrit : fderiv ℝ f 0 = 0)
    (a : MorseModel (n + 1) → MorseModel (n + 1) →L[ℝ] MorseModel (n + 1) →L[ℝ] ℝ)
    (φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)))
    (hφ : (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f)
    (hsrc : (0 : MorseModel (n + 1)) ∈ φ.source)
    (hdf : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n))
    (hdfp : DifferentiableAt ℝ (morsePartial f) (morseSection φ (0 : MorseModel n)))
    (hcontσ : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n))
    (w : Fin (n + 1) → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdiag : ∀ u v : MorseModel (n + 1),
      (fderiv ℝ (fderiv ℝ f) 0 u) v = ∑ i : Fin (n + 1), w i * u i * v i)
    (hB0 : morseSectionB f φ 0 ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (Φ : MorseModel (n + 1) → MorseModel (n + 1)) = morseSectionCompletion f φ ∧ 0 ∈ Φ.source := by
  let Φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morseSectionCompletion f φ)
      (f' := morseSectionCompletionDerivCLE f φ hB0)
      (contDiffAt_morseSectionCompletion f hf hcrit φ hφ hsrc hcontσ hB0)
      (hasFDerivAt_morseSectionCompletion f hf hcrit a φ hφ hsrc hdf hdfp hcontσ w hw hdiag hB0)
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  refine ⟨Φ, ?_, ?_⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

theorem morseSection_smooth {n : ℕ} (f : MorseModel (n + 1) → ℝ)
    (hcrit : fderiv ℝ f 0 = 0)
    (hcont : ContDiffAt ℝ ⊤ (morsePartialMap f) 0)
    (hdf : DifferentiableAt ℝ (morsePartial f) 0)
    (h₀ : fderiv ℝ (morsePartial f) 0 morseE0 ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)),
      (φ : MorseModel (n + 1) → MorseModel (n + 1)) = morsePartialMap f ∧ 0 ∈ φ.source ∧
      ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n) ∧
      DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n) := by
  let φ : OpenPartialHomeomorph (MorseModel (n + 1)) (MorseModel (n + 1)) :=
    ContDiffAt.toOpenPartialHomeomorph (f := morsePartialMap f)
      (f' := morsePartialDerivCLE (fderiv ℝ (morsePartial f) 0) h₀)
      hcont (hasFDerivAt_morsePartialMap f hdf h₀)
      (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
  have hφ0 : morsePartialMap f 0 = 0 := by
    funext i
    cases i using Fin.cases <;> simp [morsePartialMap, morsePartial, morseCons, morseTail, hcrit]
  have hφsymm : ContDiffAt ℝ ⊤ (φ.symm) (morsePartialMap f 0) := by
    have hloc := hcont.to_localInverse (hasFDerivAt_morsePartialMap f hdf h₀)
      (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)
    simpa [φ, ContDiffAt.localInverse] using hloc
  have hφsymm0 : ContDiffAt ℝ ⊤ (φ.symm) 0 := by
    simpa [hφ0] using hφsymm
  have hφsymm1 : ContDiffAt ℝ 1 (φ.symm) 0 :=
    hφsymm0.of_le (by decide : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hcons0 : ContDiffAt ℝ ⊤ (fun x' : MorseModel n => morseCons (0 : ℝ) x') 0 := by
    have hL : (fun x' : MorseModel n => morseConsLinearCLM (0, x')) =
        fun x' : MorseModel n => morseCons (0 : ℝ) x' := by
      funext x'
      rfl
    have hc : ContDiffAt ℝ ⊤ (fun x' : MorseModel n => morseConsLinearCLM (0, x')) 0 := by
      have hlin : (fun x' : MorseModel n => morseConsLinearCLM (0, x')) =
          (morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))) := by
        funext x'
        rfl
      rw [hlin]
      exact ((morseConsLinearCLM.comp (ContinuousLinearMap.inr ℝ ℝ (MorseModel n))).contDiff.contDiffAt)
    simpa [hL] using hc
  have hcons1 : ContDiffAt ℝ 1 (fun x' : MorseModel n => morseCons (0 : ℝ) x') 0 :=
    hcons0.of_le (by decide : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hsec0 : φ.symm (morseCons (0 : ℝ) (0 : MorseModel n)) = 0 := by
    have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
      funext i
      cases i using Fin.cases <;> simp [morseCons]
    rw [hz]
    have hφ0' : φ 0 = 0 := by
      have hφm : φ 0 = morsePartialMap f 0 := by rw [ContDiffAt.toOpenPartialHomeomorph_coe]
      rw [hφm, hφ0]
    have hsrc : (0 : MorseModel (n + 1)) ∈ φ.source :=
      ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
    have htarget : (0 : MorseModel (n + 1)) ∈ φ.target := by
      have ht : morsePartialMap f 0 ∈ φ.target := by
        simpa [φ] using (ContDiffAt.image_mem_toOpenPartialHomeomorph_target hcont
          (hasFDerivAt_morsePartialMap f hdf h₀) (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0))
      simpa [hφ0] using ht
    have hφinv : φ (φ.symm 0) = 0 := by
      simpa [hφ0'] using (φ.right_inv htarget)
    have hφeq : φ (φ.symm 0) = φ 0 := by
      simpa [hφ0'] using hφinv
    exact (φ.injOn (φ.map_target htarget) hsrc hφeq)
  have hσ1 : ContDiffAt ℝ 1 (morseSection φ) (0 : MorseModel n) := by
    change ContDiffAt ℝ 1 (fun x' : MorseModel n => φ.symm (morseCons (0 : ℝ) x')) (0 : MorseModel n)
    have hg' : ContDiffAt ℝ 1 (φ.symm) (morseCons (0 : ℝ) (0 : MorseModel n)) := by
      have hz : morseCons (0 : ℝ) (0 : MorseModel n) = (0 : MorseModel (n + 1)) := by
        funext i
        cases i using Fin.cases <;> simp [morseCons]
      simpa [hz] using hφsymm1
    exact ContDiffAt.comp (x := 0) (g := φ.symm)
      (f := fun x' : MorseModel n => morseCons (0 : ℝ) x') (hg := hg') (hf := hcons1)
  have hσdiff : DifferentiableAt ℝ (morseSection φ) (0 : MorseModel n) :=
    (hσ1.differentiableAt (by decide : (1 : WithTop ℕ∞) ≠ 0))
  refine ⟨φ, ?_, ?_, hσ1, hσdiff⟩
  · rw [ContDiffAt.toOpenPartialHomeomorph_coe]
  · exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

end Completion

end DifferentialGeometry.Topology.Morse
