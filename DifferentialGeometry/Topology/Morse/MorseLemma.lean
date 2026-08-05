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
    simp [smul_eq_mul, mul_assoc]
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
        simp [morsePartialDeriv, v, morseTail, morseCons, Fin.cons_succ, htv]
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
    {u : MorseModel n} (hu : morseCons (0 : ℝ) u ∈ φ.target) :
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

end Completion

end DifferentialGeometry.Topology.Morse
