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
open scoped Filter Topology

namespace Completion

variable {n : ℕ}

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

end Completion

end DifferentialGeometry.Topology.Morse
