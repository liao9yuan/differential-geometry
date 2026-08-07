import DifferentialGeometry.Topology.Morse.LocalNormalForm
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Morse

noncomputable section

abbrev LevelSetSpace {M : Type} (f : M → ℝ) (a : ℝ) : Type := {x : M // f x = a}

noncomputable def levelSetReindex {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1)) :
    MorseModel (m + 1) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun v j => v (e.symm j)
  map_add' := by
    intro x y
    ext j
    rfl
  map_smul' := by
    intro a x
    ext j
    rfl
  invFun := fun v j => v (e j)
  left_inv := by
    intro v
    ext j
    simp
  right_inv := by
    intro v
    ext j
    simp

theorem levelSetReindex_apply {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) (j : Fin (m + 1)) :
    levelSetReindex e v j = v (e.symm j) := rfl

theorem levelSetReindex_comp {m : ℕ} (e₁ e₂ : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e₁ (levelSetReindex e₂ v) = levelSetReindex (e₂.trans e₁) v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_symm {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e (levelSetReindex e.symm v) = v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_lastBasis {m : ℕ} (i : Fin (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m))
        (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) =
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
  ext j
  rw [levelSetReindex_apply]
  by_cases hj : j = i
  · subst j
    have h : (Equiv.swap i (Fin.last m)).symm i = Fin.last m := by simp
    rw [h]
    simp
  · have hne : (Equiv.swap i (Fin.last m)).symm j ≠ Fin.last m := by
      intro h'
      apply hj
      have hback := congrArg (Equiv.swap i (Fin.last m)) h'
      simpa using hback
    rw [if_neg hne]
    simp [hj]

theorem exists_coord_of_fderiv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (y : MorseModel (m + 1)) (h : fderiv ℝ g y ≠ 0) :
    ∃ i : Fin (m + 1), (fderiv ℝ g y)
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0 := by
  by_contra hz
  apply h
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ j : Fin (m + 1), v j • (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply]
  have hzall : ∀ j : Fin (m + 1), (fderiv ℝ g y)
      (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) = 0 := by
    intro j
    by_contra hne
    exact hz ⟨j, hne⟩
  rw [hv]
  simp [hzall]

noncomputable def levelSetSplit (m : ℕ) : (MorseModel m × ℝ) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun p j =>
    if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h)
  map_add' := by
    intro x y
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  map_smul' := by
    intro a x
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  invFun := fun v => ((fun i : Fin m => v (Fin.castSucc i)), v (Fin.last m))
  left_inv := by
    intro p
    ext i
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.castSucc i) = p.1 i
      have h : Fin.castSucc i ≠ Fin.last m := Fin.castSucc_ne_last i
      simp [h]
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.last m) = p.2
      simp
  right_inv := by
    intro v
    ext j
    by_cases h : j = Fin.last m
    · subst j
      simp
    · change (if h : Fin.castSucc (Fin.castPred j h) = Fin.last m then v (Fin.last m)
          else v (Fin.castSucc (Fin.castPred j h))) = v j
      have hne : Fin.castSucc (Fin.castPred j h) ≠ Fin.last m := Fin.castSucc_ne_last (Fin.castPred j h)
      rw [dif_neg hne]
      rw [Fin.castSucc_castPred j h]

noncomputable def scalarLinearEquiv {𝕜 : Type*} [NormedField 𝕜] (c : 𝕜) (hc : c ≠ 0) :
    𝕜 ≃L[𝕜] 𝕜 where
  toFun := fun z => c • z
  invFun := fun z => c⁻¹ • z
  map_add' := by
    intro x y
    simp [smul_eq_mul, mul_add]
  map_smul' := by
    intro a x
    simp [smul_eq_mul]
    ring
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹
  left_inv := by
    intro x
    change c⁻¹ • (c • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv := by
    intro x
    change c • (c⁻¹ • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

def levelSetLastBasis {m : ℕ} : MorseModel (m + 1) :=
  fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0

theorem levelSetSplit_basis (m : ℕ) :
    levelSetSplit m (0, (1 : ℝ)) = levelSetLastBasis := by
  ext j
  by_cases hj : j = Fin.last m
  · subst j
    dsimp [levelSetSplit]
    simp [levelSetLastBasis]
  · dsimp [levelSetSplit]
    simp [hj, levelSetLastBasis]

theorem levelSetReindex_swap_swap {m : ℕ} (i : Fin (m + 1)) (u₀ : MorseModel (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m)) (levelSetReindex (Equiv.swap i (Fin.last m)) u₀) =
      u₀ := by
  have hs : (Equiv.swap i (Fin.last m)).symm = Equiv.swap i (Fin.last m) := by
    ext j
    simp
  rw [← hs]
  exact levelSetReindex_symm (Equiv.swap i (Fin.last m)) u₀

theorem levelSetReindex_lastDeriv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀) (i : Fin (m + 1))
    (hi : (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0) :
    (fderiv ℝ (fun w => g (levelSetReindex (Equiv.swap i (Fin.last m)) w))
      (levelSetReindex (Equiv.swap i (Fin.last m)) u₀)) levelSetLastBasis ≠ 0 := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e u₀
  have hder : fderiv ℝ (fun w => g (levelSetReindex e w)) u₁ =
      (fderiv ℝ g (levelSetReindex e u₁)).comp ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
    have hgdiff : DifferentiableAt ℝ g (levelSetReindex e u₁) := by
      rw [levelSetReindex_swap_swap]
      exact hg.differentiableAt (by norm_num)
    have hldiff : DifferentiableAt ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).differentiableAt
    have hcomp := fderiv_comp u₁ (g := g) (f := fun w : MorseModel (m + 1) => levelSetReindex e w)
      hgdiff hldiff
    have hldiff_der : fderiv ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ =
        ((levelSetReindex e).toContinuousLinearEquiv :
          MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
      exact (ContinuousLinearMap.fderiv ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)))
    simpa [hldiff_der] using hcomp
  have hval : (fderiv ℝ g (levelSetReindex e u₁))
      (levelSetReindex e levelSetLastBasis) =
      (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
    rw [levelSetReindex_swap_swap]
    have hlb : levelSetReindex e levelSetLastBasis =
        (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
      simpa [e, levelSetLastBasis] using levelSetReindex_lastBasis i
    rw [hlb]
  rw [hder]
  change (fderiv ℝ g (levelSetReindex e u₁)) (levelSetReindex e levelSetLastBasis) ≠ 0
  rwa [hval]

theorem levelSetImplicitFunction {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀)
    (hlast : (fderiv ℝ g u₀) levelSetLastBasis ≠ 0) :
    ∃ ψ : MorseModel m → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) ψ ((levelSetSplit m).symm u₀).1 ∧
      (∀ᶠ y in nhds ((levelSetSplit m).symm u₀).1,
        g (levelSetSplit m (y, ψ y)) = g u₀) := by
  let u₁ : MorseModel m × ℝ := (levelSetSplit m).symm u₀
  let F : MorseModel m × ℝ → ℝ := fun p => g (levelSetSplit m p)
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F u₁ := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ :=
      ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetSplit m u₁) := by
      simpa [u₁] using hg
    exact hg'.comp u₁ hlin
  have hFder : (fderiv ℝ F u₁ ∘L ContinuousLinearMap.inr ℝ (MorseModel m) ℝ).IsInvertible := by
    have hder : fderiv ℝ F u₁ = (fderiv ℝ g (levelSetSplit m u₁)).comp
        ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)) := by
      have hgdiff : DifferentiableAt ℝ g (levelSetSplit m u₁) := by
        simpa [u₁] using (hg.differentiableAt (by norm_num))
      have hldiff : DifferentiableAt ℝ (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ :=
        ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)).differentiableAt
      have hcomp := fderiv_comp u₁ (g := g) (f := fun p : MorseModel m × ℝ => levelSetSplit m p)
        hgdiff hldiff
      have hldiff_der : fderiv ℝ (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ =
          ((levelSetSplit m).toContinuousLinearEquiv :
            (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)) := by
        exact (ContinuousLinearMap.fderiv ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)))
      simpa [F, hldiff_der] using hcomp
    have hscalar : (fderiv ℝ F u₁ ∘L ContinuousLinearMap.inr ℝ (MorseModel m) ℝ) =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0))) := by
      apply ContinuousLinearMap.ext
      intro z
      rw [hder]
      change (fderiv ℝ g (levelSetSplit m u₁))
        (levelSetSplit m (0, z)) = z • ((fderiv ℝ g u₀) levelSetLastBasis)
      have hlin : (fderiv ℝ g (levelSetSplit m u₁))
          (levelSetSplit m (0, z)) =
          z • (fderiv ℝ g (levelSetSplit m u₁)) (levelSetSplit m (0, (1 : ℝ))) := by
        have hs : levelSetSplit m (0, z) = z • levelSetSplit m (0, (1 : ℝ)) := by
          ext j
          dsimp [levelSetSplit]
          by_cases hj : j = Fin.last m
          · subst j
            simp
          · simp [hj]
        rw [hs]
        simp
      rw [hlin]
      have hpt : (levelSetSplit m) u₁ = u₀ := (levelSetSplit m).apply_symm_apply u₀
      rw [hpt, levelSetSplit_basis]
    rw [hscalar]
    refine ⟨scalarLinearEquiv ((fderiv ℝ g u₀) levelSetLastBasis) hlast, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ g u₀) levelSetLastBasis) • z =
      z * (fderiv ℝ g u₀) levelSetLastBasis
    simp [smul_eq_mul, mul_comm]
  exact ⟨hF.implicitFunction (by norm_num) hFder, by
    have hsm := hF.contDiffAt_implicitFunction (by norm_num) hFder
    simpa [F] using hsm, by
    have hgrap := hF.eventually_apply_implicitFunction (by norm_num) hFder
    filter_upwards [hgrap] with y hy
    simpa [u₁, F] using hy⟩

theorem exists_levelSet_local_graph {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀) (h : fderiv ℝ g u₀ ≠ 0) :
    ∃ (e : Fin (m + 1) ≃ Fin (m + 1)) (ψ : MorseModel m → ℝ),
      ContDiffAt ℝ (⊤ : ℕ∞) ψ ((levelSetSplit m).symm (levelSetReindex e u₀)).1 ∧
      (∀ᶠ y in nhds ((levelSetSplit m).symm (levelSetReindex e u₀)).1,
        g (levelSetReindex e (levelSetSplit m (y, ψ y))) = g u₀) := by
  rcases exists_coord_of_fderiv_ne_zero g u₀ h with ⟨i, hi⟩
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e u₀
  have hs : e.symm = e := by
    ext j
    simp [e]
  have hfix : levelSetReindex e (levelSetReindex e u₀) = u₀ := by
    rw [← hs]
    exact levelSetReindex_symm e u₀
  have hpt : levelSetReindex e u₁ = u₀ := by
    simpa [u₁] using hfix
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => g (levelSetReindex e w)) u₁ := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e u₁) := by
      rw [hpt]
      exact hg
    exact hg'.comp u₁ hlin
  have hlastG : (fderiv ℝ (fun w => g (levelSetReindex e w)) u₁)
      (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) ≠ 0 := by
    simpa [u₁, levelSetLastBasis] using levelSetReindex_lastDeriv_ne_zero g u₀ hg i hi
  rcases levelSetImplicitFunction (fun w => g (levelSetReindex e w)) u₁ hG hlastG with
    ⟨ψ, hψ, hgrap⟩
  exact ⟨e, ψ, hψ, by
    filter_upwards [hgrap] with y hy
    simpa [u₁, hpt] using hy⟩

def levelSetSplitFst (m : ℕ) : MorseModel (m + 1) →L[ℝ] MorseModel m :=
  (ContinuousLinearMap.fst ℝ (MorseModel m) ℝ).comp
    ((levelSetSplit m).symm.toContinuousLinearEquiv : MorseModel (m + 1) →L[ℝ] (MorseModel m × ℝ))

theorem levelSetSplitFst_split (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplitFst m (levelSetSplit m (y, z)) = y := by
  simp [levelSetSplitFst]

theorem levelSetSplit_add_basis (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplit m (y, z) = levelSetSplit m (y, 0) + z • levelSetLastBasis := by
  have hlin := (levelSetSplit m).map_add (y, (0 : ℝ)) (0, z)
  have hz : (levelSetSplit m) (0, z) = z • levelSetLastBasis := by
    rw [← levelSetSplit_basis m]
    simpa using (levelSetSplit m).map_smul z (0, (1 : ℝ))
  rw [hz] at hlin
  simpa [add_comm, add_left_comm, add_assoc] using hlin

noncomputable def levelSetChartDerivInvFun {m : ℕ} (D : MorseModel (m + 1) →L[ℝ] ℝ) :
    (ℝ × MorseModel m) → MorseModel (m + 1) :=
  fun q => levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)

noncomputable def levelSetChartDerivEquiv {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    MorseModel (m + 1) ≃L[ℝ] (ℝ × MorseModel m) where
  toFun := fun v => ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) v, levelSetSplitFst m v)
  invFun := levelSetChartDerivInvFun (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
  left_inv := by
    intro v
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    let y : MorseModel m := levelSetSplitFst m v
    let z : ℝ := ((levelSetSplit m).symm v).2
    have hv : v = levelSetSplit m (y, z) := by
      have hsymm : (levelSetSplit m).symm v = (y, z) := by
        simp [y, z, levelSetSplitFst]
      rw [← hsymm]
      exact ((levelSetSplit m).apply_symm_apply v).symm
    have hlin : D (levelSetSplit m (y, z)) = D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis := by
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
    change levelSetSplit m (y, (D v - D (levelSetSplit m (y, 0))) / D levelSetLastBasis) = v
    rw [hv]
    rw [hlin]
    have hz : (D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis -
        D (levelSetSplit m (y, 0))) / D levelSetLastBasis = z := by
      rw [smul_eq_mul]
      rw [add_sub_cancel_left]
      rw [div_eq_mul_inv]
      rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hz]
  right_inv := by
    intro q
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    change (D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)),
        levelSetSplitFst m (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis))) = q
    rw [levelSetSplitFst_split]
    apply Prod.ext
    · change D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)) = q.1
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
      have hz : ((q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis) • D levelSetLastBasis =
          q.1 - D (levelSetSplit m (q.2, 0)) := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ (q.1 - D (levelSetSplit m (q.2, 0))) hc
      rw [hz]
      ring
    · rfl
  map_add' := by
    intro x y
    ext <;> simp [map_add]
  map_smul' := by
    intro c x
    ext <;> simp [map_smul, smul_eq_mul]
  continuous_invFun := by
    have hsplit : Continuous (levelSetSplit m) := (levelSetSplit m).toContinuousLinearEquiv.continuous
    change Continuous (fun q : ℝ × MorseModel m =>
      levelSetSplit m (q.2, (q.1 - (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
        (levelSetSplit m (q.2, 0))) / ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis)))
    exact hsplit.comp (by fun_prop)

noncomputable def levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) : MorseModel (m + 1) → ℝ × MorseModel m :=
  fun w => (g (levelSetReindex e w), levelSetSplitFst m w)

theorem contDiffAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (levelSetChartMap g e) w := by
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have hg' : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) w :=
    hg.comp w hlin
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) w :=
    (levelSetSplitFst m).contDiff.contDiffAt
  simpa [levelSetChartMap] using hg'.prodMk hp

theorem contDiff_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (levelSetChartMap g e) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) :=
    hg.comp hlin
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) :=
    (levelSetSplitFst m).contDiff
  simpa [levelSetChartMap] using hg'.prodMk hp

theorem hasFDerivAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    HasFDerivAt (levelSetChartMap g e)
      (↑(levelSetChartDerivEquiv g e w hc) : MorseModel (m + 1) →L[ℝ] (ℝ × MorseModel m)) w := by
  have hdiff : DifferentiableAt ℝ (fun v => g (levelSetReindex e v)) w := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    exact (hg.comp w hlin).differentiableAt (by norm_num)
  have h₁ : HasFDerivAt (fun v => g (levelSetReindex e v))
      (fderiv ℝ (fun v => g (levelSetReindex e v)) w) w :=
    hdiff.hasFDerivAt
  have h₂ : HasFDerivAt (fun v : MorseModel (m + 1) => levelSetSplitFst m v)
      (levelSetSplitFst m) w :=
    (levelSetSplitFst m).hasFDerivAt
  have hpair := h₁.prodMk h₂
  have heq : (fderiv ℝ (fun v => g (levelSetReindex e v)) w).prod (levelSetSplitFst m) =
      ↑(levelSetChartDerivEquiv g e w hc) := by
    ext v <;> rfl
  simpa [levelSetChartMap, heq] using hpair

def levelSetLastDerivSet {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) : Set (MorseModel (m + 1)) :=
  {w | (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0}

theorem levelSetLastDerivSet_open {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    IsOpen (levelSetLastDerivSet g e) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) := hg.comp hlin
  have hf : Continuous (fderiv ℝ (fun v => g (levelSetReindex e v))) :=
    hG.continuous_fderiv (by norm_num)
  have hcont : Continuous (fun w : MorseModel (m + 1) =>
      (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis) :=
    hf.clm_apply continuous_const
  exact isOpen_compl_singleton.preimage hcont

theorem levelSetChart_invFun_mem {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) {a : ℝ}
    (ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m))
    (hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e)
    {z : MorseModel m} (hz : (a, z) ∈ ψ.target) :
    g (levelSetReindex e (ψ.symm (a, z))) = a := by
  have hval : (ψ (ψ.symm (a, z))).1 = a := by
    rw [ψ.right_inv hz]
  have h1 : (ψ (ψ.symm (a, z))).1 = g (levelSetReindex e (ψ.symm (a, z))) := by
    rw [hψ]
    rfl
  exact h1.symm.trans hval

private structure LevelSetChartData {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) where
  i : Fin (m + 1)
  hi : (fderiv ℝ g x.1) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0
  e : Fin (m + 1) ≃ Fin (m + 1)
  he : e = Equiv.swap i (Fin.last m)
  u₁ : MorseModel (m + 1)
  hu₁ : u₁ = levelSetReindex e x.1
  hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) u₁) levelSetLastBasis ≠ 0
  φ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m)
  ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m)
  hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e
  hψsource : ψ.source = φ.source ∩ levelSetLastDerivSet g e

private noncomputable def levelSetChartData.mk {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    LevelSetChartData g a x hg hreg := by
  classical
  let i : Fin (m + 1) := Classical.choose (exists_coord_of_fderiv_ne_zero g x.1 hreg)
  have hi : (fderiv ℝ g x.1) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0 :=
    Classical.choose_spec (exists_coord_of_fderiv_ne_zero g x.1 hreg)
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e x.1
  have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e u₁) := by
    rw [levelSetReindex_swap_swap]
    exact hg.contDiffAt
  have hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) u₁) levelSetLastBasis ≠ 0 :=
    levelSetReindex_lastDeriv_ne_zero g x.1 hg.contDiffAt i hi
  let φ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) :=
    ContDiffAt.toOpenPartialHomeomorph (f := levelSetChartMap g e)
      (contDiffAt_levelSetChartMap g e u₁ hg') (hasFDerivAt_levelSetChartMap g e u₁ hg' hc)
      (by norm_num)
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) :=
    φ.restrOpen (levelSetLastDerivSet g e) (levelSetLastDerivSet_open g e hg)
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e := by
    simp [ψ, φ, ContDiffAt.toOpenPartialHomeomorph_coe]
  exact ⟨i, hi, e, rfl, u₁, rfl, hc, φ, ψ, hψ, by
    rw [OpenPartialHomeomorph.restrOpen_source]⟩

noncomputable def levelSetChart {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  let inv : MorseModel m → LevelSetSpace g a := fun z =>
    if hz : (a, z) ∈ ψ.target then
      ⟨levelSetReindex d.e (ψ.symm (a, z)), levelSetChart_invFun_mem g d.e ψ hψ hz⟩
    else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := fun y : LevelSetSpace g a => (ψ (levelSetReindex d.e y.1)).2
          invFun := inv
          source := {y : LevelSetSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
          target := {z : MorseModel m | (a, z) ∈ ψ.target}
          map_source' := by
            intro y hy
            change (a, (ψ (levelSetReindex d.e y.1)).2) ∈ ψ.target
            have h1 : (ψ (levelSetReindex d.e y.1)).1 = a := by
              rw [hψ]
              change g (levelSetReindex d.e (levelSetReindex d.e y.1)) = a
              rw [d.he, levelSetReindex_swap_swap]
              exact y.2
            have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
              Prod.ext h1.symm rfl
            rw [hpair]
            exact ψ.map_source hy
          map_target' := by
            intro z hz
            change levelSetReindex d.e ((inv z).1) ∈ ψ.source
            simp only [inv, dif_pos (show (a, z) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact ψ.map_target hz
          left_inv' := by
            intro y hy
            have h1 : (ψ (levelSetReindex d.e y.1)).1 = a := by
              rw [hψ]
              change g (levelSetReindex d.e (levelSetReindex d.e y.1)) = a
              rw [d.he, levelSetReindex_swap_swap]
              exact y.2
            have hz : (a, (ψ (levelSetReindex d.e y.1)).2) ∈ ψ.target := by
              have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
                Prod.ext h1.symm rfl
              rw [hpair]
              exact ψ.map_source hy
            change inv (ψ (levelSetReindex d.e y.1)).2 = y
            simp only [inv, dif_pos hz]
            apply Subtype.ext
            change levelSetReindex d.e (ψ.symm (a, (ψ (levelSetReindex d.e y.1)).2)) = y.1
            have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
              Prod.ext h1.symm rfl
            have hleft : ψ.symm (ψ (levelSetReindex d.e y.1)) = levelSetReindex d.e y.1 :=
              ψ.left_inv hy
            rw [← hpair] at hleft
            rw [hleft]
            rw [d.he, levelSetReindex_swap_swap]
          right_inv' := by
            intro z hz
            simp only [inv, dif_pos (show (a, z) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact congrArg Prod.snd (ψ.right_inv hz) }
      open_source := by
        have hcont : Continuous (fun y : LevelSetSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        exact ψ.open_source.preimage hcont
      open_target := by
        have hcont : Continuous (fun z : MorseModel m => (a, z)) := by fun_prop
        exact ψ.open_target.preimage hcont
      continuousOn_toFun := by
        have hf : Continuous (fun y : LevelSetSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        have hcomp : ContinuousOn (fun y : LevelSetSpace g a => ψ (levelSetReindex d.e y.1))
            {y : LevelSetSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          ψ.continuousOn.comp hf.continuousOn (by intro y hy; exact hy)
        exact continuous_snd.comp_continuousOn hcomp
      continuousOn_invFun := by
        let s : Set (MorseModel m) := {z | (a, z) ∈ ψ.target}
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hc : Continuous (fun z : s => (a, (z : MorseModel m))) := by fun_prop
        have hc0 : Continuous (fun z : s => ψ.symm (a, (z : MorseModel m))) := by
          have hc0' : ContinuousOn (fun z : s => ψ.symm (a, (z : MorseModel m))) (Set.univ : Set s) := by
            refine ψ.symm.continuousOn.comp hc.continuousOn ?_
            intro z hz
            exact z.2
          exact continuousOn_univ.mp hc0'
        have hc1 : Continuous (fun z : s =>
            (⟨levelSetReindex d.e (ψ.symm (a, (z : MorseModel m))),
              levelSetChart_invFun_mem g d.e ψ hψ (show (a, (z : MorseModel m)) ∈ ψ.target from z.2)⟩ :
                LevelSetSpace g a)) :=
          Continuous.subtype_mk
            (((levelSetReindex d.e).toContinuousLinearEquiv :
              MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp hc0)
            (fun z : s => levelSetChart_invFun_mem g d.e ψ hψ
              (show (a, (z : MorseModel m)) ∈ ψ.target from z.2))
        refine hc1.congr ?_
        intro z
        simp only [Set.restrict, inv]
        rw [dif_pos (show (a, (z : MorseModel m)) ∈ ψ.target from z.2)] }

theorem mem_levelSetChart_source {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    x ∈ (levelSetChart g a x hg hreg).source := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  change levelSetReindex d.e x.1 ∈ d.ψ.source
  rw [d.hψsource]
  constructor
  · rw [← d.hu₁]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source (f := levelSetChartMap g d.e)
      (contDiffAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt))
      (hasFDerivAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt) d.hc)
      (by norm_num)
  · rw [← d.hu₁]
    exact d.hc



theorem levelSetChart_transition_contDiffAt {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : LevelSetSpace g a}
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) {z : MorseModel m}
    (hz : z ∈ ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ (levelSetChart g a x₂ hg hr₂)).source) :
    ContDiffAt ℝ (⊤ : ℕ∞) ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
      (levelSetChart g a x₂ hg hr₂)) z := by
  classical
  let c₁ : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := levelSetChart g a x₁ hg hr₁
  let c₂ : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := levelSetChart g a x₂ hg hr₂
  let d₁ := levelSetChartData.mk g a x₁ hg hr₁
  let d₂ := levelSetChartData.mk g a x₂ hg hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  have hψ₁ : (ψ₁ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₁ := d₁.hψ
  have hψ₂ : (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₂ := d₂.hψ
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1
  have haz : (a, z) ∈ ψ₁.target := by
    change (a, z) ∈ ψ₁.target
    exact hz1
  let w₁ : MorseModel (m + 1) := ψ₁.symm (a, z)
  have hw₁src : w₁ ∈ ψ₁.source := ψ₁.map_target haz
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e₁ v)) w₁) levelSetLastBasis ≠ 0 := by
    rw [d₁.hψsource] at hw₁src
    exact hw₁src.2
  let smooth : MorseModel m → MorseModel m := fun z' =>
    (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2
  have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) smooth z := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z' : MorseModel m => (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2) z
    have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => (a, z')) z := by fun_prop
    have hsymm₁ : ContDiffAt ℝ (⊤ : ℕ∞)
        (ψ₁.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (a, z) := by
      refine OpenPartialHomeomorph.contDiffAt_symm ψ₁
        (f₀' := levelSetChartDerivEquiv g e₁ w₁ hc₁') haz ?_ ?_
      · rw [hψ₁]
        exact hasFDerivAt_levelSetChartMap g e₁ w₁ hg.contDiffAt hc₁'
      · rw [hψ₁]
        exact contDiffAt_levelSetChartMap g e₁ w₁ hg.contDiffAt
    have h₁ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => ψ₁.symm (a, z')) z :=
      hsymm₁.comp z hpair
    have hlin₁ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : MorseModel (m + 1) => levelSetReindex e₁ v) (ψ₁.symm (a, z)) :=
      ((levelSetReindex e₁).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have h₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => levelSetReindex e₁ (ψ₁.symm (a, z'))) z :=
      hlin₁.comp z h₁
    have hlin₂ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : MorseModel (m + 1) => levelSetReindex e₂ v)
        (levelSetReindex e₁ (ψ₁.symm (a, z))) :=
      ((levelSetReindex e₂).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have h₃ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : MorseModel m => levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z')))) z :=
      hlin₂.comp z h₂
    have hψ₂at : ContDiffAt ℝ (⊤ : ℕ∞) (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m)
        (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z)))) := by
      rw [hψ₂]
      exact contDiffAt_levelSetChartMap g e₂ _ hg.contDiffAt
    have h₄ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : MorseModel m => ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))) z :=
      hψ₂at.comp z h₃
    have hsnd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × MorseModel m => p.2)
        (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z))))) := by fun_prop
    exact hsnd.comp z h₄
  have hagree : (c₁.symm ≫ₕ c₂ : MorseModel m → MorseModel m) =ᶠ[𝓝 z] smooth := by
    have hzsrc : ∀ᶠ z' in 𝓝 z, z' ∈ (c₁.symm ≫ₕ c₂).source := by
      exact (isOpen_iff_mem_nhds.mp (c₁.symm ≫ₕ c₂).open_source z hz)
    filter_upwards [hzsrc] with z' hz'
    rw [OpenPartialHomeomorph.trans_apply]
    have hz'1 : z' ∈ c₁.target := by
      rw [OpenPartialHomeomorph.trans_source] at hz'
      exact hz'.1
    have hsymm' : c₁.symm z' =
        (⟨levelSetReindex e₁ (ψ₁.symm (a, z')), levelSetChart_invFun_mem g e₁ ψ₁ hψ₁
          (show (a, z') ∈ ψ₁.target from hz'1)⟩ : LevelSetSpace g a) := by
      change (if h : (a, z') ∈ ψ₁.target then
          (⟨levelSetReindex e₁ (ψ₁.symm (a, z')), levelSetChart_invFun_mem g e₁ ψ₁ hψ₁ h⟩ :
            LevelSetSpace g a)
        else ⟨x₁.1, x₁.2⟩) = (⟨levelSetReindex e₁ (ψ₁.symm (a, z')),
          levelSetChart_invFun_mem g e₁ ψ₁ hψ₁ (show (a, z') ∈ ψ₁.target from hz'1)⟩ :
            LevelSetSpace g a)
      rw [dif_pos (show (a, z') ∈ ψ₁.target from hz'1)]
    rw [hsymm']
    change (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2 = smooth z'
    rfl
  exact hsmooth.congr_of_eventuallyEq hagree

theorem levelSetChart_transition_contDiffOn {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : LevelSetSpace g a}
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
        (levelSetChart g a x₂ hg hr₂))
      ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ (levelSetChart g a x₂ hg hr₂)).source := by
  rw [IsOpen.contDiffOn_iff ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
      (levelSetChart g a x₂ hg hr₂)).open_source]
  intro z hz
  exact levelSetChart_transition_contDiffAt g a hg hr₁ hr₂ hz




@[reducible]
noncomputable def levelSetChartedSpace {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    ChartedSpace (MorseModel m) (LevelSetSpace g a) where
  atlas := Set.range (fun x : LevelSetSpace g a => levelSetChart g a x hg (hreg x.1 x.2))
  chartAt := fun x => levelSetChart g a x hg (hreg x.1 x.2)
  mem_chart_source := fun x => mem_levelSetChart_source g a x hg (hreg x.1 x.2)
  chart_mem_atlas := fun x => ⟨x, rfl⟩

@[reducible]
noncomputable def levelSetHasGroupoid {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @HasGroupoid (MorseModel m) _ (LevelSetSpace g a) _ (levelSetChartedSpace g a hg hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) := by
  letI := levelSetChartedSpace g a hg hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  change ContDiffOn ℝ (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m) ∘
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) ∘
      (𝓘(ℝ, MorseModel m)).symm)
      ((𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source ∩
        Set.range (𝓘(ℝ, MorseModel m)))
  have hfun : 𝓘(ℝ, MorseModel m) ∘
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) ∘
        (𝓘(ℝ, MorseModel m)).symm =
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) := by
    ext x
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  have hdom : (𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source ∩
        Set.range (𝓘(ℝ, MorseModel m)) =
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source := by
    ext x
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  rw [hfun, hdom]
  exact levelSetChart_transition_contDiffOn g a hg (hreg x₁.1 x₁.2) (hreg x₂.1 x₂.2)

@[reducible]
noncomputable def levelSetIsManifold {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @IsManifold ℝ _ (MorseModel m) _ _ (MorseModel m) _ (𝓘(ℝ, MorseModel m))
      (⊤ : ℕ∞) (LevelSetSpace g a) _ (levelSetChartedSpace g a hg hreg) := by
  letI := levelSetChartedSpace g a hg hreg
  exact { toHasGroupoid := levelSetHasGroupoid g a hg hreg }
end

abbrev MorseHalfSpace (m : ℕ) : Type := {x : MorseModel (m + 1) // 0 ≤ x (Fin.last m)}

theorem convex_morseHalfSpace (m : ℕ) :
    Convex ℝ ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set (MorseModel (m + 1))) := by
  exact convex_halfSpace_ge (f := fun x : MorseModel (m + 1) => x (Fin.last m)) (by
    refine ⟨?_, ?_⟩
    · intro x y
      rfl
    · intro c x
      rfl) (0 : ℝ)

theorem isOpen_morseHalfSpace_interior (m : ℕ) :
    IsOpen ({x : MorseModel (m + 1) | 0 < x (Fin.last m)}) := by
  exact isOpen_Ioi.preimage (continuous_apply (Fin.last m))

theorem interior_morseHalfSpace_nonempty (m : ℕ) :
    (interior ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set (MorseModel (m + 1)))).Nonempty := by
  refine ⟨fun _ : Fin (m + 1) => (1 : ℝ), ?_⟩
  have h₁ : (fun _ : Fin (m + 1) => (1 : ℝ)) ∈ interior {x : MorseModel (m + 1) | 0 < x (Fin.last m)} := by
    rw [(isOpen_morseHalfSpace_interior m).interior_eq]
    simp
  exact interior_mono (by
    intro x hx
    change 0 < x (Fin.last m) at hx
    exact le_of_lt hx) h₁

noncomputable def morseHalfSpaceClamp {m : ℕ} (x : MorseModel (m + 1)) : MorseModel (m + 1) :=
  HAdd.hAdd x (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis)

theorem morseHalfSpaceClamp_last (m : ℕ) (x : MorseModel (m + 1)) :
    morseHalfSpaceClamp x (Fin.last m) = max (x (Fin.last m)) 0 := by
  by_cases h : 0 ≤ x (Fin.last m)
  · have h1 : max (-(x (Fin.last m))) 0 = 0 := max_eq_right (by linarith)
    rw [morseHalfSpaceClamp, h1]
    rw [max_eq_left h]
    simp
  · have h1 : max (-(x (Fin.last m))) 0 = -(x (Fin.last m)) := max_eq_left (by linarith)
    rw [morseHalfSpaceClamp, h1]
    rw [max_eq_right (by linarith)]
    simp [levelSetLastBasis]

theorem morseHalfSpaceClamp_of_mem (m : ℕ) {x : MorseModel (m + 1)} (hx : 0 ≤ x (Fin.last m)) :
    morseHalfSpaceClamp x = x := by
  ext i
  by_cases hi : i = Fin.last m
  · subst i
    rw [morseHalfSpaceClamp_last]
    exact max_eq_left hx
  · have h0 : (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis) i = 0 := by
      simp [levelSetLastBasis, hi, Pi.smul_apply, smul_eq_mul]
    simp [morseHalfSpaceClamp, h0]

noncomputable def morseModelWithCornersHalfSpace (m : ℕ) :
    ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
  ModelWithCorners.ofConvexRange
    { toFun := fun x : MorseHalfSpace m => (x : MorseModel (m + 1))
      invFun := fun x : MorseModel (m + 1) =>
        ⟨morseHalfSpaceClamp x, by
          rw [morseHalfSpaceClamp_last]
          exact le_max_right _ _⟩
      source := Set.univ
      target := {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)}
      map_source' := by intro x hx; exact x.2
      map_target' := by intro x hx; trivial
      left_inv' := by
        intro x hx
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m x.2
      right_inv' := by
        intro x hx
        exact morseHalfSpaceClamp_of_mem m hx }
    rfl (convex_morseHalfSpace m)
    (by fun_prop)
    (by
      have hcont : Continuous (morseHalfSpaceClamp (m := m)) := by
        change Continuous (fun x : MorseModel (m + 1) =>
          HAdd.hAdd x (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis))
        fun_prop
      exact Continuous.subtype_mk hcont (fun x => by
        rw [morseHalfSpaceClamp_last]
        exact le_max_right _ _))
    (interior_morseHalfSpace_nonempty m)

theorem sublevelBoundaryChart_invFun_mem {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (a : ℝ)
    (ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m))
    (hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e)
    {z : MorseHalfSpace m} (hz : (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target) :
    g (levelSetReindex e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))) ≤ a := by
  have hval : (ψ (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))).1 =
      a - (z : MorseModel (m + 1)) (Fin.last m) := by
    rw [ψ.right_inv hz]
  have h1 : (ψ (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))).1 =
      g (levelSetReindex e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
        levelSetSplitFst m (z : MorseModel (m + 1))))) := by
    rw [hψ]
    rfl
  rw [← h1]
  rw [hval]
  linarith [z.2]

noncomputable def sublevelBoundaryChart {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  let inv : MorseHalfSpace m → SublevelSpace g a := fun z =>
    if hz : (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
      ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1)))),
        sublevelBoundaryChart_invFun_mem g d.e a ψ hψ hz⟩
    else ⟨x.1, x.2⟩
  let toFunVal : SublevelSpace g a → MorseModel (m + 1) := fun y =>
    levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
        a - (ψ (levelSetReindex d.e y.1)).1)
  let toFun' : SublevelSpace g a → MorseHalfSpace m := fun y =>
    ⟨toFunVal y, by
      change 0 ≤ (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
          a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m)
      have h1 : (ψ (levelSetReindex d.e y.1)).1 =
          g (levelSetReindex d.e (levelSetReindex d.e y.1)) := by
        rw [hψ]
        rfl
      rw [h1]
      rw [d.he, levelSetReindex_swap_swap]
      simp [levelSetSplit]
      linarith [show g y.1 ≤ a from y.2]⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := inv
          source := {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
          target := {z : MorseHalfSpace m |
            (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target}
          map_source' := by
            intro y hy
            change (a - (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
              levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1))) ∈ ψ.target
            have hlast : (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m) =
                a - (ψ (levelSetReindex d.e y.1)).1 := by
              simp [levelSetSplit]
            have hp : levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) =
                levelSetSplitFst m (levelSetReindex d.e y.1) := by
              rw [levelSetSplitFst_split]
            rw [hlast, hp]
            have hpair : (a - (a - (ψ (levelSetReindex d.e y.1)).1),
                levelSetSplitFst m (levelSetReindex d.e y.1)) = ψ (levelSetReindex d.e y.1) := by
              apply Prod.ext
              · ring
              · have hpp : levelSetSplitFst m (levelSetReindex d.e y.1) =
                    (ψ (levelSetReindex d.e y.1)).2 := by
                  rw [hψ]
                  rfl
                rw [hpp]
            rw [hpair]
            exact ψ.map_source hy
          map_target' := by
            intro z hz
            change levelSetReindex d.e ((inv z).1) ∈ ψ.source
            change levelSetReindex d.e ((if h : (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
                  (⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m (z : MorseModel (m + 1)))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩ : SublevelSpace g a)
                else ⟨x.1, x.2⟩).1) ∈ ψ.source
            simp only [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact ψ.map_target hz
          left_inv' := by
            intro y hy
            have h1 : (ψ (levelSetReindex d.e y.1)).1 =
                g (levelSetReindex d.e (levelSetReindex d.e y.1)) := by
              rw [hψ]
              rfl
            have hlast : (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m) =
                a - (ψ (levelSetReindex d.e y.1)).1 := by
              simp [levelSetSplit]
            have hp : levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) =
                levelSetSplitFst m (levelSetReindex d.e y.1) := by
              rw [levelSetSplitFst_split]
            have hpair : (a - (a - (ψ (levelSetReindex d.e y.1)).1),
                levelSetSplitFst m (levelSetReindex d.e y.1)) = ψ (levelSetReindex d.e y.1) := by
              apply Prod.ext
              · ring
              · have hpp : levelSetSplitFst m (levelSetReindex d.e y.1) =
                    (ψ (levelSetReindex d.e y.1)).2 := by
                  rw [hψ]
                  rfl
                rw [hpp]
            have hz : (a - toFunVal y (Fin.last m), levelSetSplitFst m (toFunVal y)) ∈ ψ.target := by
              change (a - (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
                levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1))) ∈ ψ.target
              rw [hlast, hp, hpair]
              exact ψ.map_source hy
            change inv (toFun' y) = y
            change (if h : (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((toFun' y : MorseModel (m + 1)))) ∈ ψ.target then
                  ⟨levelSetReindex d.e (ψ.symm (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m ((toFun' y : MorseModel (m + 1))))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩
                else ⟨x.1, x.2⟩) = y
            rw [dif_pos (show (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((toFun' y : MorseModel (m + 1)))) ∈ ψ.target from by
                change (a - toFunVal y (Fin.last m), levelSetSplitFst m (toFunVal y)) ∈ ψ.target
                exact hz)]
            apply Subtype.ext
            change levelSetReindex d.e (ψ.symm (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((toFun' y : MorseModel (m + 1))))) = y.1
            change levelSetReindex d.e (ψ.symm (a - toFunVal y (Fin.last m),
                levelSetSplitFst m (toFunVal y))) = y.1
            change levelSetReindex d.e (ψ.symm (a - (levelSetSplit m (levelSetSplitFst m
                (levelSetReindex d.e y.1), a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
                levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1)))) = y.1
            rw [hlast, hp]
            rw [hpair]
            have hleft : ψ.symm (ψ (levelSetReindex d.e y.1)) = levelSetReindex d.e y.1 :=
              ψ.left_inv hy
            rw [hleft]
            rw [d.he, levelSetReindex_swap_swap]
          right_inv' := by
            intro z hz
            change (toFun' (if h : (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
                  ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m (z : MorseModel (m + 1)))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩
                else ⟨x.1, x.2⟩)) = z
            rw [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target from hz)]
            apply Subtype.ext
            change toFunVal ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1)))), _⟩ = (z : MorseModel (m + 1))
            let t : ℝ := a - (z : MorseModel (m + 1)) (Fin.last m)
            let y' : MorseModel m := levelSetSplitFst m (z : MorseModel (m + 1))
            let w : MorseModel (m + 1) := ψ.symm (t, y')
            change levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e (levelSetReindex d.e w)),
                a - (ψ (levelSetReindex d.e (levelSetReindex d.e w))).1) = (z : MorseModel (m + 1))
            have hpair : ψ w = (t, y') := by
              simpa [t, y', w] using ψ.right_inv hz
            have hG : (ψ (levelSetReindex d.e (levelSetReindex d.e w))).1 = t := by
              rw [hψ]
              simp only [levelSetChartMap]
              rw [d.he, levelSetReindex_swap_swap, ← d.he]
              have h1 : (ψ w).1 = g (levelSetReindex d.e w) := by
                rw [hψ]
                rfl
              rw [← h1]
              exact congrArg Prod.fst hpair
            have hp : levelSetSplitFst m (levelSetReindex d.e (levelSetReindex d.e w)) = y' := by
              rw [d.he, levelSetReindex_swap_swap]
              have h1 : levelSetSplitFst m w = (ψ w).2 := by
                rw [hψ]
                rfl
              rw [h1]
              exact congrArg Prod.snd hpair
            rw [hG, hp]
            change levelSetSplit m (y', a - t) = (z : MorseModel (m + 1))
            have ht : a - t = (z : MorseModel (m + 1)) (Fin.last m) := by
              dsimp [t]
              ring
            rw [ht]
            change levelSetSplit m ((levelSetSplitFst m (z : MorseModel (m + 1))),
                (z : MorseModel (m + 1)) (Fin.last m)) = (z : MorseModel (m + 1))
            change levelSetSplit m ((levelSetSplit m).symm (z : MorseModel (m + 1))) =
                (z : MorseModel (m + 1))
            exact (levelSetSplit m).apply_symm_apply (z : MorseModel (m + 1)) }
      open_source := by
        have hcont : Continuous (fun y : SublevelSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        exact ψ.open_source.preimage hcont
      open_target := by
        have hcont1 : Continuous (fun z : MorseHalfSpace m =>
            a - (z : MorseModel (m + 1)) (Fin.last m)) :=
          continuous_const.sub ((continuous_apply (Fin.last m)).comp continuous_subtype_val)
        have hcont2 : Continuous (fun z : MorseHalfSpace m =>
            levelSetSplitFst m (z : MorseModel (m + 1))) :=
          (levelSetSplitFst m).continuous.comp continuous_subtype_val
        have hcont : Continuous (fun z : MorseHalfSpace m =>
            (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1)))) :=
          hcont1.prodMk hcont2
        exact ψ.open_target.preimage hcont
      continuousOn_toFun := by
        have hf : Continuous (fun y : SublevelSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        have hcomp : ContinuousOn (fun y : SublevelSpace g a => ψ (levelSetReindex d.e y.1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          ψ.continuousOn.comp hf.continuousOn (by intro y hy; exact hy)
        have hc1 : ContinuousOn (fun y : SublevelSpace g a =>
            levelSetSplitFst m (levelSetReindex d.e y.1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          (levelSetSplitFst m).continuous.comp_continuousOn hf.continuousOn
        have hc2 : ContinuousOn (fun y : SublevelSpace g a =>
            a - (ψ (levelSetReindex d.e y.1)).1)
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} := by
          have hc2' : ContinuousOn (fun y : SublevelSpace g a =>
              (ψ (levelSetReindex d.e y.1)).1)
              {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
            continuous_fst.comp_continuousOn hcomp
          simpa [sub_eq_add_neg] using
            (continuous_const.sub continuous_id).comp_continuousOn hc2'
        have hpair : ContinuousOn (fun y : SublevelSpace g a =>
            (levelSetSplitFst m (levelSetReindex d.e y.1),
              a - (ψ (levelSetReindex d.e y.1)).1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          hc1.prodMk hc2
        have hunder : ContinuousOn (fun y : SublevelSpace g a =>
            levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
              a - (ψ (levelSetReindex d.e y.1)).1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          (by
            have hsplit : Continuous (levelSetSplit m) := (levelSetSplit m).toContinuousLinearEquiv.continuous
            exact hsplit.comp_continuousOn hpair)
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hrest : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => toFunVal x.1) := by
          exact continuousOn_iff_continuous_restrict.mp (by
            change ContinuousOn (fun y : SublevelSpace g a =>
                levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1))
                {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
            exact hunder)
        have hsub : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => (⟨toFunVal x.1, (toFun' x.1).2⟩ :
              MorseHalfSpace m)) :=
          Continuous.subtype_mk hrest (fun x => (toFun' x.1).2)
        have hcongr : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => toFun' x.1) := by
          refine hsub.congr ?_
          intro x
          exact (Subtype.ext rfl).symm
        exact hcongr
      continuousOn_invFun := by
        let s : Set (MorseHalfSpace m) := {z | (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target}
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hc : Continuous (fun z : s =>
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) := by
          have hc1 : Continuous (fun z : s =>
              a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m)) :=
            continuous_const.sub (((continuous_apply (Fin.last m)).comp continuous_subtype_val).comp continuous_subtype_val)
          have hc2 : Continuous (fun z : s =>
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) :=
            (levelSetSplitFst m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
          exact hc1.prodMk hc2
        have hc0 : Continuous (fun z : s => ψ.symm
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) := by
          have hc0' : ContinuousOn (fun z : s => ψ.symm
              (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) (Set.univ : Set s) := by
            refine ψ.symm.continuousOn.comp hc.continuousOn ?_
            intro z hz
            exact z.2
          exact continuousOn_univ.mp hc0'
        have hc1 : Continuous (fun z : s =>
            (⟨levelSetReindex d.e (ψ.symm
                (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
              sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
                (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)⟩ :
                  SublevelSpace g a)) :=
          Continuous.subtype_mk
            (((levelSetReindex d.e).toContinuousLinearEquiv :
              MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp hc0)
            (fun z : s => sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
              (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2))
        refine hc1.congr ?_
        intro z
        change (⟨levelSetReindex d.e (ψ.symm
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
          sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
            (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)⟩ :
                SublevelSpace g a) =
          (if hz : (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target then
                (⟨levelSetReindex d.e (ψ.symm (a - ((z : MorseHalfSpace m) : MorseModel (m + 1))
                  (Fin.last m), levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
                  sublevelBoundaryChart_invFun_mem g d.e a ψ hψ hz⟩ : SublevelSpace g a)
              else ⟨x.1, x.2⟩)
        rw [dif_pos (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)] }


theorem mem_sublevelBoundaryChart_source {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    x ∈ (sublevelBoundaryChart g a x hx hg hreg).source := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  change levelSetReindex d.e x.1 ∈ d.ψ.source
  rw [d.hψsource]
  constructor
  · rw [← d.hu₁]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source (f := levelSetChartMap g d.e)
      (contDiffAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt))
      (hasFDerivAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt) d.hc)
      (by norm_num)
  · rw [← d.hu₁]
    exact d.hc

theorem sublevelBoundaryChart_extend_last_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    (sublevelBoundaryChart g a x hx hg hreg).extend (morseModelWithCornersHalfSpace m) x
        (Fin.last m) = 0 := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  rw [OpenPartialHomeomorph.extend_coe]
  change (morseModelWithCornersHalfSpace m) (⟨levelSetSplit m (levelSetSplitFst m
      (levelSetReindex d.e x.1), a - (ψ (levelSetReindex d.e x.1)).1), by
        have h1 : (ψ (levelSetReindex d.e x.1)).1 =
            g (levelSetReindex d.e (levelSetReindex d.e x.1)) := by
          rw [hψ]
          rfl
        rw [h1]
        rw [d.he, levelSetReindex_swap_swap]
        simp [levelSetSplit]
        linarith [show g x.1 ≤ a from x.2]⟩ : MorseHalfSpace m)
      (Fin.last m) = 0
  change (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e x.1),
      a - (ψ (levelSetReindex d.e x.1)).1)) (Fin.last m) = 0
  have h1 : (ψ (levelSetReindex d.e x.1)).1 =
      g (levelSetReindex d.e (levelSetReindex d.e x.1)) := by
    rw [hψ]
    rfl
  rw [h1]
  rw [d.he, levelSetReindex_swap_swap]
  simp [levelSetSplit]
  linarith

end DifferentialGeometry.Topology.Morse
