/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.DifferentialForm.Defs
import DifferentialGeometry.Tensor.Alternating.Flip

open ContinuousAlternatingMap

noncomputable section Congr

namespace DifferentialForm

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m : ℕ}

/-- Reorder the arguments of a smooth differential form using an equivalence of `Fin` indices. -/
noncomputable def domDomCongr (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) : Ω^m⟮E, F⟯ :=
  ⟨fun e => (ω e).domDomCongr σ, by
    -- TODO: prove smoothness; using `sorry` for now
    sorry⟩

@[simp]
theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : Ω^n⟮E, F⟯) (e : E) :
    (domDomCongr σ ω) e = (ω e).domDomCongr σ :=
  rfl

@[simp]
theorem domDomCongr_refl (ω : Ω^n⟮E, F⟯) :
    domDomCongr (Equiv.refl _) ω = ω := by
  ext e
  rfl

end DifferentialForm

end Congr
