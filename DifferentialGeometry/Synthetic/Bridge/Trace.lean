/-
Copyright (c) 2026 Differential Geometry Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DifferentialGeometry.Synthetic.Bridge.Basic
import DifferentialGeometry.VectorBundle.Section

/-!
# Bridge Layer 1: Trace construction

This file constructs the trace components of `AbstractTrace` for the concrete
instantiation `R = C^∞(M, ℝ)`, `V = Γ(TM)`.

Given an endomorphism `L : Γ(TM) →ₗ[C^∞(M)] Γ(TM)`, we apply the Vector Bundle
Characterization (VBC) lemma to obtain a smooth bundle endomorphism with fiberwise
linear maps `φ(x) : TangentSpace I x →ₗ[ℝ] TangentSpace I x`. The trace is defined
fiberwise as `tr(L)(x) := LinearMap.trace ℝ (TangentSpace I x) (φ(x))`.

## Main definitions

* `concreteTr` : the trace map
    `(Γ(TM) →ₗ[C^∞(M)] Γ(TM)) →ₗ[C^∞(M)] C^∞(M)`

## Main results

* `concreteTr_outer` : `tr(α.smulRight v) = α v`
* `concreteTr_comm` : `tr(A * B) = tr(B * A)`
-/

noncomputable section

set_option autoImplicit false

open scoped Manifold ContDiff
open Bundle

section TraceConstruction

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### VBC fiberwise map and its properties -/

/-- Apply VBC to a `C^∞(M)`-linear endomorphism on sections to get the fiberwise linear map. -/
private def vbcFiber
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  exact (ContMDiffVectorBundleHom.ofLinearMapSection (I := I) (n := (⊤ : ℕ∞)) L).fiberLinearMap x

/-- The fundamental VBC specification: the fiberwise map agrees with the section map. -/
private theorem vbcFiber_spec
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) :
    vbcFiber I M L x (σ x) = (L σ) x := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  exact ContMDiffVectorBundleHom.linearMap_acts_pointwise
    (I := I) (n := (⊤ : ℕ∞)) L _ σ x
    (ContMDiffSection.exists_eq_at x (σ x)).choose_spec

/-- The fiberwise map is additive in L. -/
private theorem vbcFiber_add
    (L₁ L₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) : vbcFiber I M (L₁ + L₂) x = vbcFiber I M L₁ x + vbcFiber I M L₂ x := by
  ext v
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  simp only [LinearMap.add_apply]
  rw [← hσ, vbcFiber_spec, vbcFiber_spec, vbcFiber_spec]
  rfl

/-- The fiberwise map is `C^∞(M)`-homogeneous in L. -/
private theorem vbcFiber_smul
    (f : C^∞⟮I, M; ℝ⟯)
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) : vbcFiber I M (f • L) x = f x • vbcFiber I M L x := by
  ext v
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  simp only [LinearMap.smul_apply]
  rw [← hσ, vbcFiber_spec, vbcFiber_spec]
  change ((f • L) σ) x = f x • (L σ) x
  simp [ContMDiffSection.coe_smulContMDiffMap]

/-- The fiberwise map respects composition. -/
private theorem vbcFiber_mul
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
           Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) : vbcFiber I M (A * B) x = vbcFiber I M A x * vbcFiber I M B x := by
  ext v
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  change vbcFiber I M (A * B) x v = (vbcFiber I M A x) ((vbcFiber I M B x) v)
  rw [← hσ, vbcFiber_spec]
  -- Goal: (A (B σ)) x = vbcFiber I M A x (vbcFiber I M B x (σ x))
  conv_rhs => rw [vbcFiber_spec I M B σ x]
  exact (vbcFiber_spec I M A (B σ) x).symm

/-! ### Smoothness of the trace -/

/-- The pointwise trace function. -/
private def concreteTr_fun
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => LinearMap.trace ℝ (TangentSpace I x) (vbcFiber I M L x)

/-- The trace function is smooth. -/
private theorem concreteTr_fun_smooth
    (L : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
         Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (concreteTr_fun I M L) := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  intro x₀
  -- Get a local frame near x₀
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
  let b := Module.finBasis ℝ E
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
  obtain ⟨σ', hσ'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  -- The trace equals ∑ᵢ b.equivFun ((e ⟨x, (L (σ' i)) x⟩).2) i near x₀
  -- because trace(φ_x) = ∑ᵢ eᵢ*(φ_x(eᵢ)) and in the trivialization
  -- eᵢ = le⁻¹(bᵢ) = σ'ᵢ(x), so φ_x(eᵢ) = (L σ'ᵢ)(x) by VBC.
  have htr_eq : ∀ᶠ x in nhds x₀,
      concreteTr_fun I M L x =
        ∑ i, b.equivFun ((e ⟨x, (L (σ' i)) x⟩).2) i := by
    filter_upwards [hσ', e.open_baseSet.mem_nhds he] with x hσ'x hx
    let le := e.linearEquivAt ℝ x hx
    -- trace(vbcFiber L x) using the basis {le⁻¹(bᵢ)} of TangentSpace I x
    -- = ∑ᵢ (le⁻¹(bᵢ))*.repr(vbcFiber L x (le⁻¹(bᵢ)))(i)
    -- where (le⁻¹(bᵢ))* is the dual basis.
    -- In coordinates via le: trace = ∑ᵢ b.equivFun(le(vbcFiber L x (le⁻¹(bᵢ))))(i)
    -- = ∑ᵢ b.equivFun(le(L(σ'ᵢ)(x)))(i)    [by VBC and σ'ᵢ(x) = le⁻¹(bᵢ)]
    -- = ∑ᵢ b.equivFun((e ⟨x, L(σ'ᵢ)(x)⟩).2)(i)   [since (e ⟨x, v⟩).2 = le(v)]
    change LinearMap.trace ℝ (TangentSpace I x) (vbcFiber I M L x) =
      ∑ i, b.equivFun ((e ⟨x, (L (σ' i)) x⟩).2) i
    -- The trace of the fiberwise endomorphism equals the trace of its
    -- conjugation to E via the trivialization linear equiv.
    -- trace(φ_x) = trace(le ∘ φ_x ∘ le⁻¹) since trace is conjugation-invariant.
    -- The i-th diagonal entry of le ∘ φ_x ∘ le⁻¹ in basis b is
    -- b.equivFun(le(φ_x(le⁻¹(bᵢ))))(i) = b.equivFun((e ⟨x, (L σ'ᵢ)(x)⟩).2)(i)
    -- Conjugate to E via le to use trace invariance under conjugation
    rw [← LinearMap.trace_conj' (vbcFiber I M L x) le]
    rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
    congr 1; ext i
    -- φ_E (b i) = le (vbcFiber L x (le.symm (b i))) = le ((L σ'ᵢ)(x)) = (e ⟨x, (L σ'ᵢ)(x)⟩).2
    have hσ'_eq : (σ' i) x = le.symm (b i) := by
      rw [hσ'x i]
      simp [Trivialization.localFrame, Trivialization.basisAt, hx, le]
    have hconj : le.conj (vbcFiber I M L x) (b i) = (e ⟨x, (L (σ' i)) x⟩).2 := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [show le.symm (b i) = (σ' i) x from hσ'_eq.symm]
      rw [vbcFiber_spec I M L (σ' i) x]
      -- le v = (e ⟨x, v⟩).2 by definition of linearEquivAt
      simp [le]
    rw [hconj]; rfl
  refine (ContMDiffAt.congr_of_eventuallyEq ?_ htr_eq).contMDiffWithinAt
  apply ContMDiffAt.sum
  intro i _
  -- b.equivFun ((e ⟨x, (L (σ' i)) x⟩).2) i is a composition of smooth maps:
  -- x ↦ (e ⟨x, (L (σ' i)) x⟩).2 is smooth (L(σ'ᵢ) is a smooth section)
  -- w ↦ b.equivFun w i is a CLM (coordinate projection)
  have h_sect : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun x => (e ⟨x, (L (σ' i)) x⟩).2) x₀ :=
    (contMDiffAt_section x₀).mp (L (σ' i)).contMDiff.contMDiffAt
  have hcl : ContDiff ℝ ∞ (fun w : E => b.equivFun w i) :=
    (ContinuousLinearMap.proj i |>.comp
      b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
  exact hcl.contDiffAt.contMDiffAt.comp _ h_sect

/-! ### The trace map -/

/-- The trace map: a `C^∞(M)`-linear map from section endomorphisms to smooth functions. -/
noncomputable def concreteTr :
    (Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
     Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) →ₗ[C^∞⟮I, M; ℝ⟯]
    C^∞⟮I, M; ℝ⟯ where
  toFun L := ⟨concreteTr_fun I M L, concreteTr_fun_smooth I M L⟩
  map_add' L₁ L₂ := by
    ext x
    change concreteTr_fun I M (L₁ + L₂) x =
      concreteTr_fun I M L₁ x + concreteTr_fun I M L₂ x
    simp only [concreteTr_fun]
    rw [vbcFiber_add I M L₁ L₂ x]
    exact map_add (LinearMap.trace ℝ (TangentSpace I x)) _ _
  map_smul' f L := by
    ext x
    change concreteTr_fun I M (f • L) x = f x * concreteTr_fun I M L x
    simp only [concreteTr_fun]
    rw [vbcFiber_smul I M f L x, LinearMap.map_smul, smul_eq_mul]

/-! ### Auxiliary: pointwise action of C^∞(M)-linear maps to smooth functions -/

/-- A `C^∞(M)`-linear map `α : Γ(TM) → C^∞(M)` acts pointwise:
    if `σ₁(x) = σ₂(x)` then `(α σ₁)(x) = (α σ₂)(x)`. -/
private theorem smoothLinearMap_acts_pointwise
    (α : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (σ₁ σ₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (p : M)
    (h : σ₁ p = σ₂ p) :
    (α σ₁) p = (α σ₂) p := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  suffices hsuff : ∀ (τ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      τ p = 0 → (α τ) p = 0 by
    have h₁ := hsuff (σ₁ - σ₂) (by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact h)
    simp only [map_sub, ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
    exact h₁
  intro τ hτ
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from by
      simp)
  let e := trivializationAt E (TangentSpace I : M → Type _) p
  let bE := Module.finBasis ℝ E
  have he : p ∈ e.baseSet := mem_baseSet_trivializationAt E _ p
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) bE
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  obtain ⟨χ, -, hχsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
    (e.open_baseSet.mem_nhds he)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(ℝ) (↑(⊤ : ℕ∞))
      (fun x => χ x • hframe.coeff i x (τ x)) := by
    intro i
    have hsmooth_lfc : ContMDiff I 𝓘(ℝ) (↑(⊤ : ℕ∞))
        (fun x => χ x • e.localFrame_coeff I bE i x (τ x)) := by
      intro x
      by_cases hx : x ∈ tsupport (χ : M → ℝ)
      · exact (χ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.smul
          (contMDiffAt_localFrame_coeff bE (hχsupp hx) τ.contMDiff.contMDiffAt i)
      · have hχ_zero : ∀ᶠ y in nhds x, (χ : M → ℝ) y = 0 :=
          Filter.Eventually.mono
            ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hx)
            fun y hy => (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
        exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          (hχ_zero.mono fun y hy => by simp [hy])
    refine hsmooth_lfc.congr fun x => ?_
    by_cases hx : x ∈ e.baseSet
    · have hbasis : e.basisAt bE hx = hframe.toBasisAt hx := by
        ext j; simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame,
          Trivialization.basisAt, hx]
      simp only [hframe.coeff_apply_of_mem hx,
        e.localFrame_coeff_apply_of_mem_baseSet bE hx, hbasis]
    · simp [hframe.coeff_apply_of_notMem hx,
        e.localFrame_coeff_apply_of_notMem_baseSet bE hx]
  let u' : Fin (Module.finrank ℝ E) → C^∞⟮I, M; ℝ⟯ := fun i =>
    ⟨fun x => χ x • hframe.coeff i x (τ x), hcoeff_smooth i⟩
  have hu'_zero : ∀ i, (u' i) p = 0 := fun i => by
    change χ p • hframe.coeff i p (τ p) = 0
    rw [χ.eq_one, one_smul, hτ, map_zero]
  have hτ_eq_near : ∀ᶠ x in nhds p, τ x = ∑ i, (u' i) x • (s' i) x := by
    filter_upwards [hs', χ.eventuallyEq_one, e.open_baseSet.mem_nhds he] with x hs'x hχx hx
    change τ x = ∑ i, (χ x • hframe.coeff i x (τ x)) • (s' i) x
    simp only [show χ x = (1 : M → ℝ) x from hχx, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq (⇑τ) hx]
    congr 1; ext i; rw [hs'x i]
  -- α acts locally
  have h_acts_locally :
      ∀ (σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {U : Set M}
        (hU : IsOpen U) (hσU : ∀ x ∈ U, σ x = 0),
      ∀ q ∈ U, (α σ) q = 0 := by
    intro σ U hU hσU q hq
    obtain ⟨ψ, -, hψsupp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) q).mem_iff.mp (hU.mem_nhds hq)
    let ψ' : C^∞⟮I, M; ℝ⟯ :=
      ⟨ψ, ψ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
    have hψσ : ψ' • σ = 0 := by
      ext x
      simp only [ContMDiffSection.coe_smulContMDiffMap, Pi.zero_apply,
        ContMDiffSection.coe_zero]
      by_cases hx : x ∈ Function.support (ψ : M → ℝ)
      · exact smul_eq_zero_of_right _ (hσU x (hψsupp (subset_closure hx)))
      · simp only [Function.mem_support, not_not] at hx
        exact smul_eq_zero_of_left hx _
    have key : α (ψ' • σ) = 0 := by rw [hψσ, map_zero]
    have key2 : ψ' • (α σ) = 0 := by rw [← α.map_smul]; exact key
    have h0 := DFunLike.congr_fun key2 q
    simp only [ContMDiffMap.coe_zero, Pi.zero_apply] at h0
    -- h0 : (ψ' • α σ) q = 0, which is ψ'(q) • (α σ)(q) = 0
    -- For C^∞(M) acting on C^∞(M), smul is mul
    change ψ' q • (α σ) q = 0 at h0
    rw [show (ψ' q : ℝ) = 1 from ψ.eq_one, one_smul] at h0
    exact h0
  obtain ⟨W, hW_open, hpW, hW_vanish⟩ : ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, (τ - ∑ i, u' i • s' i) x = 0 := by
    obtain ⟨W, hW_nhds, hW⟩ := Filter.Eventually.exists_mem hτ_eq_near
    obtain ⟨W', hW'W, hW'_open, hpW'⟩ := mem_nhds_iff.mp hW_nhds
    exact ⟨W', hW'_open, hpW', fun x hx => by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero,
        ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      exact hW x (hW'W hx)⟩
  have h_local := h_acts_locally (τ - ∑ i, u' i • s' i) hW_open hW_vanish p hpW
  rw [map_sub, ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at h_local
  rw [h_local, map_sum]
  simp_rw [α.map_smul]
  -- The goal is (∑ i, u' i • α (s' i)) p = 0.
  -- We need to evaluate pointwise. Use the algebra hom ContMDiffMap.evalAlgHom.
  -- Actually, use the ring hom evaluation
  let evalp : C^∞⟮I, M; ℝ⟯ →+* ℝ := ContMDiffMap.evalRingHom p
  -- The RHS is evalp applied to the sum
  change evalp (∑ i, u' i • α (s' i)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  -- evalp (u' i • α (s' i)) = evalp (u' i) * evalp (α (s' i)) = 0 * ... = 0
  change evalp (u' i • α (s' i)) = 0
  rw [show u' i • α (s' i) = u' i * α (s' i) from rfl, map_mul]
  simp [evalp, ContMDiffMap.evalRingHom, hu'_zero i]

/-! ### trace_outer: tr(α.smulRight v) = α v -/

/-- The trace of a smulRight endomorphism equals evaluation: `tr(α.smulRight v) = α v`. -/
theorem concreteTr_outer
    (v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    concreteTr I M (α.smulRight v) = α v := by
  ext x
  change concreteTr_fun I M (α.smulRight v) x = (α v) x
  simp only [concreteTr_fun]
  -- Define the fiberwise linear functional α_x
  let α_x : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun w =>
        (α (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose) x
      map_add' := fun w₁ w₂ => by
        set σ₁ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₁).choose
        set σ₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₂).choose
        set σ₁₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (w₁ + w₂)).choose
        have h₁ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₁).choose_spec
        have h₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₂).choose_spec
        have h₁₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (w₁ + w₂)).choose_spec
        have h_ptwise : (α σ₁₂) x = (α (σ₁ + σ₂)) x :=
          smoothLinearMap_acts_pointwise I M α σ₁₂ (σ₁ + σ₂) x (by
            rw [h₁₂, ContMDiffSection.coe_add, Pi.add_apply, h₁, h₂])
        rw [h_ptwise, map_add]
        rfl
      map_smul' := fun c w => by
        set σ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose
        set σ_c := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (c • w)).choose
        have hσ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose_spec
        have hσ_c := (ContMDiffSection.exists_eq_at (I := I) (F := E)
          (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (c • w)).choose_spec
        let c' : C^∞⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
        have h_ptwise : (α σ_c) x = (α (c' • σ)) x :=
          smoothLinearMap_acts_pointwise I M α σ_c (c' • σ) x (by
            rw [hσ_c]
            show c • w = (c' • σ) x
            simp only [ContMDiffSection.coe_smulContMDiffMap, c']
            congr 1; exact hσ.symm)
        rw [h_ptwise, α.map_smul]
        simp only [smul_eq_mul, RingHom.id_apply, c']
        rfl }
  -- Show vbcFiber (α.smulRight v) x = α_x.smulRight (v x)
  have hfiber_eq : vbcFiber I M (α.smulRight v) x = α_x.smulRight (v x) := by
    ext w
    obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    simp only [LinearMap.smulRight_apply]
    rw [← hσ, vbcFiber_spec]
    -- Goal: ((α.smulRight v) σ) x = α_x (σ x) • v x
    -- LHS = ((α σ) • v) x = (α σ)(x) • v(x)
    -- RHS = α_x (σ x) • v(x) = (α σ_{σ(x)})(x) • v(x)
    -- These are equal because α acts pointwise
    suffices h : α_x (σ x) = (α σ) x by
      simp only [LinearMap.smulRight_apply] at *
      change (α σ) x • v x = α_x (σ x) • v x
      rw [h]
    -- α_x (σ x) = (α choose_{σ(x)})(x) = (α σ)(x) by pointwise
    change (α (ContMDiffSection.exists_eq_at x (σ x)).choose) x = (α σ) x
    exact smoothLinearMap_acts_pointwise I M α _ σ x
      (ContMDiffSection.exists_eq_at x (σ x)).choose_spec
  rw [hfiber_eq, LinearMap.trace_smulRight]
  -- Now α_x (v x) = (α v)(x) by pointwise
  change (α (ContMDiffSection.exists_eq_at x (v x)).choose) x = (α v) x
  exact smoothLinearMap_acts_pointwise I M α _ v x
    (ContMDiffSection.exists_eq_at x (v x)).choose_spec

/-! ### trace_comm: tr(A * B) = tr(B * A) -/

/-- The trace is cyclic: `tr(A * B) = tr(B * A)`. -/
theorem concreteTr_comm
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
           Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteTr I M (A * B) = concreteTr I M (B * A) := by
  ext x
  change concreteTr_fun I M (A * B) x = concreteTr_fun I M (B * A) x
  simp only [concreteTr_fun]
  rw [vbcFiber_mul I M A B x, vbcFiber_mul I M B A x]
  exact LinearMap.trace_mul_comm _ _ _

end TraceConstruction

end
