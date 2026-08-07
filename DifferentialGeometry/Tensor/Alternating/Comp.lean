





import DifferentialGeometry.Tensor.Multilinear.Comp
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional


open ContinuousAlternatingMap

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by
  let F₁ : MultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') := MultilinearMap.mk
    (toFun := fun v => (f (g v)).compContinuousAlternatingMap h)
    (map_update_add' := fun m i x y => by
      simp only [ContinuousAlternatingMap.map_update_add, map_add]
      congr)
    (map_update_smul' := fun m i c x => by
      dsimp
      rw [ContinuousAlternatingMap.map_update_smul, ContinuousLinearMap.map_smul]
      congr)
  let F₂ : ContinuousMultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') :=
    F₁.mkContinuous (‖f‖ * ‖g‖ * ‖h‖) (H := by
      intro m
      unfold F₁
      simp only [MultilinearMap.coe_mk]
      apply ContinuousAlternatingMap.opNorm_le_bound
      · positivity
      intro m'
      simp only [compContinuousAlternatingMap_coe, Function.comp_apply]
      calc
        ‖(f (g m)) (h m')‖ ≤ ‖f (g m)‖ * ‖h m'‖ := ContinuousLinearMap.le_opNorm (f (g m)) (h m')
        _ ≤ ‖f (g m)‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousAlternatingMap.le_opNorm h m'
          positivity
        _ ≤ ‖f‖ * ‖g m‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact ContinuousLinearMap.le_opNorm f (g m)
          positivity
        _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖m i‖) * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact ContinuousAlternatingMap.le_opNorm g m
            positivity
          positivity
        _ = (‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
  exact ContinuousAlternatingMap.mk F₂ (map_eq_zero_of_eq' := by
    intro v i j h₁ h₂
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, F₂, F₁]
    have : g v = 0 := g.map_eq_zero_of_eq' v i j h₁ h₂
    rw [this, ContinuousLinearMap.map_zero]
    ext v'
    rfl)

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

noncomputable def _root_.LinearIsometry.compLeft {𝕜 : Type*} {𝕜₂ : Type*}
    {𝕜₃ : Type*} (E : Type*) {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] (σ₁₂ : 𝕜 →+* 𝕜₂) {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
    [RingHomIsometric σ₁₃] (f : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) :=
  { ContinuousLinearMap.compSL _ _ _ _ _ f.toContinuousLinearMap with
    norm_map' := fun _ ↦ f.norm_toContinuousLinearMap_comp }

omit [Fintype ι] in
theorem compContinuousAlternatingMapCLM_cont [Finite ι] :
    Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
    (M →L[𝕜] M') → (M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) := by
  letI := Fintype.ofFinite ι
  let φ : (M [⋀^ι]→L[𝕜] N) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  change Continuous (fun p : M →L[𝕜] M' ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜))
  exact Continuous.clm_comp compContinuousMultilinearMapL_diag_continuous continuous_const

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι ι' : Type*}
variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  [Fintype ι] [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  f.compContinuousAlternatingMap₂ g h

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

omit [Fintype ι] in
theorem compContinuousLinearMap_compContinuousLinearMap
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (L : E [⋀^ι]→L[𝕜] N) (A : E' →L[𝕜] E) (B : E'' →L[𝕜] E') :
    (L.compContinuousLinearMap A).compContinuousLinearMap B =
      L.compContinuousLinearMap (A ∘L B) := by
  ext v
  rfl

end ContinuousAlternatingMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

theorem ContinuousAlternatingMap.compContinuousLinearMapL_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  letI := Fintype.ofFinite ι
  let φ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] _ := ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) →ₗᵢ[𝕜] _ := φ.compLeft _ (RingHom.id _)
  rw [← Φ.comp_continuous_iff]
  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂).comp
    (toContinuousMultilinearMapCLM 𝕜))
  exact (ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous 𝕜 ι F₁ F₂).clm_comp
    continuous_const

end Continuous

section Smooth
variable {ι F₁ F₂} [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

open scoped Bundle Manifold

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
      (compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  classical
  let ψ : (F₁ [⋀^ι]→L[ℝ] F₂) →ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)) →ₗᵢ[ℝ]
      ((F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂) :=
    ψ.compLeft _ (RingHom.id ℝ)
  have hh : ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
      (Φ (compContinuousLinearMapCLM p) : (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
    have h₁ : ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
        (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι => p) :
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) :=
      ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff
    have h₂ : ContDiff ℝ ⊤ (fun M : (ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂) =>
        (M.comp (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ) :
          (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
      fun_prop
    convert h₂.comp h₁ using 1
  have heψ : IsClosed (Set.range (ψ : F₁ [⋀^ι]→L[ℝ] F₂ →
      ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
    exact (isClosedEmbedding_toContinuousMultilinearMap (𝕜 := ℝ) (E := F₁) (F := F₂)).isClosed_range
  have heΦ : IsClosed (Set.range Φ) := by
    simpa [Φ] using isClosed_range_comp ψ heψ
  exact contDiff_of_comp_linearIsometry_omega Φ heΦ hh

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    let F : (F₁ →L[ℝ] F₁) → (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁))) (𝓘(ℝ, ((F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
      (compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  classical
  let ψ : (F₁' [⋀^ι]→L[ℝ] F₂) →ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁') F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let ψ₀ : (F₁ [⋀^ι]→L[ℝ] F₂) →ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let Φ : ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)) →ₗᵢ[ℝ]
      ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂) :=
    ψ₀.compLeft _ (RingHom.id ℝ)
  have hh : ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
      (Φ (compContinuousLinearMapCLM p) : (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
    have h₁ : ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
        (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι => p) :
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁') F₂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) :=
      ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff_of_space
    have h₂ : ContDiff ℝ ⊤ (fun M : (ContinuousMultilinearMap ℝ (fun _ : ι => F₁') F₂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂) =>
        (M.comp (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ) :
          (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
      fun_prop
    convert h₂.comp h₁ using 1
  have heψ : IsClosed (Set.range (ψ : F₁' [⋀^ι]→L[ℝ] F₂ →
      ContinuousMultilinearMap ℝ (fun _ : ι => F₁') F₂)) := by
    exact (isClosedEmbedding_toContinuousMultilinearMap (𝕜 := ℝ) (E := F₁') (F := F₂)).isClosed_range
  have heψ₀ : IsClosed (Set.range (ψ₀ : F₁ [⋀^ι]→L[ℝ] F₂ →
      ContinuousMultilinearMap ℝ (fun _ : ι => F₁) F₂)) := by
    exact (isClosedEmbedding_toContinuousMultilinearMap (𝕜 := ℝ) (E := F₁) (F := F₂)).isClosed_range
  have heΦ : IsClosed (Set.range Φ) := by
    simpa [Φ] using isClosed_range_comp ψ₀ heψ₀
  exact contDiff_of_comp_linearIsometry_omega Φ heΦ hh

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    let F : (F₁ →L[ℝ] F₁') → (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁'))) (𝓘(ℝ, ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space

end Smooth

end Comp
