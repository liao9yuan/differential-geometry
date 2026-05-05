import DifferentialGeometry.Synthetic.Realization.Basic
import DifferentialGeometry.Synthetic.Realization.Trace
import DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Realization: MetricDuality from RiemannianMetric

Given a `Bundle.ContMDiffRiemannianMetric` on the tangent bundle, we construct
the Synthetic layer's `MetricDuality` fields:

* `concreteGTensor` : the metric as a (0,2)-tensor
* `concreteGTensor_symm` : symmetry
* `concreteGTensor_nondegenerate` : nondegeneracy (eq_of_forall_g_eq)
* `concreteGTensor_sharp_spec` : every C^∞(M)-linear functional is in the image of flat

Nondegeneracy follows from positive-definiteness of `g.inner x` at each fiber:
if `g(X, Z) = g(Y, Z)` for all smooth sections Z, then at each point x,
`g.inner x (X x - Y x) w = 0` for all fiber vectors w (via `exists_eq_at`),
and positive-definiteness forces `X x = Y x`.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle SyntheticTensor

section MetricRealization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))

private abbrev V_ := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_ := C^∞⟮I, M; ℝ⟯

/-! ### The pointwise inner product of two sections -/

private theorem gFun_smooth
    (X Y : V_ I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => g.inner x (X x) (Y x)) := by
  intro x₀
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, g.inner x⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) :=
    g.contMDiff.of_le le_top
  have hgX : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, g.inner x (X x)⟩ :
        TotalSpace (E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] ℝ))) x₀ :=
    ContMDiffAt.clm_bundle_apply hg.contMDiffAt X.contMDiff.contMDiffAt
  have hgXY : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => (⟨x, g.inner x (X x) (Y x)⟩ :
        TotalSpace ℝ (fun _ : M => ℝ))) x₀ :=
    ContMDiffAt.clm_bundle_apply hgX Y.contMDiff.contMDiffAt
  simp only [contMDiffAt_totalSpace] at hgXY
  exact hgXY.2

private def gSmooth (X Y : V_ I M) : R_ I M :=
  ⟨fun x => g.inner x (X x) (Y x), gFun_smooth I M g X Y⟩

/-! ### C^∞(M)-bilinearity -/

private theorem gSmooth_add_left (X₁ X₂ Y : V_ I M) :
    gSmooth I M g (X₁ + X₂) Y = gSmooth I M g X₁ Y + gSmooth I M g X₂ Y := by
  apply ContMDiffMap.ext; intro x
  change g.inner x ((X₁ + X₂) x) (Y x) = g.inner x (X₁ x) (Y x) + g.inner x (X₂ x) (Y x)
  simp only [ContMDiffSection.coe_add, Pi.add_apply, map_add, ContinuousLinearMap.add_apply]

private theorem gSmooth_smul_left (f : R_ I M) (X Y : V_ I M) :
    gSmooth I M g (f • X) Y = f * gSmooth I M g X Y := by
  apply ContMDiffMap.ext; intro x
  change g.inner x ((f • X) x) (Y x) = f x * g.inner x (X x) (Y x)
  simp only [ContMDiffSection.coe_smulContMDiffMap, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem gSmooth_add_right (X Y₁ Y₂ : V_ I M) :
    gSmooth I M g X (Y₁ + Y₂) = gSmooth I M g X Y₁ + gSmooth I M g X Y₂ := by
  apply ContMDiffMap.ext; intro x
  change g.inner x (X x) ((Y₁ + Y₂) x) = g.inner x (X x) (Y₁ x) + g.inner x (X x) (Y₂ x)
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  exact (g.inner x (X x)).map_add (Y₁ x) (Y₂ x)

private theorem gSmooth_smul_right (f : R_ I M) (X Y : V_ I M) :
    gSmooth I M g X (f • Y) = f * gSmooth I M g X Y := by
  apply ContMDiffMap.ext; intro x
  change g.inner x (X x) ((f • Y) x) = f x * g.inner x (X x) (Y x)
  simp only [ContMDiffSection.coe_smulContMDiffMap]
  exact (g.inner x (X x)).map_smul (f x) (Y x)

private theorem gSmooth_symm (X Y : V_ I M) :
    gSmooth I M g X Y = gSmooth I M g Y X := by
  apply ContMDiffMap.ext; intro x
  exact g.symm x (X x) (Y x)

/-! ### Packaging as TensorData -/

noncomputable def concreteGTensor : TensorData (R_ I M) (V_ I M) 0 2 where
  toFun vs :=
    MultilinearMap.constOfIsEmpty (R_ I M) (fun _ : Fin 0 => (V_ I M) →ₗ[R_ I M] R_ I M)
      (gSmooth I M g (vs 0) (vs 1))
  map_update_add' m i x y := by
    suffices h : gSmooth I M g (Function.update m i (x + y) 0)
          (Function.update m i (x + y) 1) =
        gSmooth I M g (Function.update m i x 0) (Function.update m i x 1) +
        gSmooth I M g (Function.update m i y 0) (Function.update m i y 1) by
      ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.add_apply]; exact h ▸ rfl
    rcases i with ⟨i, hi⟩
    interval_cases i
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact gSmooth_add_left I M g x y (m 1)
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact gSmooth_add_right I M g (m 0) x y
  map_update_smul' m i c x := by
    suffices h : gSmooth I M g (Function.update m i (c • x) 0)
          (Function.update m i (c • x) 1) =
        c * gSmooth I M g (Function.update m i x 0) (Function.update m i x 1) by
      ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply,
        smul_eq_mul]; exact h ▸ rfl
    rcases i with ⟨i, hi⟩
    interval_cases i
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact gSmooth_smul_left I M g c x (m 1)
    · simp only [Function.update, dite_eq_ite]; norm_num
      exact gSmooth_smul_right I M g c (m 0) x

theorem concreteGTensor_eval (X Y : V_ I M) :
    concreteGTensor I M g ![X, Y] ![] = gSmooth I M g X Y := by
  simp [concreteGTensor]

theorem concreteGTensor_eval_pt (X Y : V_ I M) (x : M) :
    (concreteGTensor I M g ![X, Y] ![]) x = g.inner x (X x) (Y x) := by
  simp [concreteGTensor_eval, gSmooth]

/-! ### Symmetry -/

theorem concreteGTensor_symm :
    swap_covariant 0 1 (concreteGTensor I M g) = concreteGTensor I M g := by
  apply MultilinearMap.ext; intro vs
  change (concreteGTensor I M g).domDomCongr (Equiv.swap (0 : Fin 2) 1) vs =
    concreteGTensor I M g vs
  simp only [MultilinearMap.domDomCongr_apply, concreteGTensor, MultilinearMap.coe_mk]
  congr 1
  exact gSmooth_symm I M g (vs 1) (vs 0)

/-! ### Nondegeneracy -/

/-- Nondegeneracy: if `g(X, Z) = g(Y, Z)` for all smooth sections Z, then X = Y.
Uses positive-definiteness and `exists_eq_at`. -/
theorem concreteGTensor_nondegenerate :
    ∀ X Y : V_ I M,
      (∀ Z : V_ I M, concreteGTensor I M g ![X, Z] ![] = concreteGTensor I M g ![Y, Z] ![]) →
      X = Y := by
  intro X Y hZ
  ext x
  have h_fiberwise : ∀ w : TangentSpace I x, g.inner x (X x) w = g.inner x (Y x) w := by
    intro w
    obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
    have h := DFunLike.congr_fun (hZ σ) x
    simp only [concreteGTensor_eval_pt] at h
    rwa [hσ] at h
  have h_diff : ∀ w : TangentSpace I x, g.inner x (X x - Y x) w = 0 := by
    intro w
    have : g.inner x (X x - Y x) = g.inner x (X x) - g.inner x (Y x) := map_sub _ _ _
    rw [this, ContinuousLinearMap.sub_apply, h_fiberwise w, sub_self]
  by_contra h_ne
  have h_ne' : X x - Y x ≠ 0 := fun h => h_ne (sub_eq_zero.mp h ▸ rfl)
  exact absurd (h_diff (X x - Y x)) (ne_of_gt (g.pos x (X x - Y x) h_ne'))

/-! ### Fiber-level metric properties -/

/-- The flat map `g.inner x` is injective at each fiber. -/
private theorem metric_flat_injective (x : M) :
    Function.Injective (g.inner x : TangentSpace I x → TangentSpace I x →L[ℝ] ℝ) := by
  intro v w hvw
  by_contra h_ne
  have h_diff : v - w ≠ 0 := sub_ne_zero.mpr h_ne
  have h_eq : g.inner x v = g.inner x w := hvw
  have : g.inner x (v - w) (v - w) = 0 := by
    have hsub : g.inner x (v - w) = g.inner x v - g.inner x w := map_sub _ _ _
    rw [hsub, h_eq, sub_self, ContinuousLinearMap.zero_apply]
  exact absurd this (ne_of_gt (g.pos x (v - w) h_diff))

/-- The flat map `g.inner x` is surjective at each fiber (injective between
equal finite-dimensional spaces implies surjective). -/
private theorem metric_flat_surjective (x : M) :
    Function.Surjective (g.inner x : TangentSpace I x → TangentSpace I x →L[ℝ] ℝ) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x →L[ℝ] ℝ) := inferInstance
  have h_dim : Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := TangentSpace I x) (F' := ℝ))]
    exact (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim).mp
    (metric_flat_injective I M g x)

/-! ### Sharp spec: every C^∞(M)-linear functional is in the image of flat -/

/-- Fiberwise functional from a C^∞(M)-linear map. -/
private noncomputable def α_fiberDef
    (α : V_ I M →ₗ[R_ I M] R_ I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] ℝ where
  toFun w :=
    (α (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose) x
  map_add' w₁ w₂ := by
    have h₁ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₁).choose_spec
    have h₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₂).choose_spec
    have h₁₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (w₁ + w₂)).choose_spec
    set σ₁ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₁).choose
    set σ₂ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w₂).choose
    rw [smoothLinearMap_acts_pointwise I M α _ (σ₁ + σ₂) x (by
      rw [h₁₂, ContMDiffSection.coe_add, Pi.add_apply, h₁, h₂]),
      map_add]; rfl
  map_smul' c w := by
    have hσ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose_spec
    set σ := (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w).choose
    let c' : C^∞⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
    rw [smoothLinearMap_acts_pointwise I M α _ (c' • σ) x (by
      rw [(ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (c • w)).choose_spec]
      show c • w = (c' • σ) x
      simp only [ContMDiffSection.coe_smulContMDiffMap, c']; congr 1; exact hσ.symm),
      α.map_smul]; simp only [smul_eq_mul, RingHom.id_apply, c']; rfl

private theorem α_fiberDef_spec
    (α : V_ I M →ₗ[R_ I M] R_ I M)
    (σ : V_ I M) (x : M) :
    α_fiberDef I M α x (σ x) = (α σ) x :=
  smoothLinearMap_acts_pointwise I M α _ σ x
    (ContMDiffSection.exists_eq_at x (σ x)).choose_spec

/-- Fiberwise sharp: invert the flat map at each fiber. -/
private noncomputable def sharp_fiberDef (x : M)
    (φ : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metric_flat_surjective I M g x (LinearMap.toContinuousLinearMap φ)).choose

private theorem sharp_fiberDef_spec (x : M)
    (φ : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (sharp_fiberDef I M g x φ) w = φ w := by
  have h := (metric_flat_surjective I M g x
    (LinearMap.toContinuousLinearMap φ)).choose_spec
  have : (g.inner x (sharp_fiberDef I M g x φ)) w =
      (LinearMap.toContinuousLinearMap φ) w :=
    congr_fun (congr_arg DFunLike.coe h) w
  simpa using this

/-- Sharp spec: every C^∞(M)-linear functional is realized by a smooth section via g. -/
theorem concreteGTensor_sharp_spec :
    ∀ α : V_ I M →ₗ[R_ I M] R_ I M,
      ∃ v : V_ I M, ∀ Z : V_ I M,
        concreteGTensor I M g ![v, Z] ![] = α Z := by
  intro α
  let sf := fun x => sharp_fiberDef I M g x (α_fiberDef I M α x)
  have pointwise_spec : ∀ (Z : V_ I M) (x : M),
      g.inner x (sf x) (Z x) = (α Z) x := by
    intro Z x
    rw [sharp_fiberDef_spec I M g x (α_fiberDef I M α x) (Z x)]
    exact α_fiberDef_spec I M α Z x
  -- Smoothness: the sharp section is smooth because in each local trivialization
  -- it equals the solution of a smooth invertible linear system.
  -- The Gram matrix G_{ij}(x) = g.inner x (σ'ᵢ x)(σ'ⱼ x) is smooth and invertible.
  -- By contDiffAt_map_inverse, the inverse is smooth, giving smooth coordinates.
  have sharp_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, sf x⟩ : TotalSpace E (TangentSpace I : M → Type _))) := by
    intro x₀
    rw [contMDiffAt_section x₀]
    let e := trivializationAt E (TangentSpace I : M → Type _) x₀
    have he : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E _ x₀
    let b := Module.finBasis ℝ E
    let hframe := e.isLocalFrameOn_localFrame_baseSet I (↑(⊤ : ℕ∞)) b
    obtain ⟨σ', hσ'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
    -- Build the Gram CLM: F(x) : E →L[ℝ] E with
    --   F(x)(v) = Σᵢ (Σⱼ G_{ij}(x) · (b.repr v j)) · bᵢ
    -- where G_{ij}(x) = g.inner x (σ'ᵢ x) (σ'ⱼ x).
    let bCLE := b.equivFun.toContinuousLinearEquiv
    let elem : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E →L[ℝ] E :=
      fun i j => ((ContinuousLinearMap.proj j).comp bCLE.toContinuousLinearMap).smulRight (b i)
    let G_fun : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → M → ℝ :=
      fun i j x => g.inner x ((σ' i) x) ((σ' j) x)
    let F_map : M → E →L[ℝ] E := fun x => ∑ i, ∑ j, (G_fun i j x) • elem i j
    let d_vec : M → E := fun x => ∑ j, ((α (σ' j)) x) • b j
    have hF_smooth : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ F_map := by
      apply ContMDiff.sum; intro i _; apply ContMDiff.sum; intro j _
      exact (gFun_smooth I M g (σ' i) (σ' j)).smul contMDiff_const
    have hd_vec_smooth : ContMDiff I 𝓘(ℝ, E) ∞ d_vec := by
      apply ContMDiff.sum; intro j _
      exact (α (σ' j)).contMDiff.smul contMDiff_const
    -- Helper: σ'ⱼ(x) = le.symm(bⱼ) when σ' agrees with local frame at x
    have frame_eq_le_symm : ∀ (x : M) (hx : x ∈ e.baseSet)
        (hσ'x : ∀ i, (σ' i) x = e.localFrame b i x) (j : Fin (Module.finrank ℝ E)),
        (σ' j) x = (e.linearEquivAt ℝ x hx).symm (b j) := by
      intro x hx hσ'x j
      rw [hσ'x j]
      simp [Trivialization.localFrame, Trivialization.basisAt, hx]
    -- F(x) is injective when σ' agrees with local frame at x
    have hF_inj_at : ∀ (x : M) (hx : x ∈ e.baseSet)
        (hσ'x : ∀ i, (σ' i) x = e.localFrame b i x),
        Function.Injective (F_map x) := by
      intro x hx hσ'x v₁ v₂ hv
      suffices h : v₁ - v₂ = 0 from sub_eq_zero.mp h
      set v := v₁ - v₂
      have hFv : F_map x v = 0 := by rw [map_sub, sub_eq_zero]; exact hv
      let le := e.linearEquivAt ℝ x hx
      set w := le.symm v
      -- w = Σⱼ (b.repr v)(j) • σ'ⱼ(x)
      have hw_expand : w = ∑ j, (b.repr v) j • (σ' j) x := by
        change le.symm v = _
        conv_lhs => rw [show v = ∑ j, (b.repr v) j • b j from (b.sum_repr v).symm]
        simp only [map_sum, LinearEquiv.map_smul]
        congr 1; ext j; congr 1
        exact (frame_eq_le_symm x hx hσ'x j).symm
      -- g.inner x w (σ'ᵢ x) = 0 from positive definiteness argument
      -- (skip computing via F_map, directly show g.inner x w vanishes on frame)
      have hw_flat_on_frame : ∀ i, g.inner x w ((σ' i) x) = 0 := by
        intro i
        rw [hw_expand]
        -- g.inner x (Σⱼ cⱼ • σ'ⱼ x)(σ'ᵢ x) = Σⱼ cⱼ • g.inner x (σ'ⱼ x)(σ'ᵢ x)
        rw [map_sum, ContinuousLinearMap.sum_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        -- This equals Σⱼ G_fun j i x * (b.repr v)(j)
        -- = Σⱼ G_fun i j x * (b.repr v)(j)  (by symmetry of g)
        -- We need to show this equals 0, i.e., the i-th coordinate of F(x)(v) = 0.
        -- Use symmetry of g to rewrite G_fun j i = G_fun i j
        -- Use symmetry: g.inner x (σ'ⱼ x)(σ'ᵢ x) = G_fun i j x
        simp_rw [show ∀ j, g.inner x ((σ' j) x) ((σ' i) x) = G_fun i j x from
          fun j => (g.symm x ((σ' i) x) ((σ' j) x)).symm]
        simp_rw [mul_comm ((b.repr v) _) (G_fun i _ x)]
        -- Need the coordinate formula: Σⱼ G_fun i j x * (b.repr v)(j) = (b.repr (F_map x v))(i)
        -- Then since F_map x v = 0, this is 0.
        -- Prove the coordinate formula
        suffices hcoord_formula : ∀ (y : M) (u : E) (k : Fin (Module.finrank ℝ E)),
            (b.repr (F_map y u)) k = ∑ j, G_fun k j y * (b.repr u) j by
          rw [← hcoord_formula x v i, hFv]; simp
        intro y u k
        -- F_map y u = Σ k', Σ j, G_fun k' j y • elem k' j u
        -- elem k' j u = (bCLE u)(j) • b k' = (b.repr u)(j) • b k'
        -- So F_map y u = Σ k', (Σ j, G_fun k' j y * (b.repr u)(j)) • b k'
        -- Hence (b.repr (F_map y u))(k) = Σ j, G_fun k j y * (b.repr u)(j)
        -- F_map y u = Σ i', Σ j, G_fun i' j y • elem i' j u
        -- elem i' j u = (bCLE u)(j) • b i' = (b.repr u)(j) • b i'
        -- So F_map y u = Σ i', (Σ j, G_fun i' j y * (b.repr u)(j)) • b i'
        -- and (b.repr (F_map y u))(k) = Σ j, G_fun k j y * (b.repr u)(j)
        -- because b is a basis.
        -- First, show F_map y u = Σ i', (Σ j, G_fun i' j y * (b.repr u) j) • b i'
        -- F_map y u = Σ i', (Σ j, G_fun i' j y * (b.repr u) j) • b i'
        -- Compute directly: (b.repr (F_map y u)) k
        -- F_map y u = Σ i', Σ j, G_fun i' j y • (bCLE u)(j) • b i'
        -- Take b.repr and evaluate at k:
        change (b.repr (F_map y u)) k = _
        simp only [F_map, map_sum, LinearEquiv.map_smul, ContinuousLinearMap.coe_sum',
          Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, elem,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp',
          Function.comp_apply, ContinuousLinearMap.proj_apply]
        -- Now have Finsupp sum at k
        simp only [smul_eq_mul, Finsupp.finset_sum_apply, Finsupp.smul_apply,
          b.repr_self, Finsupp.single_apply,
]
        simp only [ContinuousLinearEquiv.coe_apply, show ∀ (u : E) (j : Fin (Module.finrank ℝ E)),
            bCLE u j = (b.repr u) j from fun _ _ => rfl]
        -- Each inner sum: Σ i', G_fun i' j y * ((b.repr u) j * if i' = k then 1 else 0)
        -- = G_fun k j y * (b.repr u) j
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      -- g.inner x w = 0
      have hw_flat : g.inner x w = 0 := by
        ext u
        rw [ContinuousLinearMap.zero_apply]
        let hba := hframe.toBasisAt hx
        rw [show u = ∑ i, hba.repr u i • hba i from (hba.sum_repr u).symm, map_sum]
        apply Finset.sum_eq_zero; intro i _
        rw [map_smul, smul_eq_mul]
        rw [show (hba i : TangentSpace I x) = (σ' i) x from by
          rw [IsLocalFrameOn.toBasisAt_coe]; exact (hσ'x i).symm]
        rw [hw_flat_on_frame i, mul_zero]
      have hw_zero : w = 0 := by
        by_contra h_ne
        exact absurd (show g.inner x w w = 0 from by rw [hw_flat, ContinuousLinearMap.zero_apply])
          (ne_of_gt (g.pos x w h_ne))
      calc v = le (le.symm v) := (le.apply_symm_apply v).symm
        _ = le w := rfl
        _ = le 0 := by rw [hw_zero]
        _ = 0 := map_zero _
    -- F(x₀) is invertible
    have hF_invertible : (F_map x₀).IsInvertible := by
      have hinj := hF_inj_at x₀ he (fun i => Filter.Eventually.self_of_nhds hσ' i)
      exact ⟨ContinuousLinearEquiv.ofBijective (F_map x₀)
        (LinearMap.ker_eq_bot.mpr hinj)
        (LinearMap.range_eq_top.mpr
          ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj)),
        rfl⟩
    -- inverse ∘ F is smooth near x₀
    have hF_inv_smooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun x => ContinuousLinearMap.inverse (F_map x)) x₀ :=
      hF_invertible.contDiffAt_map_inverse.contMDiffAt.comp _ hF_smooth.contMDiffAt
    -- Near x₀, (e ⟨x, sf x⟩).2 = F(x)⁻¹(d_vec(x))
    have hsf_eq : ∀ᶠ x in nhds x₀,
        (e ⟨x, sf x⟩).2 = ContinuousLinearMap.inverse (F_map x) (d_vec x) := by
      filter_upwards [hσ', e.open_baseSet.mem_nhds he] with x hσ'x hx
      set le := e.linearEquivAt ℝ x hx
      have hF_invertible_x : (F_map x).IsInvertible := by
        have hinj := hF_inj_at x hx hσ'x
        exact ⟨ContinuousLinearEquiv.ofBijective (F_map x)
          (LinearMap.ker_eq_bot.mpr hinj)
          (LinearMap.range_eq_top.mpr
            ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj)),
          rfl⟩
      suffices hFsf : F_map x (le (sf x)) = d_vec x by
        rw [← hFsf, hF_invertible_x.inverse_apply_self]; simp [le]
      -- F(x)(le(sf x)) = d_vec(x)
      -- sf x = le.symm(le(sf x)) = Σⱼ (b.repr(le(sf x)))(j) • σ'ⱼ(x)
      have hsf_expand : sf x = ∑ j, (b.repr (le (sf x))) j • (σ' j) x := by
        conv_lhs => rw [show sf x = le.symm (le (sf x)) from (le.symm_apply_apply _).symm]
        conv_lhs =>
          rw [show le (sf x) = ∑ j, (b.repr (le (sf x))) j • b j from (b.sum_repr _).symm]
        simp only [map_sum, LinearEquiv.map_smul]
        congr 1; ext j; congr 1
        exact (frame_eq_le_symm x hx hσ'x j).symm
      -- Show F(x)(le(sf x)) = d_vec(x) by comparing b.repr coordinates.
      -- Use the coordinate formula from hF_inj_at's proof.
      have hcoord_formula : ∀ (y : M) (u : E) (k : Fin (Module.finrank ℝ E)),
          (b.repr (F_map y u)) k = ∑ j, G_fun k j y * (b.repr u) j := by
        intro y u k
        change (b.repr (F_map y u)) k = _
        simp only [F_map, map_sum, LinearEquiv.map_smul, ContinuousLinearMap.coe_sum',
          Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, elem,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp',
          Function.comp_apply, ContinuousLinearMap.proj_apply]
        simp only [smul_eq_mul, Finsupp.finset_sum_apply, Finsupp.smul_apply,
          b.repr_self, Finsupp.single_apply]
        simp only [ContinuousLinearEquiv.coe_apply, show ∀ (u : E) (j : Fin (Module.finrank ℝ E)),
            bCLE u j = (b.repr u) j from fun _ _ => rfl]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      apply b.equivFun.injective
      ext i
      simp only [b.equivFun_apply]
      rw [hcoord_formula]
      -- RHS: (b.equivFun (d_vec x))(i) = (α (σ' i))(x)
      -- d_vec x = Σⱼ (α σ'ⱼ)(x) • b j, so b.equivFun(d_vec x)(i) = (α σ'ᵢ)(x)
      have hd_coord : (b.repr (d_vec x)) i = (α (σ' i)) x := by
        simp only [d_vec, map_sum, LinearEquiv.map_smul, Finsupp.finset_sum_apply,
          Finsupp.smul_apply, smul_eq_mul, b.repr_self, Finsupp.single_apply]
        simp [Finset.sum_ite_eq']
      rw [hd_coord]
      -- LHS: Σⱼ G_fun i j x * (b.repr (le (sf x)))(j)
      --     = Σⱼ g.inner x (σ'ᵢ x)(σ'ⱼ x) * cⱼ
      --     = g.inner x (σ'ᵢ x)(Σⱼ cⱼ • σ'ⱼ x)  [bilinearity of 2nd arg]
      --     = g.inner x (σ'ᵢ x)(sf x)             [by hsf_expand]
      --     = g.inner x (sf x)(σ'ᵢ x)             [by symmetry]
      --     = (α σ'ᵢ)(x)                           [by pointwise_spec]
      -- LHS = Σⱼ G_fun i j x * cⱼ = g.inner x (sf x)(σ'ᵢ x) = (α σ'ᵢ)(x) = RHS
      -- Expand LHS using hsf_expand and bilinearity
      have hlhs : ∑ j, G_fun i j x * (b.repr (le (sf x))) j =
          g.inner x (sf x) ((σ' i) x) := by
        -- RHS = g.inner x (Σⱼ cⱼ • σ'ⱼ x)(σ'ᵢ x) by hsf_expand
        -- = Σⱼ cⱼ * g.inner x (σ'ⱼ x)(σ'ᵢ x) by bilinearity
        -- = Σⱼ cⱼ * G_fun i j x by symmetry
        -- = LHS after commuting
        conv_rhs => rw [hsf_expand]
        rw [map_sum]; simp only [map_smul]
        -- Now RHS is (∑ j, cⱼ • g.inner x (σ'ⱼ x)) (σ'ᵢ x)
        rw [ContinuousLinearMap.sum_apply]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        simp_rw [show ∀ j, g.inner x ((σ' j) x) ((σ' i) x) = G_fun i j x from
          fun j => (g.symm x ((σ' i) x) ((σ' j) x)).symm]
        congr 1; ext j; ring
      rw [hlhs]
      exact pointwise_spec (σ' i) x
    exact (ContMDiffAt.congr_of_eventuallyEq
      (hF_inv_smooth.clm_apply hd_vec_smooth.contMDiffAt) hsf_eq).contMDiffWithinAt
  let v : V_ I M := ⟨sf, sharp_smooth⟩
  exact ⟨v, fun Z => by
    apply ContMDiffMap.ext; intro x
    rw [concreteGTensor_eval_pt]
    exact pointwise_spec Z x⟩

/-! ### Sharp section and its linearity -/

/-- Extract the sharp image of a covector from `concreteGTensor_sharp_spec`. -/
private noncomputable def sharp_section
    (α : V_ I M →ₗ[R_ I M] R_ I M) : V_ I M :=
  (concreteGTensor_sharp_spec I M g α).choose

private theorem sharp_section_spec
    (α : V_ I M →ₗ[R_ I M] R_ I M) (Z : V_ I M) :
    concreteGTensor I M g ![sharp_section I M g α, Z] ![] = α Z :=
  (concreteGTensor_sharp_spec I M g α).choose_spec Z

private theorem sharp_section_g
    (α : V_ I M →ₗ[R_ I M] R_ I M) (Z : V_ I M) :
    gSmooth I M g (sharp_section I M g α) Z = α Z := by
  rw [← concreteGTensor_eval]; exact sharp_section_spec I M g α Z

/-- sharp_section is additive. -/
private theorem sharp_section_add
    (α β : V_ I M →ₗ[R_ I M] R_ I M) :
    sharp_section I M g (α + β) = sharp_section I M g α + sharp_section I M g β := by
  apply concreteGTensor_nondegenerate I M g
  intro Z
  rw [sharp_section_spec, concreteGTensor_eval, gSmooth_add_left,
      ← concreteGTensor_eval, ← concreteGTensor_eval,
      sharp_section_spec, sharp_section_spec]
  simp [LinearMap.add_apply]

/-- sharp_section is R-homogeneous. -/
private theorem sharp_section_smul
    (f : R_ I M) (α : V_ I M →ₗ[R_ I M] R_ I M) :
    sharp_section I M g (f • α) = f • sharp_section I M g α := by
  apply concreteGTensor_nondegenerate I M g
  intro Z
  rw [sharp_section_spec, concreteGTensor_eval, gSmooth_smul_left,
      ← concreteGTensor_eval, sharp_section_spec,
      LinearMap.smul_apply, smul_eq_mul]

/-! ### g_inv: the inverse metric tensor -/

/-- The inverse metric `g⁻¹(α, β) = g(♯α, ♯β)`. -/
noncomputable def concreteGInv : TensorData (R_ I M) (V_ I M) 2 0 :=
  MultilinearMap.constOfIsEmpty (R_ I M) (fun _ : Fin 0 => V_ I M)
    { toFun := fun αs =>
        gSmooth I M g (sharp_section I M g (αs 0)) (sharp_section I M g (αs 1))
      map_update_add' := fun m i x y => by
        rcases i with ⟨i, hi⟩
        interval_cases i
        · simp only [Function.update, dite_eq_ite]; norm_num
          rw [sharp_section_add, gSmooth_add_left]
        · simp only [Function.update, dite_eq_ite]; norm_num
          rw [sharp_section_add, gSmooth_add_right]
      map_update_smul' := fun m i c x => by
        rcases i with ⟨i, hi⟩
        interval_cases i
        · simp only [Function.update, dite_eq_ite]; norm_num
          rw [sharp_section_smul, gSmooth_smul_left]
        · simp only [Function.update, dite_eq_ite]; norm_num
          rw [sharp_section_smul, gSmooth_smul_right] }

theorem concreteGInv_eval (α β : V_ I M →ₗ[R_ I M] R_ I M) :
    concreteGInv I M g ![] ![α, β] =
      gSmooth I M g (sharp_section I M g α) (sharp_section I M g β) := by
  simp [concreteGInv]

/-! ### inverse_eval: g⁻¹(α, flat(Y)) = α(Y) -/

/-- sharp(flat(Y)) = Y: the sharp section of the flat covector of Y is Y itself. -/
private theorem sharp_section_flat
    (Y : V_ I M) :
    sharp_section I M g (flat_covector (concreteGTensor I M g) Y) = Y := by
  apply concreteGTensor_nondegenerate I M g
  intro Z
  rw [sharp_section_spec]
  simp [flat_covector_apply]

theorem concreteGInv_inverse_eval
    (Y : V_ I M) (α : V_ I M →ₗ[R_ I M] R_ I M) :
    concreteGInv I M g ![] ![α, flat_covector (concreteGTensor I M g) Y] = α Y := by
  rw [concreteGInv_eval, sharp_section_flat, sharp_section_g]

end MetricRealization

/-! ### Finite-dimensional real inner-product realization -/

section RealInnerProductMetric

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The real inner product, packaged as a synthetic `(0,2)` tensor. -/
noncomputable def realInnerProductGTensor : TensorData ℝ E 0 2 where
  toFun vs :=
    MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E →ₗ[ℝ] ℝ)
      (inner ℝ (vs 0) (vs 1))
  map_update_add' m i x y := by
    fin_cases i
    · ext αs
      simp [Function.update, inner_add_left]
    · ext αs
      simp [Function.update, inner_add_right]
  map_update_smul' m i c x := by
    fin_cases i
    · ext αs
      simp [Function.update, real_inner_smul_left]
    · ext αs
      simp [Function.update, real_inner_smul_right]

@[simp] theorem realInnerProductGTensor_eval (X Y : E) :
    realInnerProductGTensor (E := E) ![X, Y] ![] = inner ℝ X Y := by
  simp [realInnerProductGTensor]

/-- The sharp vector representing a real linear functional by the Riesz map. -/
noncomputable def realInnerProductSharp (α : E →ₗ[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap α)

@[simp] theorem realInnerProductSharp_spec (α : E →ₗ[ℝ] ℝ) (X : E) :
    inner ℝ (realInnerProductSharp (E := E) α) X = α X := by
  simp [realInnerProductSharp,
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
      (x := X) (y := LinearMap.toContinuousLinearMap α))]

private theorem realInnerProductSharp_add (α β : E →ₗ[ℝ] ℝ) :
    realInnerProductSharp (E := E) (α + β) =
      realInnerProductSharp (E := E) α + realInnerProductSharp (E := E) β := by
  apply (InnerProductSpace.toDual ℝ E).injective
  ext Z
  simp

private theorem realInnerProductSharp_smul (c : ℝ) (α : E →ₗ[ℝ] ℝ) :
    realInnerProductSharp (E := E) (c • α) =
      c • realInnerProductSharp (E := E) α := by
  apply (InnerProductSpace.toDual ℝ E).injective
  ext Z
  simp

/-- The inverse metric induced by the real inner product. -/
noncomputable def realInnerProductGInv : TensorData ℝ E 2 0 :=
  MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
    { toFun := fun αs =>
        inner ℝ (realInnerProductSharp (E := E) (αs 0))
          (realInnerProductSharp (E := E) (αs 1))
      map_update_add' := fun m i x y => by
        fin_cases i
        · simp [Function.update, realInnerProductSharp_add, inner_add_left]
        · simp [Function.update, realInnerProductSharp_add, inner_add_right]
      map_update_smul' := fun m i c x => by
        fin_cases i
        · simp [Function.update, realInnerProductSharp_smul, real_inner_smul_left]
        · simp [Function.update, realInnerProductSharp_smul, real_inner_smul_right] }

@[simp] theorem realInnerProductGInv_eval (α β : E →ₗ[ℝ] ℝ) :
    realInnerProductGInv (E := E) ![] ![α, β] =
      inner ℝ (realInnerProductSharp (E := E) α) (realInnerProductSharp (E := E) β) := by
  simp [realInnerProductGInv]

/-- The `MetricDuality` carried by a finite-dimensional real inner-product space. -/
noncomputable def realInnerProductMetricDuality : MetricDuality ℝ E where
  g_tensor := realInnerProductGTensor (E := E)
  symm_tensor := by
    ext vs αs
    change inner ℝ (vs 1) (vs 0) = inner ℝ (vs 0) (vs 1)
    exact real_inner_comm (vs 0) (vs 1)
  g_inv := realInnerProductGInv (E := E)
  eq_of_forall_g_eq := by
    intro X Y h
    apply (InnerProductSpace.toDual ℝ E).injective
    ext Z
    simpa using h Z
  inverse_eval := by
    intro Y α
    rw [realInnerProductGInv_eval]
    have hsharp_flat :
        realInnerProductSharp (E := E)
          (flat_covector (realInnerProductGTensor (E := E)) Y) = Y := by
      apply (InnerProductSpace.toDual ℝ E).injective
      ext Z
      simp [flat_covector_apply]
    rw [hsharp_flat]
    exact realInnerProductSharp_spec (E := E) α Y
  sharp_spec := by
    intro α
    refine ⟨realInnerProductSharp (E := E) α, ?_⟩
    intro Z
    exact realInnerProductSharp_spec (E := E) α Z

/-- The standard real inner-product realization has `met.g = inner ℝ`. -/
@[simp] theorem realInnerProductMetricDuality_g_eq_inner (X Y : E) :
    (realInnerProductMetricDuality (E := E)).g X Y = inner ℝ X Y := by
  simp [MetricDuality.g, realInnerProductMetricDuality]

end RealInnerProductMetric

end
