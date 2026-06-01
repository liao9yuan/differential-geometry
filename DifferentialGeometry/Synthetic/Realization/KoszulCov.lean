import DifferentialGeometry.Synthetic.Realization.KoszulGerm
import DifferentialGeometry.Synthetic.Realization.SmoothExtension
import DifferentialGeometry.Synthetic.Realization.SmoothExtensionMDiff
import DifferentialGeometry.Synthetic.Realization.SmoothSections

/-!
# KoszulCov: Fiberwise covariant-derivative CLM of the concrete Koszul connection

Phase B, substep B.3/C of the Realization programme.

## Summary

Given a smooth tangent-section `Y : Γ(TM)`, the Koszul connection provides a
smooth bundle hom `X ↦ ∇_X Y` on `Γ(TM)` which is `C^∞(M)`-linear in `X`. By
the VBC lemma `ContMDiffVectorBundleHom.ofLinearMapSection`, this corresponds to
a smooth bundle endomorphism `Φ_Y : TM → TM` covering the identity. The fiber
value of `Φ_Y` at a point `x : M` is a linear map `TangentSpace I x →ₗ[ℝ]
TangentSpace I x`, which becomes a continuous linear map via finite-
dimensionality (`LinearMap.toContinuousLinearMap`).

For a raw section `σ : Π x : M, TangentSpace I x` whose total-space form is
`MDifferentiableAt` at `x`, we use the 1-jet extension from Step A
(`smoothExtensionAt_MDiff`) to obtain a globally smooth section `σ'` matching
`σ`'s value and trivialisation-read `mfderiv` at `x`. The 1-jet-dependence
theorem from Step B (`koszul_connection_1jet_dep`) then guarantees that the
resulting fiber CLM depends only on the 1-jet of `σ` at `x`.

## Main declarations

* `koszulFiberLinMap I M g Y` — the `C^∞(M,ℝ)`-linear map `Γ(TM) → Γ(TM)`
  given by `X ↦ ∇_X Y`, for a fixed smooth `Y`.
* `koszulFiberBundleHom I M g Y` — the corresponding smooth bundle hom
  `TM → TM` obtained via VBC.
* `koszulFiberCLM I M g Y x` — the fiber CLM
  `TangentSpace I x →L[ℝ] TangentSpace I x` extracted from
  `koszulFiberBundleHom`.
* `koszulFiberCLM_apply_section` — the evaluation formula:
  `koszulFiberCLM Y x (X x) = concreteKoszulConnection X Y x`.
* `koszulFiberCLM_germ_invariant` — germ-invariance of
  `koszulFiberCLM` in `Y`.
* `koszulFiberCLM_1jet_invariant` — 1-jet-invariance of `koszulFiberCLM` in
  `Y`.
* `concreteKoszulCovFun I M g σ x` — for a raw section `σ`, either uses
  `smoothExtensionAt_MDiff` on the `MDifferentiableAt` hypothesis or returns
  `0`.
* `concreteKoszulCovFun_of_smooth_section` — for any globally smooth section
  `Y`, `concreteKoszulCovFun g (⇑Y) x = koszulFiberCLM g Y x`.
* `concreteKoszulCov_isCovariantDerivativeOn` — the full Mathlib
  `IsCovariantDerivativeOn` structure is realised by `concreteKoszulCovFun` on
  `Set.univ`.
* `concreteKoszulCov` — the bundled Mathlib `CovariantDerivative` built from
  `concreteKoszulCovFun`.
* `concreteKoszulCov_contMDiff` — the `ContMDiffCovariantDerivative` instance
  at level `∞` for `concreteKoszulCov`, showing the concrete Koszul covariant
  derivative is smooth.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle Filter ContinuousLinearMap CovariantDerivative

namespace KoszulCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private abbrev V_k := Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
private abbrev R_k := C^∞⟮I, M; ℝ⟯

/-! ### The `C^∞(M,ℝ)`-linear map `X ↦ ∇_X Y` for fixed smooth `Y` -/

/-- For a fixed smooth tangent-section `Y`, the map `X ↦ ∇_X Y` from
`Γ(TM)` to itself is `C^∞(M,ℝ)`-linear. This is the key VBC input. -/
noncomputable def koszulFiberLinMap
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) : V_k I M →ₗ[R_k I M] V_k I M where
  toFun X := concreteKoszulConnection I M g X Y
  map_add' X₁ X₂ := concreteKoszul_add_left I M g X₁ X₂ Y
  map_smul' f X := concreteKoszul_smul_left I M g f X Y

@[simp]
theorem koszulFiberLinMap_apply
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y X : V_k I M) :
    koszulFiberLinMap I M g Y X = concreteKoszulConnection I M g X Y := rfl

/-! ### The bundle hom `Φ_Y : TM → TM` from the VBC lemma -/

/-- The smooth bundle endomorphism of `TM` obtained by applying the VBC lemma
`ContMDiffVectorBundleHom.ofLinearMapSection` to `koszulFiberLinMap g Y`. -/
noncomputable def koszulFiberBundleHom
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) :
    ContMDiffVectorBundleHom ℝ I (⊤ : ℕ∞) E (TangentSpace I : M → Type _)
      E (TangentSpace I : M → Type _) := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  exact ContMDiffVectorBundleHom.ofLinearMapSection
    (I := I) (n := (⊤ : ℕ∞)) (koszulFiberLinMap I M g Y)

/-! ### The fiberwise CLM -/

/-- The fiberwise continuous linear map
`TangentSpace I x →L[ℝ] TangentSpace I x` at `x` obtained from the bundle hom
`koszulFiberBundleHom`. Uses `LinearMap.toContinuousLinearMap` to upgrade the
fiberwise linear map to a CLM (valid because each fiber is finite-dimensional). -/
noncomputable def koszulFiberCLM
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    ((koszulFiberBundleHom I M g Y).fiberLinearMap x)

@[simp]
theorem koszulFiberCLM_apply_linearMap
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) (x : M) (v : TangentSpace I x) :
    koszulFiberCLM I M g Y x v = (koszulFiberBundleHom I M g Y).fiberLinearMap x v := rfl

/-- **Evaluation formula for `koszulFiberCLM`.** Evaluating the fiber CLM on
the value at `x` of a smooth section `X` equals the value of the Koszul
connection at `x`. This is the section-level specification of the VBC output. -/
theorem koszulFiberCLM_apply_section
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y X : V_k I M) (x : M) :
    koszulFiberCLM I M g Y x (X x) = concreteKoszulConnection I M g X Y x := by
  haveI : Fact (1 ≤ (⊤ : ℕ∞)) := ⟨le_top⟩
  change (koszulFiberBundleHom I M g Y).fiberLinearMap x (X x) =
      concreteKoszulConnection I M g X Y x
  -- Apply `linearMap_acts_pointwise`: the fiber map from VBC agrees with the
  -- section-level map after evaluating a chosen smooth section at `x`.
  have h := ContMDiffVectorBundleHom.linearMap_acts_pointwise
    (I := I) (n := (⊤ : ℕ∞)) (koszulFiberLinMap I M g Y)
    (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (X x)).choose
    X x
    (ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (X x)).choose_spec
  -- `koszulFiberBundleHom = ofLinearMapSection (koszulFiberLinMap ...)`;
  -- `fiberLinearMap x (X x)` unfolds to `F (choose (X x)) x` by construction.
  -- `linearMap_acts_pointwise` gives `F (choose (X x)) x = F X x`, and the
  -- latter is `koszulFiberLinMap Y X x = concreteKoszulConnection X Y x`.
  exact h

/-! ### Germ-invariance of `koszulFiberCLM` in `Y` -/

/-- **Germ-invariance of `koszulFiberCLM` in the section argument `Y`.** If two
smooth sections `Y`, `Y'` have the same germ at `x` (as raw `Π x, TangentSpace I x`
functions), then the fiber CLMs at `x` agree. This propagates B.1's
germ-dependence of the concrete Koszul connection from the section-level to
the fiber-CLM level. -/
theorem koszulFiberCLM_germ_invariant
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y Y' : V_k I M) (x : M)
    (h : (⇑Y : Π x : M, TangentSpace I x) =ᶠ[𝓝 x] (⇑Y')) :
    koszulFiberCLM I M g Y x = koszulFiberCLM I M g Y' x := by
  refine ContinuousLinearMap.ext fun v => ?_
  -- Pick any smooth section X_v with X_v x = v via exists_eq_at.
  obtain ⟨X_v, hXv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  -- Reduce the CLM equality at `v` to the section equality at `X_v`.
  rw [show v = X_v x from hXv.symm]
  rw [koszulFiberCLM_apply_section, koszulFiberCLM_apply_section]
  -- Now we need to show `concreteKoszulConnection X_v Y x = concreteKoszulConnection X_v Y' x`,
  -- which follows from B.1's germ-dependence.
  exact KoszulGerm.koszul_connection_germ_dep I M g X_v Y Y' x h

/-! ### 1-jet-invariance of `koszulFiberCLM` in `Y`

This is the main new ingredient for Step C. We upgrade germ-invariance to the
stronger property of 1-jet invariance: the fiber CLM depends only on the
value and the trivialisation-read `mfderiv` at the base point. -/

/-- **1-jet-invariance of `koszulFiberCLM` in the section argument `Y`.** If two
smooth sections `Y`, `Y'` have the same value and matching trivialisation-read
`mfderiv`s at `x`, then the fiber CLMs at `x` agree. This propagates Step B's
1-jet-dependence of the concrete Koszul connection from the section-level to
the fiber-CLM level. -/
theorem koszulFiberCLM_1jet_invariant
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y Y' : V_k I M) (x : M)
    (hval : Y x = Y' x)
    (hmf : mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x
        ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x
      =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x
          ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) x) :
    koszulFiberCLM I M g Y x = koszulFiberCLM I M g Y' x := by
  refine ContinuousLinearMap.ext fun v => ?_
  -- Pick any smooth section X_v with X_v x = v via exists_eq_at.
  obtain ⟨X_v, hXv⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  -- Reduce the CLM equality at `v` to the section equality at `X_v`.
  rw [show v = X_v x from hXv.symm]
  rw [koszulFiberCLM_apply_section, koszulFiberCLM_apply_section]
  -- Now we need to show
  --   concreteKoszulConnection X_v Y x = concreteKoszulConnection X_v Y' x,
  -- which follows from Step B's 1-jet-dependence (`koszul_connection_1jet_dep`).
  exact KoszulGerm.koszul_connection_1jet_dep I M g X_v Y Y' x hval hmf

/-! ### The choice-invariant fiber CLM for raw sections -/

/-- For a raw tangent-section `σ : Π x, TangentSpace I x`, the fiber CLM at `x`:
* if `σ` is `MDifferentiableAt` at `x` (in total-space form), we use Step A's
  `smoothExtensionAt_MDiff` to produce a globally smooth section with matching
  1-jet at `x`, then apply `koszulFiberCLM`;
* otherwise, we return `0`.

The 1-jet-invariance theorem `koszulFiberCLM_1jet_invariant` ensures that, on
the "MDifferentiableAt" branch, the resulting fiber CLM depends only on the
1-jet of `σ` at `x`, not on the choice of smooth extension. -/
noncomputable def concreteKoszulCovFun
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (σ : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x := by
  classical
  by_cases hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x
  · exact koszulFiberCLM I M g (Realization.smoothExtensionAt_MDiff I M σ x hσ) x
  · exact 0

/-! ### General choice-invariance via 1-jet matching

These helper lemmas show that when `σ` is `MDifferentiableAt` at `x` (in
total-space form) and `Y : V_k` is any globally smooth tangent section with
matching value and triv-read mfderiv at `x`, we have
`concreteKoszulCovFun g σ x = koszulFiberCLM g Y x`. -/

/-- **1-jet choice-invariance of `concreteKoszulCovFun`.** If `σ` is
`MDifferentiableAt` at `x` in total-space form and `Y : V_k` is a globally
smooth tangent section with matching value and trivialisation-read `mfderiv` at
`x`, then `concreteKoszulCovFun g σ x = koszulFiberCLM g Y x`. -/
theorem concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (σ : Π x : M, TangentSpace I x) (x : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x)
    (Y : V_k I M)
    (hY_val : (Y : Π x, TangentSpace I x) x = σ x)
    (hY_mf : mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x
        ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x
      =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x ⟨y, σ y⟩).2) x) :
    concreteKoszulCovFun I M g σ x = koszulFiberCLM I M g Y x := by
  classical
  -- Expand the definition along the `true` branch.
  unfold concreteKoszulCovFun
  rw [dif_pos hσ]
  -- On the true branch, the definition yields
  --   koszulFiberCLM g (smoothExtensionAt_MDiff σ x hσ) x.
  -- We need to show this equals `koszulFiberCLM g Y x`.
  -- Both `smoothExtensionAt_MDiff σ x hσ` and `Y` have matching 1-jets with `σ`
  -- at `x`, so by transitivity their 1-jets match. Apply 1-jet invariance.
  refine koszulFiberCLM_1jet_invariant I M g
    (Realization.smoothExtensionAt_MDiff I M σ x hσ) Y x ?_ ?_
  · -- Value match: smoothExt = σ x (Step A) and Y x = σ x (hypothesis).
    rw [Realization.smoothExtensionAt_MDiff_value, hY_val]
  · -- Triv-read-mfderiv match: smoothExt triv-read-mfderiv = σ triv-read-mfderiv (Step A),
    -- and Y triv-read-mfderiv = σ triv-read-mfderiv (hypothesis).
    rw [Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv, hY_mf]

/-! ### Choice-invariance on smooth sections -/

/-- **Choice-invariance theorem.** For any globally smooth tangent-section `Y`
and any point `x`, the raw-section fiber CLM `concreteKoszulCovFun` applied to
`⇑Y` equals the fiber CLM `koszulFiberCLM` applied to `Y` itself.

Proof: on a globally smooth section `Y`, the `MDifferentiableAt` hypothesis
holds; by 1-jet invariance, the smooth extension returned by Step A has the
same fiber-CLM value as `Y`. -/
theorem concreteKoszulCovFun_of_smooth_section
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) (x : M) :
    concreteKoszulCovFun I M g (⇑Y) x = koszulFiberCLM I M g Y x := by
  classical
  -- Y is MDifferentiableAt (in total-space form) at every point.
  have hY_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (Y : Π x, TangentSpace I x) y⟩ : TotalSpace E (TangentSpace I))) x :=
    (Y.contMDiff x).mdifferentiableAt (by simp)
  -- Apply the choice-invariance lemma with Y itself as the smooth witness.
  refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g (⇑Y) x hY_mdiff Y ?_ ?_
  · rfl
  · rfl

/-! ### Additivity of `koszulFiberCLM` in the section argument -/

/-- **Additivity of `koszulFiberCLM` in the section argument.** For globally
smooth sections `Y, Y'` and a point `x`, the fiber CLMs satisfy
`koszulFiberCLM g (Y + Y') x = koszulFiberCLM g Y x + koszulFiberCLM g Y' x`. -/
theorem koszulFiberCLM_add
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y Y' : V_k I M) (x : M) :
    koszulFiberCLM I M g (Y + Y') x =
      koszulFiberCLM I M g Y x + koszulFiberCLM I M g Y' x := by
  refine ContinuousLinearMap.ext fun v => ?_
  -- Test on any smooth `X` with `X x = v`.
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  -- Reduce to section-level evaluation by pushing `v = X x`.
  rw [show v = X x from hX.symm]
  -- Apply `koszulFiberCLM_apply_section` to each term.
  rw [koszulFiberCLM_apply_section]
  rw [ContinuousLinearMap.add_apply]
  rw [koszulFiberCLM_apply_section, koszulFiberCLM_apply_section]
  -- Now use right-additivity of `concreteKoszulConnection`.
  have := concreteKoszul_add_right I M g X Y Y'
  -- The equality is between smooth sections; evaluate at `x`.
  exact congrArg (fun s : V_k I M => s x) this

/-- **Scalar-Leibniz of `koszulFiberCLM` in the section argument.** For a
smooth scalar `f`, smooth section `Y`, and point `x`, the fiber CLM satisfies
`koszulFiberCLM g (f • Y) x v =
  f x • koszulFiberCLM g Y x v + (extDerivFun f x v) • Y x` for all
`v : TangentSpace I x`. -/
theorem koszulFiberCLM_smul_apply
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (f : R_k I M) (Y : V_k I M) (x : M) (v : TangentSpace I x) :
    koszulFiberCLM I M g (f • Y) x v =
      f x • koszulFiberCLM I M g Y x v + (extDerivFun (I := I) f x v) • Y x := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  rw [show v = X x from hX.symm]
  rw [koszulFiberCLM_apply_section]
  -- Koszul Leibniz: concreteKoszulConnection X (f • Y) = (embed X f) • Y + f • concreteKoszulConnection X Y
  have hleib := concreteKoszul_leibniz I M g X f Y
  -- Evaluate at x (the equation in V_k becomes an equation of tangent vectors).
  have hpt : concreteKoszulConnection I M g X (f • Y) x =
      ((concreteDerivationEmbedding I M).embed X f • Y +
        f • concreteKoszulConnection I M g X Y : V_k I M) x := by
    rw [hleib]
  rw [hpt]
  -- Unfold the smul / add on ContMDiffSection to get pointwise.
  change ((concreteDerivationEmbedding I M).embed X f : M → ℝ) x • Y x +
      f x • concreteKoszulConnection I M g X Y x =
      f x • koszulFiberCLM I M g Y x (X x) + extDerivFun (I := I) f x (X x) • Y x
  -- `embed X f x = extDerivFun f x (X x)`.
  have h_embed_eval :
      ((concreteDerivationEmbedding I M).embed X f : M → ℝ) x =
        extDerivFun (I := I) f x (X x) := by
    change vectorFieldAction I M X f x = extDerivFun (I := I) f x (X x)
    rfl
  rw [h_embed_eval]
  rw [koszulFiberCLM_apply_section]
  abel

/-! ### Scalar 1-jet extension — analogue of Step A for scalar-valued functions

Given `g : M → ℝ` that is `MDifferentiableAt` at `x₀`, we construct a globally
smooth `ĝ : C^∞⟮I, M; ℝ⟯` with `ĝ x₀ = g x₀` and matching `mfderiv` at `x₀`.

The construction mirrors Step A but with scalar target `ℝ` instead of `E`: we
build an affine function in chart coordinates and multiply by a smooth bump
supported in the chart source. -/

/-- Existence of a globally smooth scalar extension with matching 1-jet at `x₀`.

The hypothesis `MDifferentiableAt g x₀` isn't strictly needed to build the
extension (if `g` is non-differentiable, `mfderiv g x₀ = 0` and the construction
still produces a valid extension with that zero 1-jet). We keep the hypothesis
for API consistency with the downstream Leibniz proof. -/
private theorem exists_smooth_scalar_matching_1jet
    (g : M → ℝ) (x₀ : M)
    (_hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x₀) :
    ∃ (ĝ : C^∞⟮I, M; ℝ⟯),
      (⇑ĝ : M → ℝ) x₀ = g x₀ ∧
      mfderiv I 𝓘(ℝ, ℝ) (⇑ĝ : M → ℝ) x₀ = mfderiv I 𝓘(ℝ, ℝ) g x₀ := by
  -- Abbreviations mirror Step A but with scalar target ℝ.
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I : M → Type _) x₀ with he_def
  set phi : M → E := ⇑(extChartAt I x₀) with hphi_def
  set L₀ : TangentSpace I x₀ →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) g x₀ with hL₀_def
  have hx₀_base : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source _ _
  -- The fixed CLM T : E →L[ℝ] ℝ := L₀ ∘L e.symmL ℝ x₀.
  set T : E →L[ℝ] ℝ := L₀ ∘L (e.symmL ℝ x₀) with hT_def
  -- Smooth scalar function ĝ_pre : M → ℝ := T ∘ phi + (g x₀ - T (phi x₀)).
  let ĝ_pre : M → ℝ := fun y => T (phi y) + (g x₀ - T (phi x₀))
  -- (A) ĝ_pre is ContMDiffOn on chart source.
  have hpre_smoothOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ĝ_pre (chartAt H x₀).source := by
    intro y hy
    have hphi_at : ContMDiffAt I 𝓘(ℝ, E) ∞ phi y :=
      (contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)) y hy |>.contMDiffAt
        ((chartAt H x₀).open_source.mem_nhds hy)
    have hT_phi : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z => T (phi z)) y :=
      T.contMDiff.contMDiffAt.comp y hphi_at
    exact (hT_phi.add contMDiffAt_const).contMDiffWithinAt
  -- (B) Smooth bump function at x₀ with tsupport ⊆ (chartAt H x₀).source.
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp
      ((chartAt H x₀).open_source.mem_nhds hx₀_src)
  -- (C) Globally smooth scalar extension: ĝ := χ • ĝ_pre.
  have hχ_globally : ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) :=
    χ.contMDiff.of_le (by exact_mod_cast le_top)
  -- Build ĝ y := (χ y : ℝ) • ĝ_pre y (globally smooth because of tsupport χ ⊆ chart source).
  have hĝ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => (χ y : ℝ) • ĝ_pre y) := by
    intro y
    by_cases hy : y ∈ tsupport (χ : M → ℝ)
    · have hy_u : y ∈ (chartAt H x₀).source := hχ hy
      have hpre_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ĝ_pre y :=
        (hpre_smoothOn y hy_u).contMDiffAt
          ((chartAt H x₀).open_source.mem_nhds hy_u)
      exact hχ_globally.contMDiffAt.smul hpre_at
    · have hχ_zero : ∀ᶠ z in 𝓝 y, (χ : M → ℝ) z = 0 :=
        Filter.Eventually.mono
          ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hy)
          fun z hz => (notMem_tsupport_iff_eventuallyEq.mp hz).self_of_nhds
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (hχ_zero.mono fun z hz => by simp [hz])
  refine ⟨⟨fun y => (χ y : ℝ) • ĝ_pre y, hĝ_smooth⟩, ?_, ?_⟩
  · -- Value at x₀: ĝ x₀ = χ x₀ • ĝ_pre x₀ = 1 • g x₀ = g x₀.
    change (χ x₀ : ℝ) • ĝ_pre x₀ = g x₀
    have hχ1 : (χ : M → ℝ) x₀ = 1 := χ.eq_one
    rw [hχ1, one_smul]
    change T (phi x₀) + (g x₀ - T (phi x₀)) = g x₀
    abel
  · -- mfderiv match.
    -- On a neighborhood of x₀ (inside chart source ∩ {χ = 1}), ĝ = ĝ_pre.
    -- Hence mfderiv ĝ x₀ = mfderiv ĝ_pre x₀ = T ∘L mfderiv phi x₀ = L₀.
    set ĝ : M → ℝ := fun y => (χ y : ℝ) • ĝ_pre y with hĝ_def
    change mfderiv I 𝓘(ℝ, ℝ) ĝ x₀ = L₀
    -- Step 1: ĝ =ᶠ[𝓝 x₀] ĝ_pre.
    have hee : ĝ =ᶠ[𝓝 x₀] ĝ_pre := by
      filter_upwards [χ.eventuallyEq_one] with y hy
      change (χ y : ℝ) • ĝ_pre y = ĝ_pre y
      rw [show (χ y : ℝ) = (1 : ℝ) from hy, one_smul]
    have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) ĝ x₀ = mfderiv I 𝓘(ℝ, ℝ) ĝ_pre x₀ :=
      Filter.EventuallyEq.mfderiv_eq hee
    -- Step 2: mfderiv ĝ_pre x₀ = T ∘L mfderiv phi x₀.
    have hphi_mdiffAt : MDifferentiableAt I 𝓘(ℝ, E) phi x₀ :=
      mdifferentiableAt_extChartAt hx₀_src
    have hTphi_mdiffAt : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => T (phi z)) x₀ :=
      T.mdifferentiableAt.comp x₀ hphi_mdiffAt
    have hconst_mdiffAt : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => g x₀ - T (phi x₀)) x₀ :=
      mdifferentiableAt_const
    have hpre_mfderiv :
        mfderiv I 𝓘(ℝ, ℝ) ĝ_pre x₀ = T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ := by
      have hĝ_pre_eq : ĝ_pre = (fun z => T (phi z)) + (fun _ : M => g x₀ - T (phi x₀)) := rfl
      rw [hĝ_pre_eq, mfderiv_add hTphi_mdiffAt hconst_mdiffAt]
      have hTphi_mfderiv :
          mfderiv I 𝓘(ℝ, ℝ) (fun z => T (phi z)) x₀ = T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ := by
        rw [show (fun z => T (phi z)) = T ∘ phi from rfl,
            mfderiv_comp x₀ T.mdifferentiableAt hphi_mdiffAt, T.mfderiv_eq]
        rfl
      rw [hTphi_mfderiv]
      have hconst_mfderiv :
          mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => g x₀ - T (phi x₀)) x₀ = 0 := mfderiv_const
      rw [hconst_mfderiv]
      exact add_zero _
    -- Step 3: T ∘L mfderiv phi x₀ = L₀ (using e.symmL ∘ e.continuousLinearMapAt = id).
    have hphi_mfderiv :
        mfderiv I 𝓘(ℝ, E) phi x₀ = e.continuousLinearMapAt ℝ x₀ := by
      have := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (𝕜 := ℝ)
        (x₀ := x₀) (x := x₀) hx₀_src
      exact this.symm
    have hT_comp :
        T ∘L mfderiv I 𝓘(ℝ, E) phi x₀ = L₀ := by
      rw [hphi_mfderiv]
      change (L₀ ∘L e.symmL ℝ x₀) ∘L e.continuousLinearMapAt ℝ x₀ = L₀
      ext v
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      exact congrArg L₀ (e.symmL_continuousLinearMapAt (R := ℝ) hx₀_base v)
    rw [h_mfderiv_eq, hpre_mfderiv, hT_comp]

/-- Given a scalar `g : M → ℝ` that is `MDifferentiableAt` at `x₀`, produce a
globally smooth `C^∞⟮I, M; ℝ⟯` extension with matching 1-jet at `x₀`. -/
private noncomputable def smoothScalarExtensionAt
    (g : M → ℝ) (x₀ : M) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x₀) :
    C^∞⟮I, M; ℝ⟯ :=
  (exists_smooth_scalar_matching_1jet I M g x₀ hg).choose

private theorem smoothScalarExtensionAt_value
    (g : M → ℝ) (x₀ : M) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x₀) :
    (smoothScalarExtensionAt I M g x₀ hg : M → ℝ) x₀ = g x₀ :=
  (exists_smooth_scalar_matching_1jet I M g x₀ hg).choose_spec.1

private theorem smoothScalarExtensionAt_mfderiv
    (g : M → ℝ) (x₀ : M) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x₀) :
    mfderiv I 𝓘(ℝ, ℝ) (smoothScalarExtensionAt I M g x₀ hg : M → ℝ) x₀
      = mfderiv I 𝓘(ℝ, ℝ) g x₀ :=
  (exists_smooth_scalar_matching_1jet I M g x₀ hg).choose_spec.2

/-! ### Full Mathlib `IsCovariantDerivativeOn` on `Set.univ`

This is the main deliverable for Step C: the `concreteKoszulCovFun` realises the
full Mathlib `IsCovariantDerivativeOn` structure on `Set.univ`, not merely the
weaker "locally smooth" variant. -/

/-- **Additivity of `concreteKoszulCovFun` for `MDifferentiableAt` sections.**
If `σ, σ'` are both `MDifferentiableAt` (in total-space form) at `x`, then
`concreteKoszulCovFun g (σ + σ') x = concreteKoszulCovFun g σ x +
concreteKoszulCovFun g σ' x`.

Strategy: use Step A's `smoothExtensionAt_MDiff` on each of `σ`, `σ'` to produce
smooth `Y`, `Y'`. Then `Y + Y'` has matching 1-jet with `σ + σ'` at `x`. Apply
additivity of `koszulFiberCLM` and 1-jet choice-invariance. -/
theorem concreteKoszulCovFun_add_MDifferentiableAt
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    {σ σ' : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ' y⟩ : TotalSpace E (TangentSpace I))) x) :
    concreteKoszulCovFun I M g (σ + σ') x =
      concreteKoszulCovFun I M g σ x + concreteKoszulCovFun I M g σ' x := by
  classical
  -- Smooth extensions Y, Y' of σ, σ'.
  set Y := Realization.smoothExtensionAt_MDiff I M σ x hσ with hY_def
  set Y' := Realization.smoothExtensionAt_MDiff I M σ' x hσ' with hY'_def
  have hY_val := Realization.smoothExtensionAt_MDiff_value I M σ x hσ
  have hY'_val := Realization.smoothExtensionAt_MDiff_value I M σ' x hσ'
  have hY_mf := Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv I M σ x hσ
  have hY'_mf := Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv I M σ' x hσ'
  -- The sum `σ + σ'` is MDifferentiableAt at x.
  have hσ_sum : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (σ + σ') y⟩ : TotalSpace E (TangentSpace I))) x :=
    mdifferentiableAt_add_section hσ hσ'
  -- Rewrite each `concreteKoszulCovFun` using the generalised choice-invariance lemma.
  -- For `σ`: use `Y` as smooth witness.
  have h_rw_σ : concreteKoszulCovFun I M g σ x = koszulFiberCLM I M g Y x := by
    refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g σ x hσ Y ?_ ?_
    · exact hY_val
    · exact hY_mf
  -- For `σ'`: use `Y'` as smooth witness.
  have h_rw_σ' : concreteKoszulCovFun I M g σ' x = koszulFiberCLM I M g Y' x := by
    refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g σ' x hσ' Y' ?_ ?_
    · exact hY'_val
    · exact hY'_mf
  -- For `σ + σ'`: use `Y + Y'` as smooth witness. Need matching value and triv-read-mfderiv.
  have h_rw_sum : concreteKoszulCovFun I M g (σ + σ') x =
      koszulFiberCLM I M g (Y + Y') x := by
    refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g (σ + σ') x hσ_sum
      (Y + Y') ?_ ?_
    · -- Value: (Y + Y') x = Y x + Y' x = σ x + σ' x = (σ + σ') x.
      change Y x + Y' x = σ x + σ' x
      rw [hY_val, hY'_val]
    · -- Triv-read-mfderiv: additivity of trivialization, then mfderiv_add.
      -- Actually, the cleanest way: use that (Y + Y') y = Y y + Y' y and
      -- (σ + σ') y = σ y + σ' y, and trivialisation-read is linear in fiber.
      -- Key: on a neighborhood of x, (fun y => (e ⟨y, (Y+Y') y⟩).2)
      --                          = (fun y => (e ⟨y, Y y⟩).2 + (e ⟨y, Y' y⟩).2)
      -- and similarly for σ + σ'. Combined with additivity of mfderiv_add and the
      -- triv-read-mfderiv matches for each summand.
      set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
        trivializationAt E (TangentSpace I : M → Type _) x with he_def
      -- The triv-read of a sum equals the sum of triv-reads on baseSet.
      have hYY'_ev :
          (fun y => (e ⟨y, ((Y + Y' : V_k I M) : Π x, TangentSpace I x) y⟩).2)
            =ᶠ[𝓝 x]
          (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2 +
                    (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) := by
        filter_upwards [e.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)] with y hy_base
        -- On baseSet, `(e ⟨y, v⟩).2 = e.continuousLinearMapAt ℝ y v`, which is linear.
        have h_cw : ∀ v : TangentSpace I y, (e ⟨y, v⟩).2 = e.continuousLinearMapAt ℝ y v := by
          intro v
          rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy_base,
              e.coe_continuousLinearEquivAt_eq (R := ℝ) hy_base]
        change (e ⟨y, ((Y + Y' : V_k I M) : Π x, TangentSpace I x) y⟩).2 =
            (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2 +
            (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2
        have h_sum_ev : ((Y + Y' : V_k I M) : Π x, TangentSpace I x) y = Y y + Y' y := rfl
        rw [h_sum_ev, h_cw (Y y + Y' y), h_cw (Y y), h_cw (Y' y), map_add]
      have hσσ'_ev :
          (fun y => (e ⟨y, ((σ + σ') : Π x, TangentSpace I x) y⟩).2)
            =ᶠ[𝓝 x]
          (fun y => (e ⟨y, σ y⟩).2 + (e ⟨y, σ' y⟩).2) := by
        filter_upwards [e.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)] with y hy_base
        have h_cw : ∀ v : TangentSpace I y, (e ⟨y, v⟩).2 = e.continuousLinearMapAt ℝ y v := by
          intro v
          rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy_base,
              e.coe_continuousLinearEquivAt_eq (R := ℝ) hy_base]
        change (e ⟨y, ((σ + σ') : Π x, TangentSpace I x) y⟩).2 =
            (e ⟨y, σ y⟩).2 + (e ⟨y, σ' y⟩).2
        have h_sum_ev : ((σ + σ') : Π x, TangentSpace I x) y = σ y + σ' y := rfl
        rw [h_sum_ev, h_cw (σ y + σ' y), h_cw (σ y), h_cw (σ' y), map_add]
      -- The triv-reads of each summand are MDifferentiableAt at x.
      have hY_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x :=
        ((mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            (⇑Y) (b₀ := x)).mp
          ((Y.contMDiff x).mdifferentiableAt (by simp)))
      have hY'_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) x :=
        ((mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            (⇑Y') (b₀ := x)).mp
          ((Y'.contMDiff x).mdifferentiableAt (by simp)))
      have hσ_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, σ y⟩).2) x :=
        (mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            σ (b₀ := x)).mp hσ
      have hσ'_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, σ' y⟩).2) x :=
        (mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            σ' (b₀ := x)).mp hσ'
      -- Combine via `EventuallyEq.mfderiv_eq` on both sides, reducing to an
      -- equality of mfderivs of sums. Use `mfderiv_add` to split the sums, then
      -- rewrite each summand using the triv-read-mfderiv matches from Step A.
      have step1 : mfderiv I 𝓘(ℝ, E)
          (fun y => (e ⟨y, ((Y + Y' : V_k I M) : Π x, TangentSpace I x) y⟩).2) x
          = mfderiv I 𝓘(ℝ, E)
              (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2 +
                        (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) x :=
        Filter.EventuallyEq.mfderiv_eq hYY'_ev
      have step5 : mfderiv I 𝓘(ℝ, E)
          (fun y => (e ⟨y, σ y⟩).2 + (e ⟨y, σ' y⟩).2) x =
          mfderiv I 𝓘(ℝ, E)
            (fun y => (e ⟨y, ((σ + σ') : Π x, TangentSpace I x) y⟩).2) x :=
        (Filter.EventuallyEq.mfderiv_eq hσσ'_ev).symm
      -- Apply mfderiv_add. We type-annotate each summand `: TangentSpace I x →L[ℝ] E`
      -- to coerce the target tangent space of the mfderiv into `E`, after which
      -- the addition is well-typed.
      set hY_mf_E : TangentSpace I x →L[ℝ] E :=
        mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x
      set hY'_mf_E : TangentSpace I x →L[ℝ] E :=
        mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) x
      set hσ_mf_E : TangentSpace I x →L[ℝ] E :=
        mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, σ y⟩).2) x
      set hσ'_mf_E : TangentSpace I x →L[ℝ] E :=
        mfderiv I 𝓘(ℝ, E) (fun y => (e ⟨y, σ' y⟩).2) x
      have step2 : (mfderiv I 𝓘(ℝ, E)
          (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2 +
                    (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2) x
            : TangentSpace I x →L[ℝ] E) = hY_mf_E + hY'_mf_E := by
        change (mfderiv I 𝓘(ℝ, E)
            ((fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2)
              + (fun y => (e ⟨y, (Y' : Π x, TangentSpace I x) y⟩).2)) x
          : TangentSpace I x →L[ℝ] E) = _
        exact mfderiv_add hY_read_mdiff hY'_read_mdiff
      have step4 : (mfderiv I 𝓘(ℝ, E)
          (fun y => (e ⟨y, σ y⟩).2 + (e ⟨y, σ' y⟩).2) x
            : TangentSpace I x →L[ℝ] E) = hσ_mf_E + hσ'_mf_E := by
        change (mfderiv I 𝓘(ℝ, E)
            ((fun y => (e ⟨y, σ y⟩).2) + (fun y => (e ⟨y, σ' y⟩).2)) x
          : TangentSpace I x →L[ℝ] E) = _
        exact mfderiv_add hσ_read_mdiff hσ'_read_mdiff
      -- Rewrite the matches hY_mf and hY'_mf in the hY_mf_E / hY'_mf_E `set` bindings.
      have hY_mf_E_eq : hY_mf_E = hσ_mf_E := hY_mf
      have hY'_mf_E_eq : hY'_mf_E = hσ'_mf_E := hY'_mf
      rw [step1, step2, hY_mf_E_eq, hY'_mf_E_eq, ← step4, step5]
  rw [h_rw_σ, h_rw_σ', h_rw_sum]
  exact koszulFiberCLM_add I M g Y Y' x

/-- **Leibniz rule for `concreteKoszulCovFun` with `MDifferentiableAt` data.**
If `σ` is `MDifferentiableAt` at `x` (in total-space form) and `g : M → ℝ` is
`MDifferentiableAt` at `x`, then
`concreteKoszulCovFun cov (g • σ) x = g x • concreteKoszulCovFun cov σ x +
(extDerivFun g x).smulRight (σ x)`.

Strategy: use Step A's `smoothExtensionAt_MDiff` for `σ` and the scalar 1-jet
extension `smoothScalarExtensionAt` for `g` to produce smooth witnesses. Then
`ĝ • Y` has matching 1-jet with `g • σ` at `x`. Apply `koszulFiberCLM_smul_apply`
and 1-jet choice-invariance. -/
theorem concreteKoszulCovFun_leibniz_MDifferentiableAt
    (cov : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    {σ : Π x : M, TangentSpace I x} {g : M → ℝ} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    concreteKoszulCovFun I M cov (g • σ) x =
      g x • concreteKoszulCovFun I M cov σ x +
      (extDerivFun (I := I) g x).smulRight (σ x) := by
  classical
  -- Smooth 1-jet extensions.
  set Y := Realization.smoothExtensionAt_MDiff I M σ x hσ with hY_def
  set ĝ := smoothScalarExtensionAt I M g x hg with hĝ_def
  have hY_val := Realization.smoothExtensionAt_MDiff_value I M σ x hσ
  have hY_mf := Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv I M σ x hσ
  have hĝ_val : (ĝ : M → ℝ) x = g x := smoothScalarExtensionAt_value I M g x hg
  have hĝ_mf : mfderiv I 𝓘(ℝ, ℝ) (ĝ : M → ℝ) x = mfderiv I 𝓘(ℝ, ℝ) g x :=
    smoothScalarExtensionAt_mfderiv I M g x hg
  -- `g • σ` is MDifferentiableAt at x.
  have hgσ_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (g • σ) y⟩ : TotalSpace E (TangentSpace I))) x := by
    have := hg.smul_section (E := (TangentSpace I : M → Type _)) (F := E) hσ
    exact this
  -- Rewrite each `concreteKoszulCovFun` using the generalised choice-invariance lemma.
  -- For `σ`: use `Y`.
  have h_rw_σ : concreteKoszulCovFun I M cov σ x = koszulFiberCLM I M cov Y x := by
    refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M cov σ x hσ Y hY_val hY_mf
  -- For `g • σ`: use `ĝ • Y`. Need matching value and triv-read-mfderiv.
  have h_rw_gσ : concreteKoszulCovFun I M cov (g • σ) x =
      koszulFiberCLM I M cov (ĝ • Y) x := by
    refine concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M cov (g • σ) x hgσ_mdiff
      (ĝ • Y) ?_ ?_
    · -- Value: (ĝ • Y) x = ĝ x • Y x = g x • σ x = (g • σ) x.
      change (ĝ : M → ℝ) x • Y x = g x • σ x
      rw [hĝ_val, hY_val]
    · -- Triv-read-mfderiv: need to match `mfderiv (triv-read of ĝ • Y)` and
      -- `mfderiv (triv-read of g • σ)` at `x`.
      -- Use the eventuallyEq of triv-reads under smul by scalars, plus
      -- `mfderiv_smul`.
      -- On a neighborhood of `x`: (e ⟨y, (ĝ • Y) y⟩).2 = ĝ y • (e ⟨y, Y y⟩).2
      -- (since e.continuousLinearMapAt is ℝ-linear).
      set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
        trivializationAt E (TangentSpace I : M → Type _) x with he_def
      have hĝY_ev :
          (fun y => (e ⟨y, ((ĝ • Y : V_k I M) : Π x, TangentSpace I x) y⟩).2)
            =ᶠ[𝓝 x]
          (fun y => (ĝ : M → ℝ) y • (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) := by
        filter_upwards [e.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)] with y hy_base
        have h_cw : ∀ v : TangentSpace I y, (e ⟨y, v⟩).2 = e.continuousLinearMapAt ℝ y v := by
          intro v
          rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy_base,
              e.coe_continuousLinearEquivAt_eq (R := ℝ) hy_base]
        change (e ⟨y, ((ĝ • Y : V_k I M) : Π x, TangentSpace I x) y⟩).2 =
            (ĝ : M → ℝ) y • (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2
        have h_smul_ev : ((ĝ • Y : V_k I M) : Π x, TangentSpace I x) y
            = (ĝ : M → ℝ) y • (Y : Π x, TangentSpace I x) y := rfl
        rw [h_smul_ev, h_cw ((ĝ : M → ℝ) y • (Y : Π x, TangentSpace I x) y),
            h_cw ((Y : Π x, TangentSpace I x) y), map_smul]
      have hgσ_ev :
          (fun y => (e ⟨y, ((g • σ) : Π x, TangentSpace I x) y⟩).2)
            =ᶠ[𝓝 x]
          (fun y => g y • (e ⟨y, σ y⟩).2) := by
        filter_upwards [e.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)] with y hy_base
        have h_cw : ∀ v : TangentSpace I y, (e ⟨y, v⟩).2 = e.continuousLinearMapAt ℝ y v := by
          intro v
          rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy_base,
              e.coe_continuousLinearEquivAt_eq (R := ℝ) hy_base]
        change (e ⟨y, ((g • σ) : Π x, TangentSpace I x) y⟩).2 = g y • (e ⟨y, σ y⟩).2
        have h_smul_ev : ((g • σ) : Π x, TangentSpace I x) y = g y • σ y := rfl
        rw [h_smul_ev, h_cw (g y • σ y), h_cw (σ y), map_smul]
      -- Differentiability of triv-reads.
      have hY_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x :=
        ((mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            (⇑Y) (b₀ := x)).mp
          ((Y.contMDiff x).mdifferentiableAt (by simp)))
      have hσ_read_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
          (fun y => (e ⟨y, σ y⟩).2) x :=
        (mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
            σ (b₀ := x)).mp hσ
      have hĝ_as_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ) (ĝ : M → ℝ) x :=
        (ĝ.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
      -- Show the mfderivs agree.
      -- The triv-read of (ĝ • Y) at x₀ = x: mfderiv = mfderiv of (ĝ • (triv-read Y)) at x
      --                                = via fromTangentSpace_mfderiv_smul' (for ℝ-vector-valued maps).
      --
      -- Similarly for (g • σ). The key observation: for scalar × E-valued in the tangent space,
      -- the mfderiv at x₀ is an E-valued CLM. We match both via the product rule.
      -- Since ĝ x = g x and Y x = σ x, and mfderivs of ĝ and Y match those of g and σ at x,
      -- the products' mfderivs also match.
      --
      -- Reduce to an mfderiv equality of the ℝ • E form. Use `mfderiv_smul` on
      -- both sides with the 1-jet data to match term-by-term.
      have step_left :
          mfderiv I 𝓘(ℝ, E)
            (fun y => (e ⟨y, ((ĝ • Y : V_k I M) : Π x, TangentSpace I x) y⟩).2) x
          = mfderiv I 𝓘(ℝ, E)
              (fun y => (ĝ : M → ℝ) y • (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x :=
        Filter.EventuallyEq.mfderiv_eq hĝY_ev
      have step_right :
          mfderiv I 𝓘(ℝ, E) (fun y => g y • (e ⟨y, σ y⟩).2) x
          = mfderiv I 𝓘(ℝ, E)
              (fun y => (e ⟨y, ((g • σ) : Π x, TangentSpace I x) y⟩).2) x :=
        (Filter.EventuallyEq.mfderiv_eq hgσ_ev).symm
      -- The core equality: the two smul-mfderivs agree via 1-jet matching.
      have step_core :
          mfderiv I 𝓘(ℝ, E)
            (fun y => (ĝ : M → ℝ) y • (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) x
          = mfderiv I 𝓘(ℝ, E) (fun y => g y • (e ⟨y, σ y⟩).2) x := by
        -- Rewrite each `fun y => ... y • ... y` as a `Pi.smul`-form `f • s` to
        -- match `mfderiv_smul`'s pattern.
        have h_lhs : (fun y => (ĝ : M → ℝ) y • (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2)
          = (ĝ : M → ℝ) • (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2) := rfl
        have h_rhs : (fun y => g y • (e ⟨y, σ y⟩).2)
          = g • (fun y => (e ⟨y, σ y⟩).2) := rfl
        rw [h_lhs, h_rhs, mfderiv_smul hĝ_as_scalar hY_read_mdiff,
            mfderiv_smul hg hσ_read_mdiff]
        -- After the mfderiv_smul rewrites, both sides have the form
        -- `h x • comp (fromTangentSpace ...) ∘L mfderiv (triv-read ...) x
        --   + (toSpanSingleton ((fromTangentSpace ...).symm (...))).comp
        --       (fromTangentSpace (h x) ∘L mfderiv h x)`.
        -- Using hĝ_val, hY_val, hĝ_mf, hY_mf we rewrite every occurrence of
        -- ĝ x → g x, (Y x) → σ x, mfderiv ĝ x → mfderiv g x, and the triv-read-mfderiv.
        -- The key is that `fromTangentSpace ((ĝ • f) x)` doesn't directly rewrite via
        -- `rw [hĝ_val]` because `(ĝ • f) x = ĝ x • f x` requires unfolding `Pi.smul_apply`.
        -- Use `Pi.smul_apply` to normalise and then rewrite.
        conv_lhs => rw [show ((ĝ : M → ℝ) • (fun y => (e ⟨y, (Y : Π x, TangentSpace I x) y⟩).2)) x
                      = (ĝ : M → ℝ) x • (e ⟨x, (Y : Π x, TangentSpace I x) x⟩).2 from rfl]
        conv_rhs => rw [show (g • (fun y => (e ⟨y, σ y⟩).2)) x = g x • (e ⟨x, σ x⟩).2 from rfl]
        rw [hY_val, hĝ_val, hĝ_mf, hY_mf]
      rw [step_left, step_core, step_right]
  rw [h_rw_gσ, h_rw_σ]
  -- Now goal: koszulFiberCLM cov (ĝ • Y) x = g x • koszulFiberCLM cov Y x
  --                                        + (extDerivFun g x).smulRight (σ x).
  refine ContinuousLinearMap.ext fun v => ?_
  -- Use koszulFiberCLM_smul_apply to expand the LHS.
  rw [koszulFiberCLM_smul_apply]
  -- RHS: g x • koszulFiberCLM cov Y x v + (extDerivFun g x).smulRight (σ x) v
  --    = g x • koszulFiberCLM cov Y x v + (extDerivFun g x v) • σ x.
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  -- `ĝ x = g x`, `extDerivFun ĝ x v = extDerivFun g x v`, `Y x = σ x`.
  have hĝ_x : (ĝ : M → ℝ) x = g x := hĝ_val
  have hY_x : (Y : Π x, TangentSpace I x) x = σ x := hY_val
  -- `extDerivFun ĝ x = extDerivFun g x` (at the point `x`).
  have h_extDeriv : extDerivFun (I := I) (ĝ : M → ℝ) x = extDerivFun (I := I) g x := by
    simp only [extDerivFun]
    rw [hĝ_mf, hĝ_x]
  -- Substitute.
  rw [h_extDeriv, hĝ_x, hY_x]

/-- **The full Mathlib `IsCovariantDerivativeOn` on `Set.univ`.** The function
`concreteKoszulCovFun g` realises Mathlib's bundled covariant-derivative axioms
(additivity and Leibniz rule for `MDifferentiableAt` sections) on the whole
manifold. -/
theorem concreteKoszulCov_isCovariantDerivativeOn
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (concreteKoszulCovFun I M g) Set.univ where
  add hσ hσ' _ := concreteKoszulCovFun_add_MDifferentiableAt I M g hσ hσ'
  leibniz hσ hg _ := concreteKoszulCovFun_leibniz_MDifferentiableAt I M g hσ hg

/-! ### Packaging as Mathlib's bundled `CovariantDerivative`

Using the `IsCovariantDerivativeOn` property proved above, we bundle
`concreteKoszulCovFun` as Mathlib's `CovariantDerivative` structure. This is
the main interface to the rest of the Realization programme. -/

/-- **The concrete Koszul `CovariantDerivative`**. The concrete covariant
derivative on the tangent bundle built from `concreteKoszulCovFun`, packaged
as Mathlib's bundled `CovariantDerivative` object. -/
noncomputable def concreteKoszulCov
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := concreteKoszulCovFun I M g
  isCovariantDerivativeOnUniv := concreteKoszulCov_isCovariantDerivativeOn I M g

@[simp]
theorem concreteKoszulCov_toFun
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    (concreteKoszulCov I M g).toFun = concreteKoszulCovFun I M g := rfl

@[simp]
theorem concreteKoszulCov_coeFun
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    ⇑(concreteKoszulCov I M g) = concreteKoszulCovFun I M g := rfl

/-! ### Smoothness of the Koszul covariant derivative

The concrete Koszul covariant derivative is `C^∞`. This means: whenever the
input section `σ` is `C^{∞+1} = C^∞` as a section, the output section
`fun x => (concreteKoszulCovFun g σ) x` is `C^∞` as a section of the Hom
bundle `TM →L[ℝ] TM`. -/

/-- **Key smoothness lemma**: for any globally smooth tangent-section `Y`,
the bundle-hom section `fun x => ⟨x, koszulFiberCLM g Y x⟩` is `C^∞`.

Proof strategy: use `contMDiff_clm_section_of_pointwise`, which reduces
smoothness of a CLM-bundle-valued section to pointwise smoothness when
applied to each smooth vector field `X`. For each smooth `X`, by
`koszulFiberCLM_apply_section`,
`koszulFiberCLM g Y x (X x) = concreteKoszulConnection g X Y x`.
The RHS is the value at `x` of the smooth section
`concreteKoszulConnection g X Y : V_k`, whose smoothness is automatic. -/
private theorem koszulFiberCLM_section_smooth
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        x (koszulFiberCLM I M g Y x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := (TangentSpace I : M → Type _))
    (V₂ := (TangentSpace I : M → Type _))
    (φ := fun x => koszulFiberCLM I M g Y x)
  intro X
  -- For each smooth `X`, show that `fun x => ⟨x, koszulFiberCLM g Y x (X x)⟩`
  -- is a smooth section of `TangentSpace I`.
  -- By `koszulFiberCLM_apply_section`, this equals
  -- `fun x => ⟨x, concreteKoszulConnection g X Y x⟩`, which is the total-space
  -- form of the smooth `V_k`-section `concreteKoszulConnection g X Y`.
  have h_sect : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        x ((concreteKoszulConnection I M g X Y) x)) :=
    (concreteKoszulConnection I M g X Y).contMDiff
  -- Rewrite to get the form matching `contMDiff_clm_section_of_pointwise`.
  refine h_sect.congr fun x => ?_
  congr 1
  exact (koszulFiberCLM_apply_section I M g Y X x)

/-- **Smoothness of `concreteKoszulCovFun` on a smooth section**.
For any globally smooth tangent-section `Y`, the total-space map
`fun x => ⟨x, concreteKoszulCovFun g (⇑Y) x⟩` is `C^∞`. This follows from
`koszulFiberCLM_section_smooth` via the pointwise equality
`concreteKoszulCovFun g (⇑Y) x = koszulFiberCLM g Y x`. -/
private theorem concreteKoszulCovFun_section_smooth_of_smooth_section
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (Y : V_k I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        x (concreteKoszulCovFun I M g (⇑Y) x)) := by
  have h := koszulFiberCLM_section_smooth I M g Y
  refine h.congr fun x => ?_
  congr 1
  exact (concreteKoszulCovFun_of_smooth_section I M g Y x)

/-- **The concrete Koszul covariant derivative is `C^∞`**. The
`ContMDiffCovariantDerivative` instance for `concreteKoszulCov`: whenever the
input section is `C^∞` (i.e. `CMDiff[Set.univ] (∞ + 1) (T% σ) = CMDiff[Set.univ] ∞ (T% σ)`),
the output section of the Hom bundle is `C^∞` on `Set.univ`.

Proof strategy: given `σ` smooth in total-space form, wrap it as a
`ContMDiffSection`. The pointwise equality
`concreteKoszulCovFun g (⇑Y) x = koszulFiberCLM g Y x` reduces the smoothness
of the Hom-bundle section to that of `fun x => ⟨x, koszulFiberCLM g Y x⟩`,
which we proved via the `contMDiff_clm_section_of_pointwise` bridge. -/
noncomputable instance concreteKoszulCov_contMDiff
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    ContMDiffCovariantDerivative (concreteKoszulCov I M g) ∞ where
  contMDiff := {
    contMDiff := by
      intro σ hσ
      -- `∞ + 1 = ∞`, so `σ` is genuinely `C^∞` in total-space form.
      have hσ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) x (σ x)) := by
        rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from by simp] at hσ
        rwa [← contMDiffOn_univ]
      -- Wrap `σ` as a `Cₛ^∞` section.
      let Y : V_k I M := ⟨σ, hσ_smooth⟩
      -- Convert the goal to a `ContMDiff` statement (dropping `Set.univ`).
      rw [contMDiffOn_univ]
      -- The section equals `fun x => ⟨x, concreteKoszulCovFun g (⇑Y) x⟩` since
      -- `σ = ⇑Y` by construction.
      change ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          x (concreteKoszulCovFun I M g σ x))
      -- Apply the smoothness lemma with `Y` as witness.
      exact concreteKoszulCovFun_section_smooth_of_smooth_section I M g Y
  }

/-! ### Bridge: `concreteKoszulCov` applied to smooth sections equals `concreteKoszulConnection`

For smooth tangent-sections `X, Y`, evaluating `concreteKoszulCov` at the fiber
value `X x` reproduces the concrete Koszul connection value at `x`. -/

/-- **Bridge lemma**: for smooth sections `X, Y`, the Mathlib `CovariantDerivative`
`concreteKoszulCov I M g Y x (X x)` coincides with the Synthetic
`concreteKoszulConnection I M g X Y x`. -/
theorem concreteKoszulCov_apply_section
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (X Y : V_k I M) (x : M) :
    (concreteKoszulCov I M g) Y x (X x) = concreteKoszulConnection I M g X Y x := by
  -- `(concreteKoszulCov g) Y = concreteKoszulCovFun g (⇑Y)` by coeFun.
  change (concreteKoszulCovFun I M g (⇑Y)) x (X x) =
    concreteKoszulConnection I M g X Y x
  -- For smooth `Y`, `concreteKoszulCovFun g (⇑Y) x = koszulFiberCLM g Y x`.
  rw [concreteKoszulCovFun_of_smooth_section]
  -- Apply the fiber CLM evaluation formula.
  exact koszulFiberCLM_apply_section I M g Y X x

/-! ### Metric compatibility at the Mathlib level

We now prove that the Mathlib-level metric compatibility holds for
`concreteKoszulCov I M g` with respect to the Riemannian metric `g`. The proof
combines:

1. The Synthetic-layer `koszul_metric_compat` applied to
   `concreteDerivationEmbedding` and `concreteMetricDuality`, yielding the
   Synthetic `IsMetricCompatible` for `concreteKoszulConnection`.
2. The bridge lemma `concreteKoszulCov_apply_section` translating between
   `concreteKoszulCov` and `concreteKoszulConnection`.
3. The pointwise evaluation of `concreteMetricDuality` via
   `concreteMetricDuality_g_eval`.
-/

/-- The concrete Koszul covariant derivative `concreteKoszulCov I M g` on the
tangent bundle is metric-compatible with the Riemannian metric `g`, i.e. it
satisfies the Mathlib-level predicate `IsMetricCompatibleMathlib`: for all smooth
vector fields `X Y Z` and points `x`, the directional derivative of
`y ↦ g_y(Y y, Z y)` along `X` equals `g_x(∇_X Y, Z) + g_x(Y, ∇_X Z)`. The proof
transfers the Synthetic-layer compatibility carried by `concreteKoszulConnection_isLeviCivita`
through the section bridge `concreteKoszulCov_apply_section`. -/
theorem concreteKoszulCov_isMetricCompatibleMathlib
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    IsMetricCompatibleMathlib I M (concreteKoszulCov I M g) g := by
  -- Unfold the definition of `IsMetricCompatibleMathlib`.
  intro X Y Z x
  -- Use the Synthetic `koszul_metric_compat` to get
  --   (embed X)(met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)
  -- at the section level, then evaluate at `x`.
  have h_synth := (concreteKoszulConnection_isLeviCivita I M g).1 X Y Z
  -- `h_synth : (concreteDerivationEmbedding I M).embed X ((concreteMetricDuality I M g).g Y Z)
  --            = (concreteMetricDuality I M g).g (concreteKoszulConnection I M g X Y) Z
  --              + (concreteMetricDuality I M g).g Y (concreteKoszulConnection I M g X Z)`
  -- Evaluate both sides at `x`.
  have h_synth_pt : (((concreteDerivationEmbedding I M).embed X)
      ((concreteMetricDuality I M g).g Y Z) : C^∞⟮I, M; ℝ⟯) x =
      ((concreteMetricDuality I M g).g (concreteKoszulConnection I M g X Y) Z +
        (concreteMetricDuality I M g).g Y (concreteKoszulConnection I M g X Z) :
          C^∞⟮I, M; ℝ⟯) x := by
    rw [h_synth]
  -- Simplify pointwise using definitions.
  -- LHS:  ((emb X) (met.g Y Z)) x = vectorFieldAction I M X (met.g Y Z) x
  --       = vectorFieldAction I M X ⟨fun y => g.inner y (Y y) (Z y), _⟩ x
  --       (since (met.g Y Z) has the same underlying function as y => g.inner y (Y y) (Z y)).
  -- RHS:  (met.g (conn X Y) Z + met.g Y (conn X Z)) x
  --       = g.inner x (conn X Y x) (Z x) + g.inner x (Y x) (conn X Z x)
  --       = g.inner x ((concreteKoszulCov g) Y x (X x)) (Z x)
  --         + g.inner x (Y x) ((concreteKoszulCov g) Z x (X x))
  --       (via the bridge lemma concreteKoszulCov_apply_section).
  -- Rewrite the Synthetic identity at the pointwise level, matching the
  -- Mathlib-level predicate.
  -- Step 1: RHS rewriting.
  have h_rhs_rewrite :
      ((concreteMetricDuality I M g).g (concreteKoszulConnection I M g X Y) Z +
        (concreteMetricDuality I M g).g Y (concreteKoszulConnection I M g X Z) :
          C^∞⟮I, M; ℝ⟯) x =
      g.inner x ((concreteKoszulCov I M g) Y x (X x)) (Z x) +
        g.inner x (Y x) ((concreteKoszulCov I M g) Z x (X x)) := by
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [concreteMetricDuality_g_eval, concreteMetricDuality_g_eval,
        concreteKoszulCov_apply_section, concreteKoszulCov_apply_section]
  -- Step 2: LHS rewriting.
  -- `(emb X) (met.g Y Z)` equals `vectorFieldActionSmooth I M X (met.g Y Z)`.
  -- Evaluated at `x`, this is `vectorFieldAction I M X (met.g Y Z) x`.
  -- `(met.g Y Z : C^∞⟮I, M; ℝ⟯)` as a function equals `fun y => g.inner y (Y y) (Z y)`.
  -- Since `vectorFieldAction` only depends on the underlying function, we can
  -- rewrite it to the form `vectorFieldAction I M X ⟨fun y => g.inner y (Y y) (Z y), _⟩ x`.
  have h_fn_eq : ((concreteMetricDuality I M g).g Y Z : M → ℝ) =
      (fun y => g.inner y (Y y) (Z y)) := by
    funext y
    exact concreteMetricDuality_g_eval I M g Y Z y
  -- Define the smooth wrapper appearing in `IsMetricCompatibleMathlib`.
  set f_inner : C^∞⟮I, M; ℝ⟯ := ⟨fun y => g.inner y (Y y) (Z y), by
    intro x₀
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => (⟨x, g.inner x⟩ :
          TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) :=
      g.contMDiff.of_le le_top
    have hgX : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun x => (⟨x, g.inner x (Y x)⟩ :
          TotalSpace (E →L[ℝ] ℝ)
            (fun y : M => TangentSpace I y →L[ℝ] ℝ))) x₀ :=
      ContMDiffAt.clm_bundle_apply hg.contMDiffAt Y.contMDiff.contMDiffAt
    have hgXY : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => (⟨x, g.inner x (Y x) (Z x)⟩ :
          TotalSpace ℝ (fun _ : M => ℝ))) x₀ :=
      ContMDiffAt.clm_bundle_apply hgX Z.contMDiff.contMDiffAt
    simp only [contMDiffAt_totalSpace] at hgXY
    exact hgXY.2⟩ with hf_inner_def
  -- `met.g Y Z` and `f_inner` are the same smooth function (same underlying fn).
  have h_metg_eq_f : (concreteMetricDuality I M g).g Y Z = f_inner := by
    apply ContMDiffMap.ext
    intro y
    exact concreteMetricDuality_g_eval I M g Y Z y
  -- LHS simp: `((emb X) (met.g Y Z) : M → ℝ) x = vectorFieldAction I M X (met.g Y Z) x`.
  have h_lhs_rewrite :
      ((concreteDerivationEmbedding I M).embed X
          ((concreteMetricDuality I M g).g Y Z) : C^∞⟮I, M; ℝ⟯) x =
      vectorFieldAction I M X f_inner x := by
    rw [h_metg_eq_f]
    rfl
  -- Combine both rewrites with the Synthetic identity.
  rw [h_lhs_rewrite] at h_synth_pt
  rw [h_rhs_rewrite] at h_synth_pt
  -- The goal matches `h_synth_pt` up to the change of function wrapper.
  exact h_synth_pt

/-! ### Torsion-free (Mathlib-level) for `concreteKoszulCov`

We now prove that the Mathlib torsion tensor of `concreteKoszulCov g` is
identically zero. The strategy uses `CovariantDerivative.torsion_eq_zero_iff`
to reduce to the pointwise identity

```
  (concreteKoszulCov g) Y x (X x) - (concreteKoszulCov g) X x (Y x) = mlieBracket I X Y x
```

for all fiber-valued functions `X, Y` that are `MDifferentiableAt` at `x`.

The proof combines:

1. For `MDiffAt` sections, the fiber CLM
   `concreteKoszulCovFun g Y x = koszulFiberCLM g Y' x` where `Y'` is a globally
   smooth section matching `Y`'s 1-jet at `x`.
2. The smooth-section identity
   `koszulFiberCLM g Y' x (X' x) = concreteKoszulConnection g X' Y' x` for any
   globally smooth `X'`.
3. The Synthetic torsion-free law for the concrete Koszul connection:
   `concreteKoszulConnection g X' Y' - concreteKoszulConnection g Y' X' =
   bracket emb X' Y'` (from `koszul_torsion_free`).
4. The bracket-equals-`mlieBracketSection` identity (from
   `bracket_eq_mlieBracketSection`).
5. The 1-jet invariance of `mlieBracket` for `MDifferentiableAt` vector fields,
   which we prove below using the chart-pullback formula. -/

/-! #### General trivialization-read and chart-pullback lemmas -/

/-- The chart pullback of a raw tangent-section `σ` through `(extChartAt I x₀).symm`
equals the trivialization-read on the chart source. This is the MDiffAt-general
version of `KoszulGerm.mpullbackWithin_extChartAt_symm_eq_trivReadAt`. -/
private theorem mpullback_extChartAt_symm_eq_trivRead_general
    (σ : Π x : M, TangentSpace I x) (x₀ : M) (y : M)
    (hy_src : y ∈ (extChartAt I x₀).source) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm σ (Set.range I)
      (extChartAt I x₀ y) =
    (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2 := by
  have hy_tgt : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy_src
  have hy_chart : y ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I)] at hy_src
  have hy_base : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := hy_chart
  -- Rewrite triv-read via `continuousLinearMapAt`.
  rw [show (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2 =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ y (σ y) from by
    rw [Trivialization.continuousLinearMapAt_apply,
      (trivializationAt E (TangentSpace I : M → Type _) x₀).coe_linearMapAt_of_mem hy_base]]
  simp only [VectorField.mpullbackWithin_apply]
  -- The inverse of `mfderivWithin (extChartAt I x₀).symm (range I) (φ y)` equals
  -- `mfderiv (extChartAt I x₀) y` via `ContinuousLinearMap.inverse_eq`.
  have h_inv_eq :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (Set.range I)
        (extChartAt I x₀ y)).inverse =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) ((extChartAt I x₀).symm (extChartAt I x₀ y)) :=
    ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy_tgt)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy_tgt)
  rw [h_inv_eq, (extChartAt I x₀).left_inv hy_src]
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hy_chart]
  rfl

/-- For `σ` `MDifferentiableAt` at `x₀` (in total-space form), the trivialization-read
`y ↦ (triv ⟨y, σ y⟩).2` is `MDifferentiableAt` at `x₀`. -/
private theorem trivRead_mdifferentiableAt_of_mdifferentiableAt
    (σ : Π x : M, TangentSpace I x) (x₀ : M)
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀) :
    MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) x₀ :=
  (mdifferentiableAt_section (IB := I) (F := E) (E := (TangentSpace I : M → Type _))
    σ (b₀ := x₀)).mp hσ

/-- For `MDiffAt` section `σ` at `x₀`, the chart-pullback has `fderivWithin` at `y₀`
determined by the trivialization-read mfderiv at `x₀`. Specifically, if
`mfderiv (trivRead) x₀ = mfderiv (trivRead) x₀` for two MDiffAt sections, then
their chart-pullback `fderivWithin`s match. -/
private theorem fderivWithin_mpullback_eq_of_trivRead_mfderiv_eq
    {σ σ' : Π x : M, TangentSpace I x} {x₀ : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, σ' y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hmf : mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) x₀ =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) x₀) :
    fderivWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm σ (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀) =
    fderivWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm σ' (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀) := by
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  -- The chart pullback of σ agrees with `trivRead σ x₀ ∘ φ.symm` on a nbhd-within `s` of `y₀`.
  have h_eq_nbhd_σ :
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm σ s) =ᶠ[𝓝[s] y₀]
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) ∘ φ.symm) := by
    have htgt_nw : (extChartAt I x₀).target ∈ 𝓝[Set.range I] (extChartAt I x₀ x₀) :=
      extChartAt_target_mem_nhdsWithin x₀
    filter_upwards [htgt_nw] with y hy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hh := mpullback_extChartAt_symm_eq_trivRead_general I M σ x₀ (φ.symm y) hy_src
    rw [φ.right_inv hy] at hh
    exact hh
  have h_eq_nbhd_σ' :
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm σ' s) =ᶠ[𝓝[s] y₀]
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) ∘ φ.symm) := by
    have htgt_nw : (extChartAt I x₀).target ∈ 𝓝[Set.range I] (extChartAt I x₀ x₀) :=
      extChartAt_target_mem_nhdsWithin x₀
    filter_upwards [htgt_nw] with y hy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hh := mpullback_extChartAt_symm_eq_trivRead_general I M σ' x₀ (φ.symm y) hy_src
    rw [φ.right_inv hy] at hh
    exact hh
  rw [Filter.EventuallyEq.fderivWithin_eq h_eq_nbhd_σ
        (h_eq_nbhd_σ.self_of_nhdsWithin hy₀s)]
  rw [Filter.EventuallyEq.fderivWithin_eq h_eq_nbhd_σ'
        (h_eq_nbhd_σ'.self_of_nhdsWithin hy₀s)]
  -- Now we compute `fderivWithin (trivRead σ x₀ ∘ φ.symm) s y₀` via the chain rule.
  have hg_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) x₀ :=
    trivRead_mdifferentiableAt_of_mdifferentiableAt I M σ x₀ hσ
  have hg'_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) x₀ :=
    trivRead_mdifferentiableAt_of_mdifferentiableAt I M σ' x₀ hσ'
  have hφ_symm_y₀ : φ.symm y₀ = x₀ := by rw [hy₀]; exact φ.left_inv (mem_extChartAt_source x₀)
  have hy₀_tgt : y₀ ∈ φ.target := by
    rw [hy₀]; exact φ.map_source (mem_extChartAt_source x₀)
  have hφsymm_mdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm s y₀ := by
    have hsmooth : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (Set.range I) y₀ :=
      contMDiffWithinAt_extChartAt_symm_range (n := ∞) (I := I) x₀ hy₀_tgt
    exact hsmooth.mdifferentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hUniq : UniqueMDiffWithinAt 𝓘(ℝ, E) s y₀ :=
    I.uniqueMDiffOn _ hy₀s
  have hg_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) Set.univ
      (φ.symm y₀) := by
    rw [hφ_symm_y₀]
    exact hg_mdiff.mdifferentiableWithinAt
  have hg'_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) Set.univ
      (φ.symm y₀) := by
    rw [hφ_symm_y₀]
    exact hg'_mdiff.mdifferentiableWithinAt
  have hφ_maps : s ⊆ φ.symm ⁻¹' (Set.univ : Set M) := fun _ _ => Set.mem_univ _
  have hcomp_σ :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) ∘ φ.symm)
          s y₀ =
      (mfderivWithin I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) Set.univ
        (φ.symm y₀)).comp (mfderivWithin 𝓘(ℝ, E) I φ.symm s y₀) :=
    mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) y₀
      hg_within hφsymm_mdiff hφ_maps hUniq
  have hcomp_σ' :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) ∘ φ.symm)
          s y₀ =
      (mfderivWithin I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) Set.univ
        (φ.symm y₀)).comp (mfderivWithin 𝓘(ℝ, E) I φ.symm s y₀) :=
    mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) y₀
      hg'_within hφsymm_mdiff hφ_maps hUniq
  -- Convert `fderivWithin = mfderivWithin` (model space case).
  rw [show fderivWithin ℝ
      ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) ∘ φ.symm) s y₀
    = mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ y⟩).2) ∘ φ.symm)
          s y₀ from (mfderivWithin_eq_fderivWithin).symm]
  rw [show fderivWithin ℝ
      ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) ∘ φ.symm) s y₀
    = mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, σ' y⟩).2) ∘ φ.symm)
          s y₀ from (mfderivWithin_eq_fderivWithin).symm]
  rw [hcomp_σ, hcomp_σ', hφ_symm_y₀, mfderivWithin_univ, mfderivWithin_univ, hmf]
  rfl

/-- The value of the chart-pullback at `y₀ = (extChartAt I x₀) x₀` equals the
section's value at `x₀`. -/
private theorem mpullback_at_y₀_eq_value
    (σ : Π x : M, TangentSpace I x) (x₀ : M) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm σ (Set.range I)
      (extChartAt I x₀ x₀) =
    (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨x₀, σ x₀⟩).2 := by
  exact mpullback_extChartAt_symm_eq_trivRead_general I M σ x₀ x₀ (mem_extChartAt_source x₀)

/-- **1-jet invariance of `mlieBracket` for `MDiffAt` vector fields.**

If `V, V'` are both `MDiffAt` at `x₀` (in total-space form) with matching
value and trivialization-read `mfderiv` at `x₀`, and similarly for `W, W'`,
then `mlieBracket I V W x₀ = mlieBracket I V' W' x₀`.

This generalizes `KoszulGerm.mlieBracketSection_snd_of_zero_1jet` (which is
stated only for smooth sections with zero 1-jet difference) to arbitrary
`MDifferentiableAt` vector fields with matching 1-jets. -/
private theorem mlieBracket_1jet_invariant
    {V V' W W' : Π x : M, TangentSpace I x} {x₀ : M}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hV' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V' y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, W y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hW' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, W' y⟩ : TotalSpace E (TangentSpace I))) x₀)
    (hV_val : V x₀ = V' x₀)
    (hW_val : W x₀ = W' x₀)
    (hV_mf : mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, V y⟩).2) x₀ =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, V' y⟩).2) x₀)
    (hW_mf : mfderiv I 𝓘(ℝ, E)
      (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, W y⟩).2) x₀ =
      mfderiv I 𝓘(ℝ, E)
        (fun y => (trivializationAt E (TangentSpace I : M → Type _) x₀ ⟨y, W' y⟩).2) x₀) :
    VectorField.mlieBracket I V W x₀ = VectorField.mlieBracket I V' W' x₀ := by
  -- Unfold `mlieBracket` as `mlieBracketWithin I _ _ univ`.
  rw [show VectorField.mlieBracket I V W = VectorField.mlieBracketWithin I V W Set.univ from by
    simp]
  rw [show VectorField.mlieBracket I V' W' = VectorField.mlieBracketWithin I V' W' Set.univ from by
    simp]
  -- By `mlieBracketWithin_apply`, both brackets equal
  -- `(mfderiv φ x₀).inverse (lieBracketWithin ℝ V_tilde W_tilde s y₀)`
  -- where `V_tilde`, `W_tilde` are the chart pullbacks.
  rw [VectorField.mlieBracketWithin_apply (V := V) (W := W) (s := Set.univ) (x₀ := x₀)]
  rw [VectorField.mlieBracketWithin_apply (V := V') (W := W') (s := Set.univ) (x₀ := x₀)]
  simp only [Set.preimage_univ, Set.univ_inter]
  -- It remains to show the inner `lieBracketWithin` values match.
  congr 1
  -- Show: lieBracketWithin ℝ V_t W_t (range I) y₀ = lieBracketWithin ℝ V'_t W'_t (range I) y₀.
  -- By definition:
  --   lieBracketWithin V_t W_t s y₀
  --     = fderivWithin W_t s y₀ (V_t y₀) - fderivWithin V_t s y₀ (W_t y₀).
  change VectorField.lieBracketWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V (Set.range I))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀) =
    VectorField.lieBracketWithin ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V' (Set.range I))
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W' (Set.range I))
      (Set.range I) (extChartAt I x₀ x₀)
  simp only [VectorField.lieBracketWithin_eq]
  -- V_t y₀ = V'_t y₀ by the value match.
  have hV_t_val :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V (Set.range I)
          (extChartAt I x₀ x₀) =
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V' (Set.range I)
          (extChartAt I x₀ x₀) := by
    rw [mpullback_at_y₀_eq_value I M V x₀, mpullback_at_y₀_eq_value I M V' x₀]
    rw [hV_val]
  have hW_t_val :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W (Set.range I)
          (extChartAt I x₀ x₀) =
      VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W' (Set.range I)
          (extChartAt I x₀ x₀) := by
    rw [mpullback_at_y₀_eq_value I M W x₀, mpullback_at_y₀_eq_value I M W' x₀]
    rw [hW_val]
  -- fderivWithin V_t s y₀ = fderivWithin V'_t s y₀ by 1-jet matching.
  have hV_t_fd :
      fderivWithin ℝ
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V (Set.range I))
        (Set.range I) (extChartAt I x₀ x₀) =
      fderivWithin ℝ
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm V' (Set.range I))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fderivWithin_mpullback_eq_of_trivRead_mfderiv_eq (I := I) (M := M) hV hV' hV_mf
  have hW_t_fd :
      fderivWithin ℝ
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W (Set.range I))
        (Set.range I) (extChartAt I x₀ x₀) =
      fderivWithin ℝ
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W' (Set.range I))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fderivWithin_mpullback_eq_of_trivRead_mfderiv_eq (I := I) (M := M) hW hW' hW_mf
  rw [hV_t_val, hW_t_val, hV_t_fd, hW_t_fd]

/-! #### The torsion-free theorem -/

/-- The concrete Koszul covariant derivative `concreteKoszulCov I M g` on the
tangent bundle is torsion-free: its Mathlib `CovariantDerivative.torsion` tensor
is identically zero. The proof reduces via `torsion_eq_zero_iff` to the pointwise
identity `∇_X Y − ∇_Y X = [X, Y]` for differentiable vector fields, which follows
from the Synthetic-layer torsion-freeness carried by `concreteKoszulConnection_isLeviCivita`
after replacing `X, Y` by smooth 1-jet extensions at the point. -/
theorem concreteKoszulCov_torsion_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)) :
    (concreteKoszulCov I M g).torsion = 0 := by
  -- Apply `torsion_eq_zero_iff.mpr`: reduce to a pointwise identity for all
  -- `MDifferentiableAt` vector fields.
  rw [(concreteKoszulCov I M g).torsion_eq_zero_iff]
  intro X Y x hX hY
  -- We need to prove:
  --   (concreteKoszulCov g) Y x (X x) - (concreteKoszulCov g) X x (Y x)
  --     = mlieBracket I X Y x.
  -- Step 1: Build smooth 1-jet extensions X', Y' of X, Y at x.
  set X' := Realization.smoothExtensionAt_MDiff I M X x hX with hX'_def
  set Y' := Realization.smoothExtensionAt_MDiff I M Y x hY with hY'_def
  have hX'_val : X' x = X x := Realization.smoothExtensionAt_MDiff_value I M X x hX
  have hY'_val : Y' x = Y x := Realization.smoothExtensionAt_MDiff_value I M Y x hY
  have hX'_mf := Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv I M X x hX
  have hY'_mf := Realization.smoothExtensionAt_MDiff_fiberRead_mfderiv I M Y x hY
  -- Smooth sections are MDiffAt.
  have hX'_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (X' : Π x, TangentSpace I x) y⟩ : TotalSpace E (TangentSpace I))) x :=
    (X'.contMDiff x).mdifferentiableAt (by simp)
  have hY'_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (Y' : Π x, TangentSpace I x) y⟩ : TotalSpace E (TangentSpace I))) x :=
    (Y'.contMDiff x).mdifferentiableAt (by simp)
  -- Step 2: Translate the LHS into the Synthetic-layer `concreteKoszulConnection`.
  -- (a) `concreteKoszulCov g Y x (X x)`:
  --   First, rewrite `concreteKoszulCov g Y x = concreteKoszulCovFun g Y x` (coeFun).
  have h_LHS_Y : (concreteKoszulCov I M g) Y x (X x) =
      concreteKoszulConnection I M g X' Y' x := by
    change (concreteKoszulCovFun I M g Y) x (X x) = concreteKoszulConnection I M g X' Y' x
    -- By 1-jet choice-invariance, `concreteKoszulCovFun g Y x = koszulFiberCLM g Y' x`.
    rw [concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g Y x hY Y' hY'_val hY'_mf]
    -- `koszulFiberCLM g Y' x (X x) = koszulFiberCLM g Y' x (X' x)` since X x = X' x.
    rw [show X x = (X' : Π x, TangentSpace I x) x from hX'_val.symm]
    -- `koszulFiberCLM g Y' x (X' x) = concreteKoszulConnection g X' Y' x`.
    exact koszulFiberCLM_apply_section I M g Y' X' x
  have h_LHS_X : (concreteKoszulCov I M g) X x (Y x) =
      concreteKoszulConnection I M g Y' X' x := by
    change (concreteKoszulCovFun I M g X) x (Y x) = concreteKoszulConnection I M g Y' X' x
    rw [concreteKoszulCovFun_eq_koszulFiberCLM_of_1jet_eq I M g X x hX X' hX'_val hX'_mf]
    rw [show Y x = (Y' : Π x, TangentSpace I x) x from hY'_val.symm]
    exact koszulFiberCLM_apply_section I M g X' Y' x
  rw [h_LHS_Y, h_LHS_X]
  -- Step 3: Use the Synthetic `koszul_torsion_free` theorem.
  -- `IsTorsionFree emb conn` gives `conn X' Y' - conn Y' X' = bracket emb X' Y'`.
  have h_tf := (concreteKoszulConnection_isLeviCivita I M g).2
  -- h_tf : IsTorsionFree (concreteDerivationEmbedding I M) (concreteKoszulConnection I M g)
  have h_tf_eq := h_tf X' Y'
  -- h_tf_eq : concreteKoszulConnection I M g X' Y' - concreteKoszulConnection I M g Y' X'
  --           = bracket (concreteDerivationEmbedding I M) X' Y'
  -- Evaluate at x and use bracket_eq_mlieBracketSection.
  have h_tf_pt : concreteKoszulConnection I M g X' Y' x -
      concreteKoszulConnection I M g Y' X' x =
      (bracket (concreteDerivationEmbedding I M) X' Y' : V_k I M) x := by
    have h_congr := congrArg (fun (s : V_k I M) => s x) h_tf_eq
    simpa using h_congr
  rw [h_tf_pt]
  -- Step 4: `bracket emb X' Y' = mlieBracketSection I M X' Y'`.
  rw [bracket_eq_mlieBracketSection]
  -- Step 5: `mlieBracketSection I M X' Y' x = VectorField.mlieBracket I X' Y' x`, which
  -- by 1-jet invariance equals `VectorField.mlieBracket I X Y x = mlieBracket I X Y x`.
  change VectorField.mlieBracket I (X' : Π x, TangentSpace I x) (Y' : Π x, TangentSpace I x) x =
    VectorField.mlieBracket I X Y x
  -- Apply mlieBracket_1jet_invariant in reverse (the roles of V,V' and W,W' are swapped).
  symm
  -- hX'_mf : mfderiv (trivRead X') x = mfderiv (trivRead X) x
  --   (note the order: smoothExtensionAt_MDiff_fiberRead_mfderiv gives
  --    mfderiv (trivRead X' ...) x = mfderiv (trivRead X ...) x)
  exact mlieBracket_1jet_invariant I M hX hX'_mdiff hY hY'_mdiff hX'_val.symm hY'_val.symm
    hX'_mf.symm hY'_mf.symm

end KoszulCov

end
