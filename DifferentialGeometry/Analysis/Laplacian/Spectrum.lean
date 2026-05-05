import DifferentialGeometry.Analysis.Laplacian.Resolvent
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

/-!
# Spectrum of the L²-side resolvent and the variational Laplacian

For a closed Riemannian manifold `(M, g)`, this file develops the spectral
decomposition of the L²-side resolvent

  `R := resolventL2 g : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g`

of the variational Laplacian, conditional on the explicit hypothesis that
`R` is a compact operator.

Given the compactness hypothesis, Mathlib's spectral theorem for compact
self-adjoint operators (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
and `ContinuousLinearMap.finite_dimensional_eigenspace`) yields:

* the eigenspaces of `R` at non-zero eigenvalues are finite-dimensional;
* the eigenspaces of `R` (across all eigenvalues) span a dense subspace of
  `Lp ℝ 2 μ_g` (their orthogonal complement is trivial);
* every nonzero eigenvalue lies in `[0, 1]` (non-negative by symmetry of the
  variational form, ≤ 1 by coercivity);
* on each shell `{|μ| ≥ ε}`, `ε > 0`, only finitely many eigenvalues occur,
  so the nonzero eigenvalues form a discrete set with `0` as the sole
  possible accumulation point.

The translation between resolvent eigenvalues and Laplacian eigenvalues:
if `R u = μ u` with `μ ≠ 0` and `u ≠ 0`, then `(1 - Δ_g) u = μ⁻¹ u`,
i.e. `Δ_g u = -((1 - μ)/μ) u`. With the geometer convention
`Δ_g = div_g ∘ grad_g`, the corresponding non-negative Laplacian eigenvalue
is `λ := (1 - μ)/μ`. Resolvent eigenvectors lift uniquely to elements of
`laplacianDomain g` via the resolvent.

## Main definitions

* `resolventEigenspace g μ` — the eigenspace of `resolventL2 g` at `μ`,
  packaged as a `Submodule ℝ (Lp ℝ 2 μ_g)`.
* `laplacianEigenvalueOf μ` — the Laplacian eigenvalue `(1 - μ)/μ`
  corresponding to a non-zero resolvent eigenvalue `μ`.

## Main results

* `resolventEigenspace_finiteDim` — under compactness, each non-zero
  eigenspace is finite-dimensional.
* `resolventEigenspaces_iSup_orthogonal_eq_bot` — under compactness, the
  orthogonal complement of the supremum of eigenspaces is trivial.
* `resolvent_eigenvalue_le_one` — every eigenvalue of `R` with non-zero
  eigenvector lies in `[0, 1]`.
* `laplacianEigenvalueOf_nonneg_of_resolventEigenvalue` — translation:
  the corresponding Laplacian eigenvalue is non-negative.
* `resolventEigenvector_lifts_to_laplacianDomain` — every non-zero
  resolvent eigenvector lifts uniquely to `laplacianDomain g`.
* `laplacianOp_of_resolventEigenvector_lift` — the variational Laplacian
  acts on the lifted eigenvector by multiplication by the corresponding
  negative Laplacian eigenvalue.
* `resolvent_eigenvalues_finite_above` — for any `ε > 0`, only finitely
  many eigenvalues `μ` of `R` satisfy `ε ≤ |μ|`.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_g)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Norm bound for `H1ComplToLp`

We need the bound `‖H1ComplToLp v‖_{L²} ≤ ‖v‖_{H¹}` for the proof that
resolvent eigenvalues are ≤ 1. The bound holds on smooth scalars (where
`smoothToLp` is non-expansive) and extends to all of `H1Compl g` by
density. -/

/-- The pointwise bound `‖H1ComplToLp v‖ ≤ ‖v‖` for `v ∈ H1Compl g`. -/
lemma norm_H1ComplToLp_apply_le (g : SmoothRiemannianMetric I M)
    (v : H1Compl g) :
    ‖H1ComplToLp (I := I) (M := M) g v‖ ≤ ‖v‖ := by
  -- Reduce to the dense subset of smooth scalars by `induction_on`.
  refine UniformSpace.Completion.induction_on (α := SmoothScalar g) v ?_ ?_
  · -- The set `{a | ‖H1ComplToLp a‖ ≤ ‖a‖}` is closed by continuity of both sides.
    have h_cont_lhs : Continuous (fun w : H1Compl g =>
        ‖H1ComplToLp (I := I) (M := M) g w‖) :=
      (H1ComplToLp (I := I) (M := M) g).continuous.norm
    have h_cont_rhs : Continuous (fun w : H1Compl g => ‖w‖) := continuous_norm
    exact isClosed_le h_cont_lhs h_cont_rhs
  · intro a
    -- For smooth `a`: `H1ComplToLp (a : H1Compl g) = smoothToLp a` and `‖smoothToLp a‖ ≤ ‖a‖`.
    have h_eq : H1ComplToLp (I := I) (M := M) g
          ((a : H1Compl g)) =
        smoothToLp (I := I) (M := M) g a := by
      have h := H1ComplToLp_smoothToH1Compl (I := I) (M := M) g a
      -- `H1ComplToLp (smoothToH1Compl g a) = smoothToLp g a`, and
      -- `smoothToH1Compl g a = (a : H1Compl g)` (definitionally, via toComplL).
      simpa using h
    have h_norm : ‖((a : H1Compl g) : H1Compl g)‖ = ‖a‖ := by
      -- `(↑) : SmoothScalar g → H1Compl g` is the isometric embedding `toComplL`.
      change ‖(UniformSpace.Completion.toCompl a : H1Compl g)‖ = ‖a‖
      exact UniformSpace.Completion.norm_coe a
    rw [h_eq, h_norm]
    exact a.norm_smoothToLp_le

/-! ## Eigenspaces of the resolvent -/

/-- The eigenspace of the resolvent `R = resolventL2 g` at the scalar `μ`,
viewed as an `ℝ`-submodule of `Lp ℝ 2 μ_g`.

For `μ ≠ 0`, under the compactness hypothesis on `R` this submodule is
finite-dimensional (`resolventEigenspace_finiteDim`). The eigenspaces
across all `μ` span a dense subspace of `Lp ℝ 2 μ_g`
(`resolventEigenspaces_iSup_orthogonal_eq_bot`). -/
noncomputable def resolventEigenspace (g : SmoothRiemannianMetric I M) (μ : ℝ) :
    Submodule ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  Module.End.eigenspace
    ((resolventL2 (I := I) (M := M) g).toLinearMap) μ

/-- Membership in the resolvent eigenspace: `u ∈ resolventEigenspace g μ`
iff `R u = μ • u`. -/
lemma mem_resolventEigenspace_iff (g : SmoothRiemannianMetric I M) (μ : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    u ∈ resolventEigenspace (I := I) (M := M) g μ ↔
      resolventL2 (I := I) (M := M) g u = μ • u := by
  unfold resolventEigenspace
  rw [Module.End.mem_eigenspace_iff]
  rfl

/-- **Finite-dimensionality of nonzero eigenspaces.** Under compactness of
`R = resolventL2 g`, each eigenspace at a non-zero scalar is
finite-dimensional. This is the spectral theorem for compact operators
applied to `R`. -/
theorem resolventEigenspace_finiteDim
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g))
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (resolventEigenspace (I := I) (M := M) g μ) := by
  -- Direct application of Mathlib's `finite_dimensional_eigenspace`.
  exact ContinuousLinearMap.finite_dimensional_eigenspace hCompact μ hμ

/-! ## Total span of the eigenspaces -/

/-- **Spectral theorem (totality of eigenspaces).** Under compactness of
`R = resolventL2 g`, the eigenspaces span `Lp ℝ 2 μ_g` densely: the
orthogonal complement of their supremum is trivial.

This is `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
applied to the (already established) self-adjointness of `R`. -/
theorem resolventEigenspaces_iSup_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g)) :
    (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ)ᗮ = ⊥ := by
  -- Mathlib's compact self-adjoint spectral theorem.
  -- The supremum is exactly `⨆ μ, eigenspace (R.toLinearMap) μ`,
  -- which by definition matches `resolventEigenspace`.
  have hSymm : (resolventL2 (I := I) (M := M) g).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  -- Note: `resolventEigenspace g μ` unfolds to
  -- `Module.End.eigenspace ((resolventL2 g).toLinearMap) μ`.
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    hCompact hSymm

/-! ## Eigenvalue translation: resolvent ↔ Laplacian -/

/-- Translation of a non-zero resolvent eigenvalue `μ` to the
corresponding Laplacian eigenvalue `λ := (1 - μ)/μ`.

Mathematical content: if `R u = μ u` with `R = (1 - Δ_g)⁻¹` and `μ ≠ 0`,
then `(1 - Δ_g) u = μ⁻¹ u`, hence `Δ_g u = -((1 - μ)/μ) u`. With the
geometer convention `spectrum(Δ_g) ⊆ (-∞, 0]`, the corresponding
non-negative Laplacian eigenvalue is `λ`. -/
def laplacianEigenvalueOf (μ : ℝ) : ℝ := (1 - μ) / μ

/-! ## Resolvent eigenvalues lie in `[0, 1]` -/

/-- For a resolvent eigenvector `u` with eigenvalue `μ`, the defining
variational identity
  `μ * ‖u‖² = ⟨R u, u⟩_{L²} = ‖resolvent g u‖²_{H¹}`. -/
private lemma mul_norm_sq_eq_h1Norm_resolvent_sq
    (g : SmoothRiemannianMetric I M)
    {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    μ * (‖u‖ ^ 2) =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 := by
  -- Setting `v = resolvent g u` in the variational identity:
  --   `⟨resolvent g u, resolvent g u⟩_{H¹} = ⟨H1ComplToLp(resolvent g u), u⟩_{L²}`
  -- and `H1ComplToLp(resolvent g u) = R u = μ • u`.
  have hRu : resolventL2 (I := I) (M := M) g u = μ • u :=
    (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  have h_h1 : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u),
        u⟫_ℝ :=
    resolvent_inner_eq_lpFunctional (I := I) (M := M) g u
      (resolvent (I := I) (M := M) g u)
  have h_lhs_to_norm : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) =
      resolventL2 (I := I) (M := M) g u := by
    rw [resolventL2_apply]
  rw [h_lhs_to_norm] at h_h1
  rw [h_replace, hRu] at h_h1
  -- h_h1 : ‖resolvent g u‖² = ⟪μ • u, u⟫
  rw [real_inner_smul_left] at h_h1
  rw [real_inner_self_eq_norm_sq] at h_h1
  linarith

/-- Every resolvent eigenvalue (with eigenvector `u ≠ 0`) is non-negative.
This follows from the variational identity
  `μ * ‖u‖² = ‖resolvent g u‖²_{H¹}`,
whose RHS is non-negative. -/
theorem resolvent_eigenvalue_nonneg
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0) :
    0 ≤ μ := by
  have h := mul_norm_sq_eq_h1Norm_resolvent_sq (I := I) (M := M) g hu
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have h_rhs_nn : 0 ≤ ‖resolvent (I := I) (M := M) g u‖ ^ 2 := sq_nonneg _
  -- μ * ‖u‖² ≥ 0 with ‖u‖² > 0 implies μ ≥ 0.
  have h_prod_nn : 0 ≤ μ * (‖u‖ ^ 2) := h.symm ▸ h_rhs_nn
  exact (mul_nonneg_iff_of_pos_right hu_pos).mp h_prod_nn

/-- For a resolvent eigenvalue `μ` with non-zero eigenvector `u`, the
bound `μ ≤ 1` holds (by coercivity of the H¹ inner product and the norm
bound `‖H1ComplToLp v‖_{L²} ≤ ‖v‖_{H¹}`).

Proof: from the variational identity
  `μ * ‖u‖² = ‖resolvent g u‖²_{H¹}`,
and the bound `‖μ u‖² = ‖R u‖² = ‖H1ComplToLp(resolvent g u)‖²_{L²} ≤ ‖resolvent g u‖²_{H¹}`,
we get `μ² ‖u‖² ≤ μ ‖u‖²`. With `‖u‖² > 0`, this yields `μ ≤ 1`
(combined with `μ ≥ 0`). -/
theorem resolvent_eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0) :
    μ ≤ 1 := by
  -- From the variational identity: μ * ‖u‖² = ‖resolvent g u‖²_{H¹}.
  have h_var := mul_norm_sq_eq_h1Norm_resolvent_sq (I := I) (M := M) g hu
  -- Norm bound for H1ComplToLp at resolvent u:
  have h_norm_bound :
      ‖H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u)‖ ≤
        ‖resolvent (I := I) (M := M) g u‖ :=
    norm_H1ComplToLp_apply_le (I := I) (M := M) g
      (resolvent (I := I) (M := M) g u)
  -- The LHS equals ‖μ • u‖_{L²} = |μ| * ‖u‖_{L²}.
  have hRu_eq_smul : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) = μ • u := by
    rw [show H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g u) =
        resolventL2 (I := I) (M := M) g u from by rw [resolventL2_apply]]
    exact (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  have h_norm_smul : ‖H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u)‖ = |μ| * ‖u‖ := by
    rw [hRu_eq_smul, norm_smul]
    rfl
  -- Square both sides of the bound.
  have h_abs_le_norm : |μ| * ‖u‖ ≤ ‖resolvent (I := I) (M := M) g u‖ :=
    h_norm_smul ▸ h_norm_bound
  have h_sq_bound : (|μ| * ‖u‖) ^ 2 ≤
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 := by
    have h_lhs_nn : 0 ≤ |μ| * ‖u‖ := by positivity
    nlinarith [h_abs_le_norm, h_lhs_nn]
  -- Use the variational identity to get μ² ‖u‖² ≤ μ ‖u‖².
  have h_chain : (|μ| * ‖u‖) ^ 2 ≤ μ * ‖u‖ ^ 2 := h_var ▸ h_sq_bound
  have h_expand : (|μ| * ‖u‖) ^ 2 = μ ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow]
    have hsq : |μ| ^ 2 = μ ^ 2 := sq_abs μ
    rw [hsq]
  have h_chain' : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_expand ▸ h_chain
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  -- So μ² ≤ μ.
  have hμ_sq_le : μ ^ 2 ≤ μ := by
    have h1 : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_chain'
    nlinarith [hu_pos]
  -- Together with μ ≥ 0, this forces μ ≤ 1.
  have hμ_nn : 0 ≤ μ :=
    resolvent_eigenvalue_nonneg (I := I) (M := M) g hu hu_ne
  -- If μ ≤ 1 fails, μ > 1, but then μ² > μ, contradiction.
  by_contra h_not
  push Not at h_not
  have h_mu_gt_one : 1 < μ := h_not
  have h_mu_pos : 0 < μ := lt_trans zero_lt_one h_mu_gt_one
  have h_lt : μ < μ ^ 2 := by nlinarith
  linarith

/-- Combined: every eigenvalue of `R` with non-zero eigenvector lies in
`[0, 1]`. -/
theorem resolvent_eigenvalue_mem_unit_interval
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0) :
    0 ≤ μ ∧ μ ≤ 1 :=
  ⟨resolvent_eigenvalue_nonneg (I := I) (M := M) g hu hu_ne,
    resolvent_eigenvalue_le_one (I := I) (M := M) g hu hu_ne⟩

/-- The translation `λ = (1 - μ)/μ` of a positive resolvent eigenvalue `μ`
yields a non-negative Laplacian eigenvalue.

Proof: a positive eigenvalue of `R` lies in `(0, 1]` (by the previous
results), so `1 - μ ≥ 0` and `μ > 0`, hence `(1 - μ)/μ ≥ 0`. -/
theorem laplacianEigenvalueOf_nonneg_of_resolventEigenvalue
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) (hu_ne : u ≠ 0)
    (hμ_pos : 0 < μ) :
    0 ≤ laplacianEigenvalueOf μ := by
  unfold laplacianEigenvalueOf
  have h_le_one : μ ≤ 1 :=
    resolvent_eigenvalue_le_one (I := I) (M := M) g hu hu_ne
  have h_num_nn : 0 ≤ 1 - μ := by linarith
  exact div_nonneg h_num_nn hμ_pos.le

/-! ## Resolvent eigenvectors lift to the Laplacian domain -/

/-- A non-zero resolvent eigenvector lifts uniquely to an element of the
Laplacian domain `laplacianDomain g ⊆ H1Compl g`.

Specifically: if `R u = μ • u` with `μ ≠ 0`, then setting
`v := μ⁻¹ • resolvent g u`, we have `v ∈ laplacianDomain g` (it is in the
range of `resolvent g`) and `H1ComplToLp v = u`. -/
theorem resolventEigenvector_lifts_to_laplacianDomain
    (g : SmoothRiemannianMetric I M) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    ∃ v : H1Compl g,
      v ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g v = u := by
  -- v := μ⁻¹ • resolvent g u; we show v = resolvent g (μ⁻¹ • u).
  refine ⟨μ⁻¹ • resolvent (I := I) (M := M) g u, ?_, ?_⟩
  · -- It is in the image of `resolvent g` (apply `resolvent g` to `μ⁻¹ • u`).
    rw [laplacianDomain_mem_iff]
    refine ⟨μ⁻¹ • u, ?_⟩
    rw [(resolvent (I := I) (M := M) g).map_smul]
  · -- H1ComplToLp (μ⁻¹ • resolvent g u) = μ⁻¹ • H1ComplToLp(resolvent g u)
    --                                   = μ⁻¹ • R u = μ⁻¹ • (μ • u) = u.
    have hRu : resolventL2 (I := I) (M := M) g u = μ • u :=
      (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
    have h_replace : H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g u) =
        resolventL2 (I := I) (M := M) g u := by
      rw [resolventL2_apply]
    rw [(H1ComplToLp (I := I) (M := M) g).map_smul]
    rw [h_replace, hRu, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- The variational Laplacian on the lifted resolvent eigenvector acts as
multiplication by the (negative of the) Laplacian eigenvalue.

Specifically, with `v := μ⁻¹ • resolvent g u`, we have `v ∈ laplacianDomain g`
and
  `Δ_g v = -((1 - μ)/μ) • u = -laplacianEigenvalueOf μ • u`. -/
theorem laplacianOp_of_resolventEigenvector_lift
    (g : SmoothRiemannianMetric I M) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    laplacianOp (I := I) (M := M) g
        ⟨μ⁻¹ • resolvent (I := I) (M := M) g u,
          (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
            ⟨μ⁻¹ • u, by
              rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ =
      -(laplacianEigenvalueOf μ) • u := by
  have hRu : resolventL2 (I := I) (M := M) g u = μ • u :=
    (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu
  -- Identify the Subtype with `resolvent (μ⁻¹ • u)`:
  have h_eq : (μ⁻¹ • resolvent (I := I) (M := M) g u :
        H1Compl (I := I) (M := M) g) =
      resolvent (I := I) (M := M) g (μ⁻¹ • u) := by
    rw [(resolvent (I := I) (M := M) g).map_smul]
  -- Convert the membership token: replace via `laplacianOp_resolvent (μ⁻¹ • u)`.
  rw [show (⟨μ⁻¹ • resolvent (I := I) (M := M) g u,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨μ⁻¹ • u, by
            rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g (μ⁻¹ • u),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨μ⁻¹ • u, rfl⟩⟩ from by
    apply Subtype.ext
    -- Underlying values agree by `(resolvent g).map_smul`.
    exact h_eq]
  rw [laplacianOp_resolvent]
  -- Goal: H1ComplToLp(resolvent (μ⁻¹ • u)) - (μ⁻¹ • u) = -laplacianEigenvalueOf μ • u.
  -- Compute H1ComplToLp(resolvent (μ⁻¹ • u)):
  --   = H1ComplToLp(μ⁻¹ • resolvent u) = μ⁻¹ • H1ComplToLp(resolvent u)
  --   = μ⁻¹ • R u = μ⁻¹ • (μ • u) = u.
  have h_HRl : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g (μ⁻¹ • u)) =
      u := by
    rw [(resolvent (I := I) (M := M) g).map_smul]
    rw [(H1ComplToLp (I := I) (M := M) g).map_smul]
    have h_replace : H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g u) =
        resolventL2 (I := I) (M := M) g u := by
      rw [resolventL2_apply]
    rw [h_replace, hRu, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  rw [h_HRl]
  -- Goal: u - (μ⁻¹ • u) = -laplacianEigenvalueOf μ • u
  have h_eq_smul : u - (μ⁻¹ • u) = (1 - μ⁻¹) • u := by
    rw [sub_smul, one_smul]
  rw [h_eq_smul]
  unfold laplacianEigenvalueOf
  -- (1 - μ⁻¹) = -((1 - μ)/μ).
  have h_alg : (1 - μ⁻¹) = -((1 - μ) / μ) := by
    field_simp
    ring
  rw [h_alg, neg_smul]

/-! ## Discrete spectrum: finiteness above each shell

We prove that for any `ε > 0`, only finitely many eigenvalues `μ` of
`R = resolventL2 g` satisfy `|μ| ≥ ε`. Since the eigenvalues of `R`
lie in `[0, 1]`, this is equivalent to: the set `{μ ∈ spectrum | μ ≥ ε}`
is finite. -/

/-- An eigenvalue of `R` admits a unit eigenvector (we choose one). -/
private lemma exists_unit_eigenvector
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) μ) :
    ∃ u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      u ∈ resolventEigenspace (I := I) (M := M) g μ ∧ ‖u‖ = 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := hμ.exists_hasEigenvector
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · -- `‖u‖⁻¹ • u` is also an eigenvector with the same eigenvalue.
    rw [mem_resolventEigenspace_iff]
    have hRu : resolventL2 (I := I) (M := M) g u = μ • u := by
      have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ := hu_mem
      exact (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu_in
    rw [(resolventL2 (I := I) (M := M) g).map_smul, hRu, smul_comm]
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt hu_pos)

/-- Eigenvectors with distinct eigenvalues are L²-orthogonal.

This is a standard consequence of self-adjointness; the eigenspaces are
mutually orthogonal. We cite the underlying Mathlib result
`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`. -/
private lemma resolvent_eigenvectors_orthogonal
    (g : SmoothRiemannianMetric I M) {μ ν : ℝ} (hμν : μ ≠ ν)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ)
    (hv : v ∈ resolventEigenspace (I := I) (M := M) g ν) :
    ⟪u, v⟫_ℝ = 0 := by
  have hSymm : ((resolventL2 (I := I) (M := M) g).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  -- Use `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`.
  have hortho := hSymm.orthogonalFamily_eigenspaces hμν
  -- `hortho : ∀ ⟨v, hv⟩ : eigenspace ⋯ μ, ∀ ⟨w, hw⟩ : eigenspace ⋯ ν, ⟪v, w⟫ = 0`.
  exact hortho ⟨u, hu⟩ ⟨v, hv⟩

/-- The image of an `R`-eigenvector at eigenvalue `μ` (with eigenvector
`u`) under `R` is `μ • u`. -/
private lemma resolventL2_apply_eigenvector
    (g : SmoothRiemannianMetric I M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hu : u ∈ resolventEigenspace (I := I) (M := M) g μ) :
    resolventL2 (I := I) (M := M) g u = μ • u :=
  (mem_resolventEigenspace_iff (I := I) (M := M) g μ u).mp hu

/-- For an injection `f : ℕ → ℝ` of distinct eigenvalues with `|f n| ≥ ε`,
together with chosen unit eigenvectors `v n`, the images `R (v n)` are
mutually `√2 ε`-separated. -/
private lemma resolventL2_image_separated_of_distinct_eigenvalues
    (g : SmoothRiemannianMetric I M)
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → ℝ} (hf_inj : Function.Injective f)
    (hf_size : ∀ n, ε ≤ |f n|)
    (v : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (hv_mem : ∀ n, v n ∈ resolventEigenspace (I := I) (M := M) g (f n))
    (hv_norm : ∀ n, ‖v n‖ = 1) :
    ∀ n m : ℕ, n ≠ m →
      Real.sqrt 2 * ε ≤ ‖resolventL2 (I := I) (M := M) g (v n) -
                         resolventL2 (I := I) (M := M) g (v m)‖ := by
  intro n m hnm
  have hRn : resolventL2 (I := I) (M := M) g (v n) = f n • v n :=
    resolventL2_apply_eigenvector (I := I) (M := M) g (hv_mem n)
  have hRm : resolventL2 (I := I) (M := M) g (v m) = f m • v m :=
    resolventL2_apply_eigenvector (I := I) (M := M) g (hv_mem m)
  have hfne : f n ≠ f m := fun h => hnm (hf_inj h)
  have hortho : ⟪v n, v m⟫_ℝ = 0 :=
    resolvent_eigenvectors_orthogonal (I := I) (M := M) g hfne
      (hv_mem n) (hv_mem m)
  -- ‖f n • v n - f m • v m‖² = ‖f n • v n‖² - 2 ⟪f n • v n, f m • v m⟫_ℝ + ‖f m • v m‖²
  --                          = (f n)² + (f m)²       (orthogonality + ‖v n‖ = ‖v m‖ = 1)
  have h_norm_sq : ‖f n • v n - f m • v m‖ ^ 2 =
      (f n) ^ 2 + (f m) ^ 2 := by
    rw [@norm_sub_sq_real]
    rw [norm_smul, norm_smul, mul_pow, mul_pow]
    rw [hv_norm n, hv_norm m]
    rw [one_pow, mul_one, mul_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [sq_abs, sq_abs]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [hortho, mul_zero, mul_zero]
    ring
  have h_norm_sq_lb : 2 * ε ^ 2 ≤ ‖f n • v n - f m • v m‖ ^ 2 := by
    rw [h_norm_sq]
    have h1 : ε ^ 2 ≤ (f n) ^ 2 := by
      have h_abs := hf_size n
      have h_abs_sq : ε ^ 2 ≤ |f n| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size n, sq_nonneg (|f n| - ε)]
      have h_sq_abs : |f n| ^ 2 = (f n) ^ 2 := sq_abs _
      linarith
    have h2 : ε ^ 2 ≤ (f m) ^ 2 := by
      have h_abs := hf_size m
      have h_abs_sq : ε ^ 2 ≤ |f m| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size m, sq_nonneg (|f m| - ε)]
      have h_sq_abs : |f m| ^ 2 = (f m) ^ 2 := sq_abs _
      linarith
    linarith
  -- Take square roots.
  have h_lhs_nn : 0 ≤ ‖f n • v n - f m • v m‖ := norm_nonneg _
  have h_target : Real.sqrt (2 * ε ^ 2) ≤ ‖f n • v n - f m • v m‖ := by
    rw [show ‖f n • v n - f m • v m‖ =
        Real.sqrt (‖f n • v n - f m • v m‖ ^ 2) from
      (Real.sqrt_sq h_lhs_nn).symm]
    exact Real.sqrt_le_sqrt h_norm_sq_lb
  have h_sqrt_eq : Real.sqrt (2 * ε ^ 2) = Real.sqrt 2 * ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (ε ^ 2 : ℝ) = ε * ε from sq ε]
    rw [Real.sqrt_mul_self hε.le]
  rw [hRn, hRm]
  rw [← h_sqrt_eq]
  exact h_target

/-- **Discreteness of the resolvent spectrum.** Under compactness of `R`,
for every `ε > 0`, only finitely many eigenvalues `μ` of `R` satisfy
`|μ| ≥ ε`.

Proof sketch (by contradiction): if there were infinitely many distinct
eigenvalues `μ_n` with `|μ_n| ≥ ε`, pick unit eigenvectors `v_n`. By
orthogonality of distinct eigenspaces and `‖v_n‖ = 1`, the images
`R v_n = μ_n v_n` are mutually `√2 ε`-separated. The sequence `(v_n)`
is bounded in the closed unit ball, so by compactness of `R` (mapping
the closed unit ball into a compact set), `(R v_n)` admits a convergent
(hence Cauchy) subsequence — but a Cauchy sequence cannot have all pairs
separated by `√2 ε > 0`. -/
theorem resolvent_eigenvalues_finite_above
    (g : SmoothRiemannianMetric I M)
    (hCompact : IsCompactOperator (resolventL2 (I := I) (M := M) g))
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite { μ : ℝ |
      Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } := by
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  -- Extract an injective sequence of elements of the set.
  let f : ℕ ↪ _ := h_inf.natEmbedding
  -- f : ℕ ↪ S; coerce to ℕ → ℝ.
  -- For each n, choose a unit eigenvector at f n.
  set f' : ℕ → ℝ := fun n => (f n : ℝ)
  have hf_eig : ∀ n, Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) (f' n) := fun n =>
    (f n).property.1
  have hf_size : ∀ n, ε ≤ |f' n| := fun n => (f n).property.2
  have hf_inj' : Function.Injective f' := by
    intro n m h
    -- f' n = f' m means (f n).val = (f m).val, hence f n = f m, hence n = m by injectivity of f.
    have h1 : f n = f m := by
      apply Subtype.ext; exact h
    exact Function.Embedding.injective f h1
  -- Choose unit eigenvectors.
  choose v hv_mem hv_norm using fun n =>
    exists_unit_eigenvector (I := I) (M := M) g (hf_eig n)
  -- Apply separation.
  have h_sep := resolventL2_image_separated_of_distinct_eigenvalues
    (I := I) (M := M) g hε hf_inj' hf_size v hv_mem hv_norm
  -- The sequence `v` is bounded (each element has norm 1).
  have h_v_in_ball : ∀ n, v n ∈ Metric.closedBall
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hv_norm n]
  -- Compactness ⇒ images of closed unit ball are in some compact set K.
  obtain ⟨K, hK_compact, hK_subset⟩ :=
    hCompact.image_closedBall_subset_compact (1 : ℝ)
  have h_R_v_in_K : ∀ n, resolventL2 (I := I) (M := M) g (v n) ∈ K := by
    intro n
    apply hK_subset
    refine ⟨v n, h_v_in_ball n, ?_⟩
    rfl
  -- Extract a convergent subsequence of (R v_n).
  obtain ⟨y, hyK, ψ, hψ_mono, hψy⟩ := hK_compact.tendsto_subseq h_R_v_in_K
  -- `(R v_{ψ n})` is Cauchy, so for `√2 ε > 0`, eventually pairs are within `√2 ε / 2`.
  have h_cauchy : CauchySeq (fun n =>
      resolventL2 (I := I) (M := M) g (v (ψ n))) :=
    hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at h_cauchy
  have h_sep_pos : 0 < Real.sqrt 2 * ε := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact mul_pos h_sqrt2_pos hε
  obtain ⟨N, hN⟩ := h_cauchy (Real.sqrt 2 * ε) h_sep_pos
  -- For N + 1 and N: dist (R v_{ψ (N+1)}, R v_{ψ N}) < √2 ε. But the separation says ≥ √2 ε.
  have h_dist : dist (resolventL2 (I := I) (M := M) g (v (ψ (N + 1))))
        (resolventL2 (I := I) (M := M) g (v (ψ N))) < Real.sqrt 2 * ε := by
    have := hN (N + 1) (Nat.le_succ N)
    -- `dist (a) (b) < ε`  same as `‖a - b‖ < ε`.
    exact this
  -- ψ is strictly monotone, so ψ (N+1) ≠ ψ N.
  have h_ne : ψ (N + 1) ≠ ψ N := by
    intro h_eq
    have h_lt : ψ N < ψ (N + 1) := hψ_mono (Nat.lt_succ_self N)
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  -- Apply separation: ‖R v_{ψ(N+1)} - R v_{ψ N}‖ ≥ √2 ε. Contradiction.
  have h_sep_specific := h_sep (ψ (N + 1)) (ψ N) h_ne
  rw [show dist (resolventL2 (I := I) (M := M) g (v (ψ (N + 1))))
        (resolventL2 (I := I) (M := M) g (v (ψ N))) =
      ‖resolventL2 (I := I) (M := M) g (v (ψ (N + 1))) -
        resolventL2 (I := I) (M := M) g (v (ψ N))‖ from
    dist_eq_norm _ _] at h_dist
  linarith [h_sep_specific, h_dist]

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M) (μ : ℝ) :
    Submodule ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  resolventEigenspace (I := I) (M := M) g μ

example (μ : ℝ) : ℝ := laplacianEigenvalueOf μ

end Laplacian
end Analysis
end DifferentialGeometry

end
