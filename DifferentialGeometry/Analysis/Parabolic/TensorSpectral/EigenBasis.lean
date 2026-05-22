import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral eigenbasis of the L²-side tensor resolvent

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
assembles the spectral eigenbasis of the compact self-adjoint resolvent

  `R := tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`

into a `HilbertBasis` of `TensorL2 r s g`, indexed by the disjoint union
of finite-dimensional bases of every nonzero-eigenvalue eigenspace.

All results are stated under the locally-constant chart hypothesis
`HasLocallyConstantChartAt H M`, which makes `R` a compact self-adjoint
operator on the Hilbert space `TensorL2 r s g`.

## Main definitions

* `TensorNonzeroResolventEigenvalue g r s` — the subtype of nonzero
  eigenvalues of `R` (paired with a nontriviality witness on the
  associated eigenspace).
* `tensorResolventEigenspaceONB` — for each nonzero eigenvalue `μ`, the
  standard orthonormal basis of the (finite-dimensional) eigenspace at
  `μ`.
* `tensorResolventEigenbasisVec` — the sigma-indexed orthonormal family
  of eigenvectors in `TensorL2 r s g`.
* `tensorResolventHilbertEigenbasisSigma` — the same data packaged as a
  `HilbertBasis` of `TensorL2 r s g`.

## Main results

* `tensorResolventEigenbasisVec_orthonormal` — the sigma-indexed family
  is orthonormal in `TensorL2 r s g`.
* `tensorResolventEigenbasisVec_span_orthogonal_eq_bot` — the orthogonal
  complement of the span of the basis vectors is trivial.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The subtype of nonzero resolvent eigenvalues -/

/-- A nonzero "resolvent eigenvalue" of the L²-side tensor resolvent
`R = tensorResolventL2 g r s`.

We package `μ ∈ ℝ` together with the proofs `μ ≠ 0` and a witness that
the associated eigenspace `tensorResolventEigenspace g r s μ` is
nontrivial (`≠ ⊥`). Under the uniform chart-Sobolev hypothesis the
nontriviality witness is equivalent to `Module.End.HasEigenvalue`, but
phrasing the subtype directly in terms of the eigenspace lets the basic
finite-dimensionality, orthogonality, and span statements proceed
without invoking eigenvalue/eigenvector lemmas every time. -/
def TensorNonzeroResolventEigenvalue
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  { μ : ℝ //
    tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 }

namespace TensorNonzeroResolventEigenvalue

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

/-- The underlying real value of a nonzero tensor resolvent eigenvalue. -/
def val (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) : ℝ :=
  μ.1

/-- The nontriviality witness for the associated eigenspace. -/
lemma eigenspace_ne_bot
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
  μ.2.1

/-- The nonzero hypothesis. -/
lemma val_ne_zero
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    μ.val ≠ 0 := μ.2.2

/-- A non-trivial eigenspace at `μ` actually contains an eigenvector,
hence `Module.End.HasEigenvalue ((tensorResolventL2 g r s).toLinearMap) μ`. -/
lemma hasEigenvalue
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    Module.End.HasEigenvalue
      ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ.val := by
  -- `tensorResolventEigenspace g r s μ.val ≠ ⊥` unfolds to
  -- `Module.End.eigenspace ... μ.val ≠ ⊥`, which is the definition of
  -- `Module.End.HasEigenvalue`.
  have h : tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
    μ.eigenspace_ne_bot
  unfold tensorResolventEigenspace at h
  exact h

@[ext] lemma ext
    (μ ν : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s)
    (h : μ.val = ν.val) : μ = ν := Subtype.ext h

end TensorNonzeroResolventEigenvalue

/-! ## Countability of `TensorNonzeroResolventEigenvalue g r s`

Under the uniform chart-Sobolev hypothesis, we exhibit the underlying set
of nonzero eigenvalues as a countable union of finite shells
`{|μ| ≥ 1/(n+1)}`, each of which is finite by
`tensorResolvent_eigenvalues_finite_above`. -/

/-- The underlying set of `TensorNonzeroResolventEigenvalue g r s`,
written as a countable union over `n : ℕ` of the finite shells
`{μ | HasEigenvalue ... μ ∧ 1/(n+1) ≤ |μ|}`. -/
private lemma nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    { μ : ℝ |
      tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 } =
      ⋃ n : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue
          ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ ∧
        (1 : ℝ) / (n + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ_eig_ne, hμ_ne⟩
    -- `tensorResolventEigenspace g r s μ ≠ ⊥` is `Module.End.HasEigenvalue _ μ`.
    have hμ_has : Module.End.HasEigenvalue
        ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ := by
      unfold tensorResolventEigenspace at hμ_eig_ne
      exact hμ_eig_ne
    have h_abs_pos : 0 < |μ| := abs_pos.mpr hμ_ne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_abs_pos
    refine Set.mem_iUnion.mpr ⟨n, hμ_has, ?_⟩
    exact le_of_lt hn
  · rintro hμ_in_union
    obtain ⟨n, hμ_in_n⟩ := Set.mem_iUnion.mp hμ_in_union
    obtain ⟨hμ_eig, hμ_size⟩ := hμ_in_n
    -- From `1/(n+1) > 0` and `1/(n+1) ≤ |μ|`, conclude `μ ≠ 0`.
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have h_abs_pos : 0 < |μ| := lt_of_lt_of_le h_pos hμ_size
    have hμ_ne : μ ≠ 0 := abs_pos.mp h_abs_pos
    -- `Module.End.HasEigenvalue` unfolds to `eigenspace ≠ ⊥`.
    have hμ_eig_ne : tensorResolventEigenspace
        (I := I) (M := M) g r s μ ≠ ⊥ := by
      unfold tensorResolventEigenspace
      exact hμ_eig
    exact ⟨hμ_eig_ne, hμ_ne⟩

/-- Under the uniform chart-Sobolev hypothesis, the set of nonzero
eigenvalues of `R = tensorResolventL2 g r s` is countable: a countable
union of finite sets. -/
theorem nonzero_tensor_resolvent_eigenvalues_set_countable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M) :
    Set.Countable
      { μ : ℝ |
        tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧
          μ ≠ 0 } := by
  rw [nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro n
  have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
  exact (tensorResolvent_eigenvalues_finite_above
    (I := I) (M := M) g r s h_atlas h_pos).countable

/-- Under the uniform chart-Sobolev hypothesis, the subtype
`TensorNonzeroResolventEigenvalue g r s` is countable. -/
theorem TensorNonzeroResolventEigenvalue.countable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M) :
    Countable (TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) := by
  unfold TensorNonzeroResolventEigenvalue
  exact (nonzero_tensor_resolvent_eigenvalues_set_countable
    (I := I) (M := M) g r s h_atlas).to_subtype

/-! ## Per-eigenspace finite-dimensionality -/

/-- For each `μ : TensorNonzeroResolventEigenvalue g r s`, under the
uniform chart-Sobolev hypothesis, the eigenspace at `μ.val` is finite-
dimensional. -/
@[reducible]
def TensorNonzeroResolventEigenvalue.finiteDimensional
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  tensorResolventEigenspace_finiteDim
    (I := I) (M := M) g r s h_atlas μ.val_ne_zero

/-! ## Per-eigenspace orthonormal basis -/

/-- The standard orthonormal basis of the (finite-dimensional) eigenspace
of `R = tensorResolventL2 g r s` at a nonzero eigenvalue, indexed by
`Fin (finrank ℝ ↥(tensorResolventEigenspace g r s μ.val))`. -/
noncomputable def tensorResolventEigenspaceONB
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)))
      ℝ (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  letI : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional h_atlas
  stdOrthonormalBasis ℝ
    (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)

/-! ## Orthogonality of the eigenspace family

Standard consequence of self-adjointness of `R`. -/

/-- The family of eigenspaces of `R = tensorResolventL2 g r s` indexed by
nonzero eigenvalues is an orthogonal family in `TensorL2 r s g`. -/
theorem tensorResolventEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    OrthogonalFamily ℝ
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ.val))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtypeₗᵢ) := by
  have hSymm :
      ((tensorResolventL2
        (I := I) (M := M) g r s).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s)
  have h_full : OrthogonalFamily ℝ
      (fun μ : ℝ =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ).subtypeₗᵢ) :=
    hSymm.orthogonalFamily_eigenspaces
  have h_inj : Function.Injective
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s => μ.val) :=
    fun μ ν h => Subtype.ext h
  exact h_full.comp h_inj

/-! ## Span identification: span of basis vectors equals iSup of eigenspaces -/

/-- The sigma-indexed family of vectors forming the eigenbasis: at index
`⟨μ, k⟩`, this is the `k`-th `stdOrthonormalBasis` vector of
`tensorResolventEigenspace g r s μ.val`, viewed as an element of
`TensorL2 r s g`. -/
noncomputable def tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    TensorL2 r s g :=
  ((tensorResolventEigenspaceONB
        (I := I) (M := M) h_atlas i.1 i.2 :
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val) :
    TensorL2 r s g)

/-- Each eigenbasis vector lies in its eigenspace. -/
theorem tensorResolventEigenbasisVec_mem
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i ∈
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val := by
  unfold tensorResolventEigenbasisVec
  exact (tensorResolventEigenspaceONB
    (I := I) (M := M) h_atlas i.1 i.2).property

/-- The eigenbasis family is orthonormal. -/
theorem tensorResolventEigenbasisVec_orthonormal
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    Orthonormal ℝ
      (tensorResolventEigenbasisVec (I := I) (M := M) (g := g) (r := r)
        (s := s) h_atlas) := by
  have h_fam :=
    tensorResolventEigenspace_orthogonalFamily_nonzero
      (I := I) (M := M) g r s
  have h_each : ∀ μ : TensorNonzeroResolventEigenvalue
        (I := I) (M := M) g r s,
      Orthonormal ℝ
        (tensorResolventEigenspaceONB
          (I := I) (M := M) h_atlas μ) :=
    fun μ =>
      (tensorResolventEigenspaceONB
        (I := I) (M := M) h_atlas μ).orthonormal
  have h_sig := h_fam.orthonormal_sigma_orthonormal h_each
  convert h_sig using 1

/-- Span of the eigenbasis vectors lies inside the supremum (over nonzero
eigenvalues) of the eigenspaces. -/
private lemma span_tensorResolventEigenbasisVec_le_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas)) ≤
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine SetLike.mem_coe.mpr ?_
  refine Submodule.mem_iSup_of_mem i.1 ?_
  exact tensorResolventEigenbasisVec_mem
    (I := I) (M := M) h_atlas i

/-- For each nonzero eigenvalue, its eigenspace is contained in the span
of the eigenbasis vectors (because the per-eigenspace basis already spans
the eigenspace). -/
private lemma tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≤
      Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas)) := by
  intro x hx
  letI : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional h_atlas
  set b := tensorResolventEigenspaceONB
    (I := I) (M := M) h_atlas μ
  have h_basis_span : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have h_subtype_apply :
      ((tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype '' Set.range b) =
      Set.range (fun k =>
        ((b k : tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
          TensorL2 r s g)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have h_in_basis_set : ∀ k : Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)),
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g) ∈
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas) := by
    intro k
    refine ⟨⟨μ, k⟩, ?_⟩
    rfl
  have h_subtype_subset : Set.range (fun k =>
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g)) ⊆
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas) := by
    rintro y ⟨k, rfl⟩
    exact h_in_basis_set k
  have hx_subtype : x =
      (tensorResolventEigenspace
        (I := I) (M := M) g r s μ.val).subtype ⟨x, hx⟩ := rfl
  have h_top_mem :
      (⟨x, hx⟩ :
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) ∈
      Submodule.span ℝ (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) := by
    rw [h_basis_span]; trivial
  have h_after_map : x ∈ Submodule.map
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype
        (Submodule.span ℝ (Set.range (b.toBasis :
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val)) →
          tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val))) := by
    refine ⟨⟨x, hx⟩, h_top_mem, rfl⟩
  rw [Submodule.map_span] at h_after_map
  have h_eq_basis : ((b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val)) = (b : _ → _) := by
    funext k
    have := OrthonormalBasis.coe_toBasis b
    exact congr_fun this k
  rw [h_eq_basis] at h_after_map
  rw [h_subtype_apply] at h_after_map
  exact Submodule.span_mono h_subtype_subset h_after_map

/-- The span (in `TensorL2 r s g`) of the eigenbasis vectors equals the
supremum over nonzero eigenvalues of the resolvent eigenspaces. -/
theorem span_tensorResolventEigenbasisVec_eq_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas)) =
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  refine le_antisymm
    (span_tensorResolventEigenbasisVec_le_iSup_eigenspace
      (I := I) (M := M) h_atlas) ?_
  exact iSup_le
    (tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
      (I := I) (M := M) h_atlas)

/-! ## Density: the orthogonal complement of the eigenbasis span is `⊥`

The orthogonal complement of `iSup over all real μ` of the eigenspaces is
trivial by `tensorResolventEigenspaces_iSup_orthogonal_eq_bot`. The zero
eigenspace is `⊥` (under the uniform chart-Sobolev hypothesis, which
gives injectivity of `R`), so dropping it from the iSup is harmless. -/

/-- Under the uniform chart-Sobolev hypothesis, the orthogonal complement
of the supremum (over nonzero eigenvalues) of the resolvent eigenspaces
is `⊥`. -/
theorem nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    (⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)ᗮ = ⊥ := by
  suffices h_iSup_eq :
      (⨆ μ : TensorNonzeroResolventEigenvalue
                (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) =
      (⨆ μ : ℝ, tensorResolventEigenspace
                  (I := I) (M := M) g r s μ) by
    rw [h_iSup_eq]
    exact tensorResolventEigenspaces_iSup_orthogonal_eq_bot
      (I := I) (M := M) g r s h_atlas
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun μ => ?_)
    exact le_iSup
      (fun ν : ℝ =>
        tensorResolventEigenspace (I := I) (M := M) g r s ν) μ.val
  · refine iSup_le (fun ν => ?_)
    by_cases hν : ν = 0
    · rw [hν,
          tensorResolventEigenspace_zero_eq_bot
            (I := I) (M := M) g r s]
      exact bot_le
    · by_cases h_eig_bot :
          tensorResolventEigenspace (I := I) (M := M) g r s ν = ⊥
      · rw [h_eig_bot]; exact bot_le
      · -- Eigenspace is non-trivial and `ν ≠ 0`, so we package ν into
        -- the subtype directly.
        let hν_in_subtype :
            TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s :=
          ⟨ν, h_eig_bot, hν⟩
        have hval : hν_in_subtype.val = ν := rfl
        calc tensorResolventEigenspace
              (I := I) (M := M) g r s ν
            = tensorResolventEigenspace
                (I := I) (M := M) g r s hν_in_subtype.val := by rw [hval]
          _ ≤ ⨆ μ : TensorNonzeroResolventEigenvalue
                      (I := I) (M := M) g r s,
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val :=
              le_iSup
                (fun μ : TensorNonzeroResolventEigenvalue
                          (I := I) (M := M) g r s =>
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val) hν_in_subtype

/-- The orthogonal complement of the span of the eigenbasis vectors is
`⊥`. -/
theorem tensorResolventEigenbasisVec_span_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    (Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas)))ᗮ =
      ⊥ := by
  rw [span_tensorResolventEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    (I := I) (M := M) h_atlas

/-! ## The sigma-indexed eigenbasis as a `HilbertBasis` -/

/-- The sigma-indexed orthonormal Hilbert basis of `TensorL2 r s g`
consisting of eigenvectors of `R = tensorResolventL2 g r s`, indexed by
pairs `⟨μ, k⟩` with `μ` a nonzero eigenvalue and `k` an index in the
standard orthonormal basis of the corresponding (finite-dimensional)
eigenspace.

This is built via `HilbertBasis.mkOfOrthogonalEqBot` from the eigenbasis
family and the trivial-orthogonal-complement theorem. -/
noncomputable def tensorResolventHilbertEigenbasisSigma
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    HilbertBasis
      (Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)))
      ℝ (TensorL2 r s g) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (tensorResolventEigenbasisVec_orthonormal
      (I := I) (M := M) h_atlas)
    (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
      (I := I) (M := M) h_atlas)

@[simp] lemma tensorResolventHilbertEigenbasisSigma_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (i : Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas i =
      tensorResolventEigenbasisVec
        (I := I) (M := M) h_atlas i := by
  unfold tensorResolventHilbertEigenbasisSigma
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (tensorResolventEigenbasisVec_orthonormal
        (I := I) (M := M) h_atlas)
      (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
        (I := I) (M := M) h_atlas))
    i

/-! ## Sanity tests -/

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M) :
    HilbertBasis
      (Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)))
      ℝ (TensorL2 r s g) :=
  tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_atlas

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
