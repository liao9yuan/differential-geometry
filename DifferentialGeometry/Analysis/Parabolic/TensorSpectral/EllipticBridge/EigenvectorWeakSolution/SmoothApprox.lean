import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EigenBasis
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.CanonicalTensorRepr

/-!
# Smooth `H¹`-approximation of a connection-Laplacian eigenvector

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix a nonzero
resolvent eigenvalue `μ` and an eigenvector `φ := tensorResolventEigenbasisVec`
of the `L²`-side tensor resolvent `R = tensorResolventL2 g r s`. The eigenvector
`φ` is an abstract element of the `L²` Hilbert space `TensorL2 r s g`; the
elliptic-regularity argument that promotes it to a `C^∞` section needs `φ` to be
realised as the `L²`-coercion of an `H¹` element, approximated in `H¹` norm by
genuine smooth compactly-supported tensor sections.

This file assembles exactly that setup.

* `eigenvectorResolvent g r s h_atlas i` is the `H¹`-completion element
  `tensorResolvent g r s φ`. Because `φ` lies in the resolvent eigenspace at the
  nonzero eigenvalue `μ`, the membership equation `R φ = μ • φ` rearranges to

  ```
  φ = μ⁻¹ • TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i),
  ```

  i.e. `φ` itself is `μ⁻¹` times the `L²`-coercion of an `H¹` element.

* The canonical Euclidean chart components of `φ` are accordingly `μ⁻¹` times
  the chart components of that `L²`-coercion.

* The `H¹`-completion element `eigenvectorResolvent g r s h_atlas i` is the
  limit, in `TensorH1Compl g r s`, of a sequence of (coercions of) smooth
  compactly-supported `H¹` tensor sections, by density of the completion
  embedding.

* `eigenvectorResolvent g r s h_atlas i` solves the eigenvector weak equation:
  testing against any smooth compactly-supported `H¹` section `S`, its `H¹`
  pairing with `S` equals the `L²` pairing of the underlying smooth `L²` section
  with the eigenvector `φ`. This is the variational identity defining the
  resolvent.

* For a fixed smooth test section `S`, the Dirichlet (covariant-gradient)
  pairing of the approximating sequence against `S` converges. This is extracted
  from convergence of the full `H¹` pairing — continuity of the inner product —
  by subtracting the `L²` part, which converges by continuity of the `H¹`-to-`L²`
  inclusion.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
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

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The eigenbasis-vector sigma index

The eigenbasis of the `L²`-side tensor resolvent is indexed by pairs `⟨μ, k⟩`
with `μ` a nonzero eigenvalue and `k` an index in the standard orthonormal basis
of the (finite-dimensional) eigenspace at `μ`. We abbreviate this index type. -/

/-- The sigma-index type of the resolvent eigenbasis: a nonzero eigenvalue `μ`
paired with an index `k` into the standard orthonormal basis of the eigenspace
at `μ`. -/
abbrev TensorEigenIdx
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  Σ μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s,
    Fin (Module.finrank ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val))

/-! ## The eigenvector resolvent

For an eigenbasis index `i`, the eigenvector `tensorResolventEigenbasisVec` lies
in `TensorL2 r s g`; applying the `H¹`-completion-valued resolvent
`tensorResolvent g r s` to it produces an element of `TensorH1Compl g r s`. -/

/-- The `H¹`-completion element obtained by applying the resolvent
`tensorResolvent g r s` to the eigenbasis vector at index `i`.

Since `tensorResolventEigenbasisVec h_atlas i` lies in the resolvent
eigenspace at the nonzero eigenvalue `μ := i.fst.val`, this `H¹` element is
related to the eigenvector by `eigenvector_eq_resolvent_smul`. -/
noncomputable def eigenvectorResolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1Compl g r s :=
  tensorResolvent (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)

/-! ## The eigenvector as a rescaled `L²`-coercion of an `H¹` element

The eigenbasis vector `φ := tensorResolventEigenbasisVec h_atlas i` satisfies
the membership equation of the resolvent eigenspace at `μ := i.fst.val`, namely
`tensorResolventL2 g r s φ = μ • φ`. Unfolding
`tensorResolventL2 = TensorH1ComplToTensorL2 ∘ tensorResolvent` and dividing by
the nonzero scalar `μ` yields `φ = μ⁻¹ • TensorH1ComplToTensorL2 (eigenvectorResolvent …)`. -/

/-- **The eigenvector is a rescaled `L²`-coercion of an `H¹` element.** The
eigenbasis vector `tensorResolventEigenbasisVec h_atlas i` equals `μ⁻¹` times
the `L²`-coercion of the `H¹`-completion element
`eigenvectorResolvent g r s h_atlas i`, where `μ := i.fst.val` is the
associated nonzero resolvent eigenvalue. -/
theorem eigenvector_eq_resolvent_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i =
      (i.fst.val)⁻¹ •
        TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) := by
  -- `φ` lies in the resolvent eigenspace at `μ := i.fst.val`.
  have h_mem :
      tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i ∈
        tensorResolventEigenspace (I := I) (M := M) g r s i.fst.val :=
    tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i
  -- Membership unfolds to `R φ = μ • φ`.
  have h_eig :
      tensorResolventL2 (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) =
        i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i :=
    (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)).mp h_mem
  -- `R φ = TensorH1ComplToTensorL2 (tensorResolvent φ) = TensorH1ComplToTensorL2
  --   (eigenvectorResolvent …)`.
  have h_eig' :
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) =
        i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i := by
    rw [eigenvectorResolvent]
    rw [← tensorResolventL2_apply (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)]
    exact h_eig
  -- `μ ≠ 0`, so we may divide.
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  -- `μ⁻¹ • (μ • φ) = φ`.
  rw [h_eig', smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]

/-! ## Chart components of the eigenvector

The canonical Euclidean chart component is `ℝ`-homogeneous in the abstract `L²`
element (`tensorL2ChartComponent_smul`). Combining this with the rescaling
identity `eigenvector_eq_resolvent_smul` expresses each chart component of the
eigenvector as `μ⁻¹` times the chart component of the `L²`-coercion of
`eigenvectorResolvent`. -/

/-- **The chart components of the eigenvector are rescaled chart components of
the resolvent.** The canonical Euclidean chart component of the eigenbasis
vector at base point `α` and component multi-index `P₀` equals `μ⁻¹` times the
chart component of the `L²`-coercion of the `H¹`-completion element
`eigenvectorResolvent g r s h_atlas i`. -/
theorem eigenvector_chartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ =
      (i.fst.val)⁻¹ •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P₀ := by
  -- Rewrite the eigenvector and pull the scalar out of the chart component.
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s h_atlas i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P₀

/-! ## Smooth `H¹`-approximation of the eigenvector resolvent

The `H¹`-completion `TensorH1Compl g r s` is the Hausdorff completion of the
pre-Hilbert space `SmoothCcTensorH1 g r s` of smooth compactly-supported `H¹`
tensor sections. The canonical embedding into the completion therefore has dense
range, so every element of `TensorH1Compl g r s` — in particular
`eigenvectorResolvent g r s h_atlas i` — is the limit of a sequence of
embedded smooth sections. -/

/-- **Smooth `H¹`-approximating sequence of the eigenvector resolvent.** There
is a sequence of smooth compactly-supported `H¹` tensor sections whose
`H¹`-completion embeddings converge, in `TensorH1Compl g r s`, to
`eigenvectorResolvent g r s h_atlas i`. -/
theorem exists_smoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ w : ℕ → SmoothCcTensorH1 g r s,
      Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) := by
  -- The completion embedding `(↑) : SmoothCcTensorH1 → TensorH1Compl` has dense
  -- range, so the target lies in the closure of its range.
  have h_dense :
      DenseRange
        ((↑) : SmoothCcTensorH1 g r s → TensorH1Compl g r s) :=
    UniformSpace.Completion.denseRange_coe
  -- Membership of the target in the closure of the range yields an approximating
  -- sequence (the ambient space is first-countable/metric).
  have h_mem_closure :
      eigenvectorResolvent (I := I) (M := M) g r s h_atlas i ∈
        closure (Set.range
          ((↑) : SmoothCcTensorH1 g r s → TensorH1Compl g r s)) :=
    h_dense (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)
  -- Extract a sequence in the range converging to the target.
  rw [mem_closure_iff_seq_limit] at h_mem_closure
  obtain ⟨x, hx_range, hx_tendsto⟩ := h_mem_closure
  -- Each `x n` is `(w n : TensorH1Compl)` for some smooth section `w n`.
  choose w hw using hx_range
  refine ⟨w, ?_⟩
  -- `smoothToTensorH1Compl g r s (w n) = (w n : TensorH1Compl) = x n`.
  have h_eq : (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n)) = x := by
    funext n
    rw [smoothToTensorH1Compl_apply]
    exact hw n
  rw [h_eq]
  exact hx_tendsto

/-! ## The eigenvector weak equation

The defining variational identity of the resolvent states that, for every test
element `v` of the `H¹` completion,
`⟨tensorResolvent g r s φ, v⟩_{H¹} = ⟨TensorH1ComplToTensorL2 v, φ⟩_{L²}`.
Specialising the test element to the completion embedding of a smooth
compactly-supported `H¹` section `S`, and using that `TensorH1ComplToTensorL2`
sends that embedding to the `L²`-coercion of the underlying smooth section,
gives the eigenvector weak equation. -/

/-- **The eigenvector weak equation.** For every smooth compactly-supported `H¹`
tensor section `S`, the `H¹` pairing of `eigenvectorResolvent g r s h_atlas i`
with the completion embedding of `S` equals the `L²` pairing of the underlying
smooth `L²` section of `S` with the eigenbasis vector. -/
theorem eigenWeakEquation
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s) :
    ⟪eigenvectorResolvent (I := I) (M := M) g r s h_atlas i,
        (smoothToTensorH1Compl (I := I) (M := M) g r s S)⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i⟫_ℝ := by
  -- The defining variational identity of the resolvent.
  have h_var := tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
    (smoothToTensorH1Compl (I := I) (M := M) g r s S)
  -- `tensorResolvent g r s φ = eigenvectorResolvent g r s h_atlas i`.
  rw [← eigenvectorResolvent] at h_var
  -- `TensorH1ComplToTensorL2 (smoothToTensorH1Compl S) = (S.toCcTensor : TensorL2)`.
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (I := I) (M := M) g r s S] at h_var
  exact h_var

/-! ## The `H¹` pairing of the approximating sequence

The completion embedding preserves the inner product: the `H¹` pairing of two
embedded smooth sections equals the pre-Hilbert `H¹` inner product of the
underlying sections, which decomposes (`tensorH1Inner_def`) as the `L²` pairing
plus the integrated covariant-gradient pairing. -/

/-- The `H¹` pairing of two completion-embedded smooth `H¹` sections equals the
pre-Hilbert `H¹` inner product of the underlying sections. -/
private lemma inner_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensorH1 g r s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g r s S,
        smoothToTensorH1Compl (I := I) (M := M) g r s T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := by
  rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply]
  -- `⟪(S : Completion), (T : Completion)⟫ = ⟪S, T⟫` by `inner_coe`.
  rw [UniformSpace.Completion.inner_coe]
  -- The pre-Hilbert `H¹` inner product unfolds to `tensorH1Inner`.
  exact SmoothCcTensorH1.inner_def S T

/-- The `H¹` pairing of two completion-embedded smooth `H¹` sections is the `L²`
pairing of the underlying smooth `L²` sections plus the integrated
covariant-gradient pairing. -/
private lemma inner_smoothToTensorH1Compl_eq_l2_add_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensorH1 g r s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g r s S,
        smoothToTensorH1Compl (I := I) (M := M) g r s T⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
          (T.toCcTensor : TensorL2 r s g)⟫_ℝ +
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            S.toCcTensor T.toCcTensor x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [inner_smoothToTensorH1Compl (I := I) (M := M) g r s S T,
    tensorH1Inner_def]
  -- The `L²` part: `tensorL2Inner g r s S.toFun T.toFun
  --   = ⟪(S.toCcTensor : TensorL2), (T.toCcTensor : TensorL2)⟫` by `inner_coe`
  --   and `SmoothCcTensor.inner_def`.
  have h_l2 :
      tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun T.toCcTensor.toFun =
        ⟪(S.toCcTensor : TensorL2 r s g),
          (T.toCcTensor : TensorL2 r s g)⟫_ℝ := by
    rw [UniformSpace.Completion.inner_coe]
    exact (SmoothCcTensor.inner_def S.toCcTensor T.toCcTensor).symm
  rw [h_l2]

/-! ## Convergence of the Dirichlet pairing of the approximating sequence

For a fixed smooth test section `S`, write `w_n` for an `H¹`-approximating
sequence of `eigenvectorResolvent g r s h_atlas i`. The full `H¹` pairing
`⟨smoothToTensorH1Compl (w_n), smoothToTensorH1Compl S⟩` converges to
`⟨eigenvectorResolvent …, smoothToTensorH1Compl S⟩` by continuity of the inner
product. The `L²` part `⟨(w_n).toCcTensor, S.toCcTensor⟩_{L²}` converges to
`⟨TensorH1ComplToTensorL2 (eigenvectorResolvent …), S.toCcTensor⟩_{L²}` by
continuity of the `H¹`-to-`L²` inclusion. Since the `H¹` pairing is the `L²`
part plus the Dirichlet pairing, the Dirichlet pairing is their difference and
hence converges to the difference of the two limits. -/

/-- The full `H¹` pairing of the approximating sequence converges to the `H¹`
pairing of the eigenvector resolvent with the test section. -/
private lemma smoothApprox_h1_pairing_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s)
    {w : ℕ → SmoothCcTensorH1 g r s}
    (hw : Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))) :
    Filter.Tendsto
      (fun n => ⟪smoothToTensorH1Compl (I := I) (M := M) g r s (w n),
          smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ)
      atTop
      (𝓝 (⟪eigenvectorResolvent (I := I) (M := M) g r s h_atlas i,
          smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ)) := by
  -- The inner product against the fixed second argument is continuous.
  have h_cont :
      Continuous (fun u : TensorH1Compl g r s =>
        ⟪u, smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ) :=
    (innerSL ℝ).continuous₂.comp
      (continuous_id.prodMk continuous_const)
  exact (h_cont.tendsto _).comp hw

/-- The `L²` pairing of the approximating sequence converges to the `L²` pairing
of the `L²`-coercion of the eigenvector resolvent with the test section. -/
private lemma smoothApprox_l2_pairing_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s)
    {w : ℕ → SmoothCcTensorH1 g r s}
    (hw : Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))) :
    Filter.Tendsto
      (fun n => ⟪((w n).toCcTensor : TensorL2 r s g),
          (S.toCcTensor : TensorL2 r s g)⟫_ℝ)
      atTop
      (𝓝 (⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i),
          (S.toCcTensor : TensorL2 r s g)⟫_ℝ)) := by
  -- `⟪(w n).toCcTensor, S.toCcTensor⟫ = ⟪TensorH1ComplToTensorL2
  --   (smoothToTensorH1Compl (w n)), S.toCcTensor⟫`.
  have h_rewrite :
      (fun n => ⟪((w n).toCcTensor : TensorL2 r s g),
          (S.toCcTensor : TensorL2 r s g)⟫_ℝ) =
        fun n => ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (smoothToTensorH1Compl (I := I) (M := M) g r s (w n)),
            (S.toCcTensor : TensorL2 r s g)⟫_ℝ := by
    funext n
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s (w n)]
  rw [h_rewrite]
  -- `u ↦ ⟪TensorH1ComplToTensorL2 u, S.toCcTensor⟫` is continuous.
  have h_cont :
      Continuous (fun u : TensorH1Compl g r s =>
        ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s u,
          (S.toCcTensor : TensorL2 r s g)⟫_ℝ) := by
    have h_cont_inner :
        Continuous (fun v : TensorL2 r s g =>
          ⟪v, (S.toCcTensor : TensorL2 r s g)⟫_ℝ) :=
      (innerSL ℝ).continuous₂.comp
        (continuous_id.prodMk continuous_const)
    exact h_cont_inner.comp
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous
  exact (h_cont.tendsto _).comp hw

/-- **Convergence of the Dirichlet pairing of the approximating sequence.** For
a fixed smooth compactly-supported `H¹` test section `S` and an
`H¹`-approximating sequence `w` of `eigenvectorResolvent g r s h_atlas i`, the
integrated covariant-gradient (Dirichlet) pairing of `w n` against `S` converges,
as `n → ∞`, to

```
⟨eigenvectorResolvent …, smoothToTensorH1Compl S⟩_{H¹}
  - ⟨TensorH1ComplToTensorL2 (eigenvectorResolvent …), S.toCcTensor⟩_{L²}.
```

Both terms of this limit are explicit: the first is the `H¹` pairing of the
eigenvector resolvent with the test section (which, by `eigenWeakEquation`,
equals the `L²` pairing of `S.toCcTensor` with the eigenvector), and the second
is the `L²` pairing of the `L²`-coercion of the eigenvector resolvent with
`S.toCcTensor`. -/
theorem smoothApprox_dirichlet_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s)
    {w : ℕ → SmoothCcTensorH1 g r s}
    (hw : Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s (w n))
        atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (w n).toCcTensor S.toCcTensor x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪eigenvectorResolvent (I := I) (M := M) g r s h_atlas i,
              smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ -
            ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i),
              (S.toCcTensor : TensorL2 r s g)⟫_ℝ)) := by
  -- The Dirichlet integral is the full `H¹` pairing minus the `L²` pairing.
  have h_dirichlet_eq :
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (w n).toCcTensor S.toCcTensor x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        fun n => ⟪smoothToTensorH1Compl (I := I) (M := M) g r s (w n),
              smoothToTensorH1Compl (I := I) (M := M) g r s S⟫_ℝ -
            ⟪((w n).toCcTensor : TensorL2 r s g),
              (S.toCcTensor : TensorL2 r s g)⟫_ℝ := by
    funext n
    have h_decomp := inner_smoothToTensorH1Compl_eq_l2_add_dirichlet
      (I := I) (M := M) g r s (w n) S
    -- `H¹ = L² + Dirichlet`, so `Dirichlet = H¹ - L²`.
    linarith [h_decomp]
  rw [h_dirichlet_eq]
  -- The difference of the two convergent pairings.
  exact (smoothApprox_h1_pairing_tendsto (I := I) (M := M) g r s h_atlas i S hw).sub
    (smoothApprox_l2_pairing_tendsto (I := I) (M := M) g r s h_atlas i S hw)

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1Compl g r s :=
  eigenvectorResolvent (I := I) (M := M) g r s h_atlas i

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
