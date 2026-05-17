import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox

/-!
# The canonical chart component of an eigenvector as an `L²`-limit of smooth ones

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix an eigenbasis
index `i : TensorEigenIdx g r s` with nonzero resolvent eigenvalue
`μ := i.fst.val`. The eigenvector `φ := tensorResolventEigenbasisVec h_atlas i`
is an abstract element of the `L²` Hilbert space `TensorL2 r s g`. Its canonical
Euclidean chart component `tensorL2ChartComponent g r s φ α P₀` is an
`L²`-continuous, partition-of-unity-weighted bridge with no concrete tensor
section behind it.

The chart-local elliptic-regularity argument that promotes `φ` to a `C^∞`
section must realise this abstract chart component **concretely** — as the
`L²`-limit of the chart components of genuine smooth sections. This file does
exactly that.

## The construction

`SmoothApprox.lean` produces, via `exists_smoothApprox`, a sequence of smooth
compactly-supported `H¹` tensor sections whose `H¹`-completion embeddings
converge to the eigenvector resolvent `eigenvectorResolvent g r s h_atlas i`.
The two downstream files of this campaign — the weak-partials file and the
data-structure-assembly file — both run `n → ∞` limits over **the same**
approximating sequence, so the sequence is not hidden existentially: it is
canonicalised here as

* `eigenvectorSmoothApprox g r s h_atlas i : ℕ → SmoothCcTensorH1 g r s`,

a `Classical.choose` of `exists_smoothApprox`, with spec lemma
`eigenvectorSmoothApprox_tendsto`.

## The proof chain

Threading the chosen sequence `w := eigenvectorSmoothApprox g r s h_atlas i`
through the chain:

1. `TensorH1ComplToTensorL2` is continuous; applied to the `H¹`-convergence it
   gives `TensorH1ComplToTensorL2 (smoothToTensorH1Compl (w n)) →
   TensorH1ComplToTensorL2 (eigenvectorResolvent …)` in `TensorL2 r s g`.
2. `TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe` rewrites the `n`-th
   term to `((w n).toCcTensor : TensorL2 r s g)`.
3. `eigenvector_eq_resolvent_smul` rearranges (using `μ ≠ 0`) to
   `TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`.
4. So `((w n).toCcTensor : TensorL2 r s g) → μ • φ`; scaling by the continuous
   `μ⁻¹ • ·` gives `μ⁻¹ • ((w n).toCcTensor : TensorL2 r s g) → φ`.
5. `tensorL2ChartComponentCLM g r s α P₀` is a continuous linear map
   `TensorL2 r s g →L[ℝ] Lp ℝ 2 (chartL2Measure α)`; applying it yields the
   headline `L²`-convergence.
6. `tensorL2ChartComponent_smul` pulls `μ⁻¹` out of the `n`-th term, and
   `tensorL2ChartComponent_smoothToTensorL2_eq` / `…_coeFn` identify
   `tensorL2ChartComponent g r s ((w n).toCcTensor : TensorL2 r s g) α P₀` with
   the concrete Euclidean chart component
   `tensorChartComponent g r s (w n).toCcTensor α P₀.1 P₀.2`.

## Main definitions

* `eigenvectorSmoothApprox g r s h_atlas i` — the canonical smooth
  `H¹`-approximating sequence of the eigenvector resolvent.

## Main results

* `eigenvectorSmoothApprox_tendsto` — its `H¹`-completion embeddings converge to
  `eigenvectorResolvent g r s h_atlas i`.
* `eigenvectorChartComponentL2_approx_eq` — the `n`-th approximant's canonical
  chart component is `μ⁻¹` times the `L²` class of the concrete Euclidean chart
  component of the smooth section `(w n).toCcTensor`.
* `eigenvectorChartComponentL2_tendsto` — **the headline**: those approximant
  chart components converge, in `Lp ℝ 2 (chartL2Measure α)`, to the canonical
  chart component `tensorL2ChartComponent g r s φ α P₀` of the eigenvector.

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

/-! ## The canonical smooth `H¹`-approximating sequence of the eigenvector

The two downstream files of this campaign — the eigenvector weak-partials file
and the data-structure-assembly file — each take an `n → ∞` limit over a smooth
`H¹`-approximating sequence of the eigenvector resolvent, and the limits must be
taken over **one and the same** sequence. We therefore fix a canonical choice
once, here, via `Classical.choose` applied to `exists_smoothApprox`. -/

/-- **The canonical smooth `H¹`-approximating sequence of the eigenvector
resolvent.** A `Classical.choose`-fixed sequence of smooth compactly-supported
`H¹` tensor sections whose `H¹`-completion embeddings converge, in
`TensorH1Compl g r s`, to `eigenvectorResolvent g r s h_atlas i`.

Fixing the sequence here — rather than re-extracting it per file — guarantees
that the weak partials and the variational identity of the downstream
elliptic-regularity argument are limits over the same approximants. -/
noncomputable def eigenvectorSmoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℕ → SmoothCcTensorH1 g r s :=
  Classical.choose (exists_smoothApprox (I := I) (M := M) g r s h_atlas i)

/-- **Spec of the canonical smooth `H¹`-approximating sequence.** The
`H¹`-completion embeddings of `eigenvectorSmoothApprox g r s h_atlas i`
converge, in `TensorH1Compl g r s`, to the eigenvector resolvent
`eigenvectorResolvent g r s h_atlas i`. -/
theorem eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))
      atTop
      (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) :=
  Classical.choose_spec (exists_smoothApprox (I := I) (M := M) g r s h_atlas i)

/-! ## The `L²`-coercion of the eigenvector resolvent equals `μ • φ`

The eigenvector `φ := tensorResolventEigenbasisVec h_atlas i` satisfies, by
`eigenvector_eq_resolvent_smul`, the identity
`φ = μ⁻¹ • TensorH1ComplToTensorL2 (eigenvectorResolvent …)` where
`μ := i.fst.val` is the associated nonzero resolvent eigenvalue. Multiplying by
`μ` and cancelling rearranges this to express the `L²`-coercion of the
eigenvector resolvent directly as `μ • φ`. -/

/-- The `L²`-coercion of the eigenvector resolvent is `μ • φ`, where
`μ := i.fst.val` is the associated nonzero resolvent eigenvalue and
`φ := tensorResolventEigenbasisVec h_atlas i` is the eigenvector. This is the
rearrangement of `eigenvector_eq_resolvent_smul` obtained by multiplying through
by the nonzero scalar `μ`. -/
private lemma resolventL2_eq_smul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i := by
  -- `φ = μ⁻¹ • TensorH1ComplToTensorL2 (eigenvectorResolvent …)`.
  have h_eq := eigenvector_eq_resolvent_smul (I := I) (M := M) g r s h_atlas i
  -- `μ ≠ 0`, so `μ • φ = μ • (μ⁻¹ • (…)) = (…)`.
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

/-! ## The rescaled `L²`-coercion of the approximating sequence

The `n`-th approximant is the smooth compactly-supported `H¹` section
`w n := eigenvectorSmoothApprox g r s h_atlas i n`. Composing the spec lemma
`eigenvectorSmoothApprox_tendsto` with the continuous map
`TensorH1ComplToTensorL2` and rewriting the `n`-th term by
`TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe` shows that the `L²`
coercions of the underlying smooth `L²` sections `(w n).toCcTensor` converge to
the `L²`-coercion of the eigenvector resolvent, namely `μ • φ`. Rescaling by the
continuous map `μ⁻¹ • ·` makes them converge to the eigenvector `φ` itself. -/

/-- The `L²`-coercions of the underlying smooth `L²` sections of the canonical
approximating sequence converge, in `TensorL2 r s g`, to `μ • φ`, where
`μ := i.fst.val` and `φ := tensorResolventEigenbasisVec h_atlas i`. -/
private lemma smoothApprox_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)) := by
  -- Apply the continuous map `TensorH1ComplToTensorL2` to the `H¹`-convergence.
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)))
        atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s h_atlas i)
  -- Rewrite the `n`-th term and the limit.
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s h_atlas i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n)
  rw [h_term, resolventL2_eq_smul_eigenvector (I := I) (M := M)
    g r s h_atlas i] at h_l2
  exact h_l2

/-- The `μ⁻¹`-rescaled `L²`-coercions of the underlying smooth `L²` sections of
the canonical approximating sequence converge, in `TensorL2 r s g`, to the
eigenvector `φ := tensorResolventEigenbasisVec h_atlas i`. -/
private lemma smoothApprox_smul_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)) := by
  -- Scalar multiplication by `μ⁻¹` is continuous.
  have h_smul :=
    (smoothApprox_coe_tendsto (I := I) (M := M) g r s h_atlas i).const_smul
      (i.fst.val)⁻¹
  -- `μ⁻¹ • (μ • φ) = φ`.
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

/-! ## The concrete characterisation of the approximant chart component

For each `n`, the canonical chart component of the `μ⁻¹`-rescaled `L²`-coercion
of the smooth section `(w n).toCcTensor` is, by `tensorL2ChartComponent_smul`
and the smooth-section compatibility `tensorL2ChartComponent_smoothToTensorL2_eq`,
exactly `μ⁻¹` times the `L²` class of the concrete Euclidean chart component
`tensorChartComponent g r s (w n).toCcTensor α P₀.1 P₀.2`. This is the explicit
description of each term of the headline `L²`-convergence, and the form the
downstream chart-local analysis consumes. -/

/-- **The concrete characterisation of the approximant chart component.** For
each `n`, the canonical Euclidean chart component of the `μ⁻¹`-rescaled
`L²`-coercion of the smooth section
`(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor` equals `μ⁻¹` times
the `L²` class of the concrete Euclidean chart component
`tensorChartComponent g r s (eigenvectorSmoothApprox … n).toCcTensor α P₀.1 P₀.2`,
where `μ := i.fst.val` is the associated nonzero resolvent eigenvalue. -/
theorem eigenvectorChartComponentL2_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        (tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P₀.1 P₀.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor α P₀.1 P₀.2) := by
  -- Pull the scalar `μ⁻¹` out of the canonical chart component.
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s h_atlas i n).toCcTensor) : TensorL2 r s g) α P₀]
  -- Identify the chart component of the smooth `L²` section.
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    α P₀]

/-- On the canonical chart target, the canonical Euclidean chart component of
the `n`-th `μ⁻¹`-rescaled approximant agrees, almost everywhere with respect to
`chartL2Measure α`, with `μ⁻¹` times the concrete Euclidean chart component
`tensorChartComponent g r s (eigenvectorSmoothApprox … n).toCcTensor α P₀.1 P₀.2`. -/
theorem eigenvectorChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s h_atlas i n).toCcTensor α P₀.1 P₀.2 y := by
  -- Pull the scalar out of the canonical chart component, then pass to `coeFn`.
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s h_atlas i n).toCcTensor) : TensorL2 r s g) α P₀]
  -- `coeFn` of a scalar multiple is the scalar multiple of `coeFn`.
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s h_atlas i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  -- The unscaled canonical chart component agrees a.e. with the concrete one.
  exact (tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

/-! ## The headline `L²`-convergence

Applying the continuous linear map `tensorL2ChartComponentCLM g r s α P₀` to the
`L²`-convergence `μ⁻¹ • ((w n).toCcTensor : TensorL2 r s g) → φ` of
`smoothApprox_smul_coe_tendsto` produces the headline: the canonical chart
components of the `μ⁻¹`-rescaled smooth approximants converge, in
`Lp ℝ 2 (chartL2Measure α)`, to the canonical chart component of the
eigenvector. -/

/-- **The canonical chart component of an eigenvector as an `L²`-limit of smooth
chart components.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart
center `α : M`, and a component multi-index `P₀`, the canonical Euclidean chart
components of the `μ⁻¹`-rescaled smooth approximants
`eigenvectorSmoothApprox g r s h_atlas i n` converge, as `n → ∞` and in
`Lp ℝ 2 (chartL2Measure α)`, to the canonical Euclidean chart component
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α P₀`
of the eigenvector.

The `n`-th term is identified concretely by
`eigenvectorChartComponentL2_approx_eq`: it is `μ⁻¹` times the `L²` class of the
concrete Euclidean chart component
`tensorChartComponent g r s (eigenvectorSmoothApprox … n).toCcTensor α P₀.1 P₀.2`
of the smooth section `(eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor`. -/
theorem eigenvectorChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀)) := by
  -- Apply the continuous linear chart-component map to the `L²`-convergence.
  have h_clm :=
    ((tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous.tendsto
      _).comp
      (smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s h_atlas i)
  -- Unfold the composition and rewrite `tensorL2ChartComponentCLM _ u` as
  -- `tensorL2ChartComponent _ u`, at the `n`-th term and at the limit.
  simp only [Function.comp_def, tensorL2ChartComponentCLM_apply] at h_clm
  exact h_clm

/-! ## Sanity tests -/

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℕ → SmoothCcTensorH1 g r s :=
  eigenvectorSmoothApprox (I := I) (M := M) g r s h_atlas i

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s h_atlas i n).toCcTensor) : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀)) :=
  eigenvectorChartComponentL2_tendsto (I := I) (M := M) g r s h_atlas i α P₀

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
