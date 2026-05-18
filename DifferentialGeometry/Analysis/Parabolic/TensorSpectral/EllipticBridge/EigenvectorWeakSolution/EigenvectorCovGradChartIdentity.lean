import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartTestDecoupling

/-!
# The raw chart-component formula for the section-level covariant gradient

For a closed Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, ranks `(r, s)`, and a smooth compactly-supported `(r, s)`-tensor section
`S`, the section-level covariant gradient `covGrad g r s S` is a smooth
compactly-supported `(r, s + 1)`-tensor section: the extra covariant slot is the
slot carrying the differentiation direction.

This file proves the **raw chart-component formula** for `covGrad`: the raw
chart-frame `(r, s + 1)`-component of `covGrad g r s S`, read at the
chart-source preimage of a Euclidean-chart-target point `y`, equals a
chart-Euclidean partial derivative of the raw `(r, s)`-component of `S` plus a
zeroth-order Christoffel correction. Concretely, writing
`m := Jdx 0` for the leftmost covariant index of the target multi-index `Jdx`
and `Jdx' := Matrix.vecTail Jdx` for the remaining `Fin s`-tuple,

`tensorChartComponentRaw g r (s + 1) (covGrad g r s S) α Idx Jdx b
  = euclidPartial m (chartPushedRaw I α (tensorChartComponentRaw g r s S α Idx Jdx')) y
    + covDerivLowerOrderTerm g r s S α m Idx Jdx' y`,

with `b := (extChartAt I α).symm (toEuclidean.symm y)`.

## Proof route

The underlying section value of `covGrad g r s S` at `b` is, by
`covGrad_toSection_apply`, the image under the covariant-gradient bundle
equivalence `covGradBundleEquiv r s b` of the bundled directional covariant
derivative `Φ := tensorRSCovariantDerivative I M r s (LeviCivita g) S.toSection b`.

Reading the raw chart-frame scalar component at rank `(r, s + 1)`, the
trivialisation-compatibility identity `covGradBundleEquiv_trivializationAt_eq`
reduces the chart-`α`-trivialised representation of the covariant-gradient
bundle equivalence to the constant model equivalence `covGradModelEquiv`, whose
leftmost-slot evaluation `covGradModelEquiv_apply` reads the direction off the
slot indexed by `Jdx 0`. The chart component therefore factors as the
`(r, s)`-component projection, at `(Idx, Matrix.vecTail Jdx)`, of the
directional covariant derivative `Φ` taken along the `(Jdx 0)`-th chart-frame
basis vector.

That directional covariant derivative is `tensorCovDerivAt g r s S b
(chartBasisVecFiber α (Jdx 0) b)`, which on the chart-`α` Levi-Civita good set
equals the chart-coordinate covariant derivative
(`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`). Its raw chart-frame
component is then the chart-Euclidean partial plus the Christoffel correction by
the chart-coordinate covariant-derivative component formula
`covDerivComponent_eq_euclidPartial_add_lowerOrder`.

This is the direct `covGrad`-analogue of `tensorChartComponentRaw_prependCovGradSlot`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Trivialisation-fibre of a covariant-gradient bundle element

On the chart source, the chart-`α`-trivialisation fibre of a covariant-gradient
bundle element `Φ` (a continuous linear map from a tangent vector to an
`(r, s)`-tensor) post-composes `Φ` (with its tangent input re-trivialised
through `triv_{TM}.symmL`) with the `(r, s)`-tensor-bundle `continuousLinearMapAt`.
This is the `Trivialization.continuousLinearMap` formula for the hom bundle,
holding definitionally. -/

/-- The chart-`α`-trivialisation fibre of a covariant-gradient bundle element
`Φ` (a continuous linear map from a tangent vector to an `(r, s)`-tensor) is the
continuous linear map post-composing `Φ` (with its tangent input re-trivialised
through `triv_{TM}.symmL`) with the `(r, s)`-tensor-bundle
`continuousLinearMapAt`. -/
private lemma covGradBundle_trivFibre_eq'
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

/-! ## The raw chart-component formula for the covariant gradient

The headline below mirrors `tensorChartComponentRaw_prependCovGradSlot`. There
the section carries `dζ` un-differentiated in its leftmost slot; here the
section is the genuine covariant gradient, so after the leftmost-slot projection
the remaining `(r, s)`-component is the directional covariant derivative of `S`
along the chart-frame basis vector — which the chart-coordinate
covariant-derivative component formula resolves into the chart-Euclidean partial
plus the Christoffel correction. -/

/-- **The raw chart-component formula for the section-level covariant
gradient.** For a smooth compactly-supported `(r, s)`-tensor section `S`, a
chart center `α`, a component multi-index `Idx : Fin r → Fin n`, a target
covariant multi-index `Jdx : Fin (s + 1) → Fin n`, and a Euclidean-chart-target
point `y`, the raw chart-frame scalar component of the section-level covariant
gradient `covGrad g r s S` at `(Idx, Jdx)`, read at the chart-source preimage
`b := (extChartAt I α).symm (toEuclidean.symm y)` of `y`, equals the
`(Jdx 0)`-th chart-Euclidean partial derivative of the Euclidean push-forward of
the raw `(r, s)`-component of `S` at `(Idx, Matrix.vecTail Jdx)`, plus the
zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx)`.

The section value of `covGrad g r s S` at `b` is, by `covGrad_toSection_apply`,
the image under the covariant-gradient bundle equivalence of the bundled
directional covariant derivative `Φ` of `S`. The trivialisation-compatibility
identity `covGradBundleEquiv_trivializationAt_eq`, together with the
leftmost-slot evaluation `covGradModelEquiv_apply`, projects the `(r, s + 1)`-
component onto the `(r, s)`-component of `Φ` taken along the `(Jdx 0)`-th
chart-frame basis vector. On the chart-`α` Levi-Civita good set that directional
covariant derivative agrees with the chart-coordinate covariant derivative
(`tensorCovDerivAt_eq_chartTensorRSCovariantDerivative`), whose raw chart-frame
component is `euclidPartial + covDerivLowerOrderTerm`
(`covDerivComponent_eq_euclidPartial_add_lowerOrder`). -/
theorem tensorChartComponentRaw_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
            (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun z : M => Tensor0SSpace r I z)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z)) := tensor0SBundle_topology (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) :=
    tensorRSBundle_vector r (s + 1)
  -- The chart-source preimage `b` of `y`.
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  -- `b` lies in the chart source.
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  -- The tangent-bundle trivialisation base set is the chart source.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  -- The `(r, s + 1)`-tensor-bundle trivialisation base set is the chart source.
  have hb_baseS1 : b ∈ (trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun z : M => TensorRSSpace r (s + 1) I z) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun z : M => Tensor0SSpace r I z) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  -- `b` lies in the chart-`α` Levi-Civita good set.
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    refine ⟨⟨?_, ?_⟩, hb_int⟩
    · rw [extChartAt_source]; exact hb_chart
    · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  -- The covariant-gradient model element: the bundled directional covariant
  -- derivative of `S` at `b`.
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun z : M => S.toSection z) b with hΦ_def
  -- The raw component is the chart-frame projection of `tensorTrivProj`.
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  -- The underlying section value of `covGrad g r s S` is `covGradBundleEquiv Φ`.
  rw [covGrad_toSection_apply (I := I) (M := M) g r s S b]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun z : M => S.toSection z) b) = Φ from rfl]
  -- `continuousLinearMapAt b X = (triv ⟨b, X⟩).2` on the base set.
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun z : M => TensorRSSpace r (s + 1) I z) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  -- The trivialisation compatibility of the covariant-gradient bundle equivalence.
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  -- The chart-frame projection evaluates on `dualCovariantCMM r Idx` and the
  -- basis tuple `chartModelBasis E ∘ Jdx`; `covGradModelEquiv` reads `Jdx 0` off
  -- the leftmost slot.
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  -- The covariant-gradient bundle trivialisation fibre of `Φ`, evaluated at the
  -- leftmost basis direction.
  rw [covGradBundle_trivFibre_eq' (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- `triv_{TM}.symmL b (chartModelBasis E (Jdx 0)) = chartBasisVecFiber α (Jdx 0) b`.
  have hsymmL : (trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((chartModelBasis E) (Jdx 0)) =
      chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  -- `Φ` along the chart-frame basis vector is the directional covariant
  -- derivative `tensorCovDerivAt g r s S b (chartBasisVecFiber α (Jdx 0) b)`.
  rw [show Φ (chartBasisVecFiber (I := I) α (Jdx 0) b) =
      tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α (Jdx 0) b) from rfl]
  -- On the chart-`α` Levi-Civita good set the directional covariant derivative
  -- equals the chart-coordinate covariant derivative.
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α (Jdx 0) hb_good]
  -- The remaining factor is the raw chart-frame `(r, s)`-component of the
  -- chart-coordinate covariant derivative with the leftmost slot removed: the
  -- chart-coordinate covariant-derivative component formula resolves it into the
  -- chart-Euclidean partial plus the Christoffel correction. The `(0, s)`-tuple
  -- `Matrix.vecTail (chartModelBasis E ∘ Jdx)` is, definitionally, the tuple
  -- `chartModelBasis E ∘ Matrix.vecTail Jdx`, so the projected factor matches
  -- the component-formula left-hand side.
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α (Jdx 0) Idx (Matrix.vecTail Jdx) hy

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
