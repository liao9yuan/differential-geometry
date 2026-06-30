import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Tensor.RSTensor.Coordinates.TensorRSModelEvalBasis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Bundle continuity of tensor families from frame components

This file supplies the *converse* of `Tensor0SFamilyContinuousOnSet.eval_continuous`:
a constructor producing the joint total-space continuity predicate
`Tensor0SFamilyContinuousOnSet` from the continuity of a tensor family's scalar
components in a local trivialization frame.

The constructor is the reusable keystone for packaging chart-coordinate
regularity into bundled tensor-section continuity (`metricTensor_cont`,
`ricciCont`, `rm04Cont`, ... of `MetricFamilySmoothOn`/`IsSolutionOn`).  It is
stated in the inner-product-space setting because the model basis
`chartModelBasis` and the evaluation equivalence `eval0SCLE` are tied to the
Euclidean structure; the realized Ricci-flow consumers all live there.
-/

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Keystone constructor: bundle continuity from frame-component continuity.**

A time-dependent `(0,s)` tensor family `A` is jointly continuous as a tensor
section over `{t ∈ K} × M` as soon as, for every base trivialization centre `x₀`,
its scalar components against the local trivialization frame
`(trivializationAt E (TangentSpace I) x₀).symmL` applied to the model basis are
jointly continuous on that trivialization's domain.

This is the converse of `Tensor0SFamilyContinuousOnSet.eval_continuous` (which
projects a continuous section to continuous components).  The proof runs through
`FiberBundle.continuousAt_totalSpace` — continuity in the total space is base
continuity plus fibre-coordinate continuity — and the finite-dimensional
evaluation homeomorphism `eval0SCLE`, which turns fibre-coordinate continuity
into the continuity of the basis components. -/
theorem tensor0SFamilyContinuousOnSet_of_chartComp
    {s : Nat} {K : Set Real}
    (A : (t : Real) → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (N : M → Set M) (hN : ∀ x₀ : M, N x₀ ∈ nhds x₀)
    (hcomp : ∀ (x₀ : M) (idx : Fin s → Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          A q.1.1 q.2
            (fun k : Fin s =>
              (trivializationAt E (TangentSpace I) x₀).symmL Real q.2
                (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))))
        {q : {t : Real // t ∈ K} × M | q.2 ∈ N x₀}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  unfold Tensor0SFamilyContinuousOnSet
  rw [continuous_iff_continuousAt]
  intro q₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_snd.continuousAt, ?_⟩
  -- Normalise the fibre-coordinate goal to the clean form centred at `q₀.2`.
  show ContinuousAt
      (fun q : {t : Real // t ∈ K} × M =>
        (trivializationAt (Tensor0SModel s Real E)
          (fun x : M => Tensor0SSpace s I x) q₀.2
            ⟨q.2, A q.1.1 q.2⟩).2) q₀
  -- The neighbourhood of `q₀` on which the component continuity is supplied.
  have hopen : {q : {t : Real // t ∈ K} × M | q.2 ∈ N q₀.2} ∈ nhds q₀ :=
    continuous_snd.continuousAt.preimage_mem_nhds (hN q₀.2)
  -- Through the evaluation homeomorphism, fibre-coordinate continuity is
  -- equivalent to the continuity of every basis component.
  have key : ContinuousAt
      (fun q : {t : Real // t ∈ K} × M =>
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
          ((trivializationAt (Tensor0SModel s Real E)
            (fun x : M => Tensor0SSpace s I x) q₀.2
              ⟨q.2, A q.1.1 q.2⟩).2)) q₀ := by
    rw [continuousAt_pi]
    intro idx
    have hpt :
        (fun q : {t : Real // t ∈ K} × M =>
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
            ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M => Tensor0SSpace s I x) q₀.2
                ⟨q.2, A q.1.1 q.2⟩).2) idx)
          = fun q : {t : Real // t ∈ K} × M =>
              A q.1.1 q.2
                (fun k : Fin s =>
                  (trivializationAt E (TangentSpace I) q₀.2).symmL Real q.2
                    (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))) := by
      funext q
      rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE_apply]
      rw [show ((trivializationAt (Tensor0SModel s Real E)
              (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)
            = (A q.1.1 q.2).compContinuousLinearMap
                (fun _ : Fin s =>
                  (trivializationAt E (TangentSpace I) q₀.2).symmL Real q.2) from rfl]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [hpt]
    exact (hcomp q₀.2 idx).continuousAt hopen
  -- Recover the fibre-coordinate continuity from the components by composing
  -- with the inverse homeomorphism.
  have hsymm :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s).symm.continuous
  have hcongr : (fun q : {t : Real // t ∈ K} × M =>
      (trivializationAt (Tensor0SModel s Real E)
        (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)
      = fun q : {t : Real // t ∈ K} × M =>
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s).symm
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eval0SCLE (E := E) s
              ((trivializationAt (Tensor0SModel s Real E)
                (fun x : M => Tensor0SSpace s I x) q₀.2 ⟨q.2, A q.1.1 q.2⟩).2)) := by
    funext q
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hcongr]
  exact hsymm.continuousAt.comp key

/-- Keystone, phrased in the canonical chart-basis frame `chartBasisVecFiber`.

This is the form curvature consumers plug into: the chart-basis frame
`chartBasisVecFiber x₀ i x = (trivializationAt E (TangentSpace I) x₀).symm x (chartModelBasis i)`
is definitionally the `symmL` frame used by `tensor0SFamilyContinuousOnSet_of_chartComp`, so
this is a thin restatement that avoids re-deriving the `symmL`/`symm` identification at every
call site (metric, Ricci, Riemann). -/
theorem tensor0SFamilyContinuousOnSet_of_chartBasisComp
    {s : Nat} {K : Set Real}
    (A : (t : Real) → (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (N : M → Set M) (hN : ∀ x₀ : M, N x₀ ∈ nhds x₀)
    (hcomp : ∀ (x₀ : M) (idx : Fin s → Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          A q.1.1 q.2
            (fun k : Fin s =>
              DifferentialGeometry.Integral.Measure.chartBasisVecFiber
                (I := I) x₀ (idx k) q.2))
        {q : {t : Real // t ∈ K} × M | q.2 ∈ N x₀}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A := by
  apply tensor0SFamilyContinuousOnSet_of_chartComp A N hN
  intro x₀ idx
  have heq :
      (fun q : {t : Real // t ∈ K} × M =>
        A q.1.1 q.2
          (fun k : Fin s =>
            (trivializationAt E (TangentSpace I) x₀).symmL Real q.2
              (DifferentialGeometry.Integral.Measure.chartModelBasis E (idx k))))
        = fun q : {t : Real // t ∈ K} × M =>
            A q.1.1 q.2
              (fun k : Fin s =>
                DifferentialGeometry.Integral.Measure.chartBasisVecFiber
                  (I := I) x₀ (idx k) q.2) := by
    funext q
    congr 1
  rw [heq]
  exact hcomp x₀ idx

/-- **First consumer of the keystone: metric bundle continuity from chart-Gram
continuity.**

For a time-dependent Riemannian metric family `g` whose chart-Gram matrix entries
are jointly continuous (in `(t, x)`) on each chart trivialization domain, the
bundled metric tensor family `(t, x) ↦ metricTensorField (g t) x` is jointly
continuous as a `(0,2)` tensor section over `{t ∈ K} × M`.

This discharges the `metricTensor_cont` field of `MetricFamilySmoothOn` from the
raw chart-Gram regularity exposed by short-time existence. -/
theorem metricTensorCont_of_chartGram
    {K : Set Real} (g : Real → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun q : {t : Real // t ∈ K} × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
            (g q.1.1) x₀ q.2 i j)
        {q : {t : Real // t ∈ K} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet}) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g t) x) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
  intro x₀ idx
  have heq :
      (fun q : {t : Real // t ∈ K} × M =>
        metricTensorField (I := I) (g q.1.1) q.2
          (fun k : Fin 2 =>
            DifferentialGeometry.Integral.Measure.chartBasisVecFiber
              (I := I) x₀ (idx k) q.2))
        = fun q : {t : Real // t ∈ K} × M =>
            DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
              (g q.1.1) x₀ q.2 (idx 0) (idx 1) := by
    funext q
    rw [metricTensorField_apply,
      DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  rw [heq]
  exact hgram x₀ (idx 0) (idx 1)

namespace Tensor0SFamilyContinuousOnSet

/-- **Pullback of bundle continuity under a diffeomorphism.**  If a time-dependent `(0,s)` tensor
family `A` on `N` is jointly continuous, then so is its `Φ`-pullback on `M`,
`(t, x) ↦ (A t (Φ x)).compContinuousLinearMap (fun _ => dΦₓ)`.

Proved through the component constructor `tensor0SFamilyContinuousOnSet_of_chartBasisComp` on `M`:
in each `M`-chart, the pullback component on a chart-basis slot is `A` evaluated at `Φ x` on the
pushed-forward slots `dΦₓ (chartBasisVecFiber …)`, whose continuity is `hA.eval_continuous` with the
pushed chart-basis section `tangentMap Φ ∘ chartBasisVec` (smooth on the chart, then `Φ.continuous_tangentMap`). -/
theorem pullback
    {s : Nat} {K : Set Real}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [IsManifold I 1 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (A : (t : Real) → (x : N) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := N) s x)
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := N) s K A)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => (A t (Φ x)).compContinuousLinearMap
        (fun _ : Fin s => mfderiv I I (Φ : M → N) x)) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp
    (N := fun x₀ => (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hN := fun x₀ => (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀))
  intro x₀ idx
  rw [continuousOn_iff_continuous_restrict]
  have hslot : ∀ k : Fin s, Continuous
      (fun p : {q : {t : Real // t ∈ K} × M //
            q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
        TotalSpace.mk' E (E := fun y : N => TangentSpace I y) (Φ p.1.2)
          (mfderiv I I (Φ : M → N) p.1.2
            (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2))) := by
    intro k
    have hcomp :
        (fun p : {q : {t : Real // t ∈ K} × M //
              q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} =>
          TotalSpace.mk' E (E := fun y : N => TangentSpace I y) (Φ p.1.2)
            (mfderiv I I (Φ : M → N) p.1.2
              (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) p.1.2)))
          = (tangentMap I I (Φ : M → N)) ∘
              (fun p => DifferentialGeometry.Integral.Measure.chartBasisVec (I := I) x₀ (idx k) p.1.2) := by
      funext p; rfl
    rw [hcomp]
    refine (Φ.contMDiff.continuous_tangentMap (by simp)).comp ?_
    exact (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn
        (I := I) x₀ (idx k)).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun p => p.2)
  have hev := hA.eval_continuous
      (P := {q : {t : Real // t ∈ K} × M //
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet})
      (τ := fun p => p.1.1.1) (b := fun p => Φ p.1.2)
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
      (fun p => p.1.1.2)
      (Φ.continuous.comp (continuous_snd.comp continuous_subtype_val))
      hslot
  refine hev.congr ?_
  intro p
  simp only [Set.restrict_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]

end Tensor0SFamilyContinuousOnSet

end DifferentialGeometry.Integral.Connection
