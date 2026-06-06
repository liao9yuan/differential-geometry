import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldEvaluationLeibniz

/-! # The operator-field evaluation by fibrewise composition and its fibre Cauchy–Schwarz

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, an *operator field* between tensor bundles is a fibrewise continuous-linear
map `φ x : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x` (equivalently a fibre of the `(r, s)`-tensor
bundle, `TensorRSSpace r s I x`, since that bundle is by definition this Hom-bundle,
`Tensor/RSTensor/Defs.lean`).  A `(0, r)`-tensor `W x : TensorRSSpace 0 r I x = Tensor0SSpace 0 I x
→L[ℝ] Tensor0SSpace r I x` is, by the same definition, a continuous-linear map, so the operator field
*acts* on the `(0, r)`-tensor by **fibrewise composition**

```
(φ ∘ W) x := (φ x).comp (W x) : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x = TensorRSSpace 0 s I x,
```

a `(0, s)`-tensor.  This file records the intrinsic-fibre-norm Cauchy–Schwarz bound for that evaluation
(`riemannianFiberNormSq_appCLM_le`): the squared Riemannian fibre norm of `(φ x).comp (W x)` is
controlled by a nonnegative fibre-operator constant times the squared fibre norm of `W x`.

This is the value-level layer of the operator-field covariant calculus — the evaluation pairing through
which an `(r, s)`-operator-field section acts on a `(0, r)`-tensor section, with the per-point fibre
bound that converts a fibrewise operator into a section-proportional fibre bound.  It is the
composition-evaluation companion of the order-`0` fingerprint Cauchy–Schwarz
`riemannianFiberNormSq_clm_apply_le` (`OperatorFieldEvaluationLeibniz`), which it reuses verbatim: the
application operator `W x ↦ (φ x).comp (W x)` is itself a continuous-linear map
`TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x`, so the fibrewise Cauchy–Schwarz applies to it
directly.

## The diamond management

The application operator `W ↦ φ.comp W` is built through the bare linear map (composition is
`ℝ`-bilinear) closed to a continuous-linear map on the finite-dimensional `(0, r)`-fibre via
`LinearMap.toContinuousLinearMap`.  As in `riemannianFiberNormSq_clm_apply_le`, the ambient
model-induced fibre norm `tensorRSSpace_normedAddCommGroup` / `tensorRSSpace_normedSpace` is removed
(`attribute [-instance]`) and the `(0, r)`/`(0, s)`-tensor Riemannian bundle instances
`tensorRS_riemannianBundle g 0 r` / `tensorRS_riemannianBundle g 0 s` are installed inside the proof, so
the finite-dimensional structure and the operator norm resolve through the Riemannian fibre norms (which
are the intrinsic `riemannianFiberNormSq`, by the proven bridge `riemannianFiberNormSq_eq_bundle_norm_sq`
used inside `riemannianFiberNormSq_clm_apply_le`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise Cauchy–Schwarz for the operator-field evaluation.** For a fibrewise operator
`φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x` at a point `x` (a fibre of the `(r, s)`-tensor
bundle), the intrinsic squared Riemannian fibre norm of the evaluation `(φ).comp (W)` on a `(0,
r)`-tensor `W` is controlled by a nonnegative fibre-operator constant `Cφ` times the intrinsic squared
fibre norm of `W`:
```
rfns((φ).comp W) ≤ Cφ · rfns(W).
```

**Proof.** Install the source- and target-fibre `(0, r)`/`(0, s)`-tensor Riemannian bundle instances.
The application operator `W ↦ φ.comp W` is `ℝ`-linear (continuous-linear composition is `ℝ`-bilinear)
and closes to a continuous-linear map `appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x` on the
finite-dimensional `(0, r)`-fibre (`LinearMap.toContinuousLinearMap`).  The order-`0` fingerprint
Cauchy–Schwarz `riemannianFiberNormSq_clm_apply_le` applied to `appOp` gives the bound with `Cφ` the
squared `g`-fibre operator norm of `appOp`; its value on `W` is `φ.comp W` by definition.

**Trap screen.** Reads only the *value* `W` (no jet); a single fibrewise operator `φ` at one point `x`
(no free `(p, r)` family); the witness `Cφ` genuinely uses `φ` (it is the operator norm of the
composition map, nonzero whenever `φ ≠ 0` and the composition is nonzero); no free binders escape `x`. -/
theorem riemannianFiberNormSq_appCLM_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ W : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x W := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  let appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun W => (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))
        map_add' := fun W₁ W₂ => ContinuousLinearMap.comp_add φ _ _
        map_smul' := fun c W => ContinuousLinearMap.comp_smul φ c _ }
  obtain ⟨Cφ, hCφ_nn, hCφ⟩ :=
    riemannianFiberNormSq_clm_apply_le (I := I) (M := M) g r s x appOp
  refine ⟨Cφ, hCφ_nn, fun W => ?_⟩
  have happ : appOp W = (show TensorRSSpace 0 s I x from
      φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) := rfl
  rw [← happ]
  exact hCφ W

end Connection
end Integral
end DifferentialGeometry

end
