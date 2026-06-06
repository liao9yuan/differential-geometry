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

## The section-level operator-field action

This file also packages the *section-level* operator-field action `appCc g r s Φ W`, a smooth
compactly-supported `(0, s)`-tensor whose fibre value is the fibrewise composition `(Φ x).comp (W x)`
(`appCcFib`):

* `appCcFib` / `appCc` — the operator-field action of an `(r, s)`-tensor field `Φ` on a `(0, r)`-tensor
  `W`, fibrewise and as a smooth section;
* `appCcFib_contMDiff` — base-point smoothness of the action fibre field, via the pointwise-smoothness
  bridge `contMDiff_clm_section_of_pointwise` over two `ContMDiff.clm_bundle_apply` evaluations;
* `appCc_toSection` — the definitional fibre-value formula `(appCc Φ W) x = (Φ x).comp (W x)`.

This is the typed action object through which the operator-field covariant calculus expresses
`(r, s)`-operator fields acting on `(0, r)`-tensors at the section level (the carrier on which the
operator-field covariant product rule and the differentiated-curvature operator-field induction are
built).

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

set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise operator-field action value.** The fibre value at `x` of the action of an
`(r, s)`-operator field `Φ` on a `(0, r)`-tensor `W`: the fibrewise composition
`(Φ x).comp (W x) : Tensor0SSpace 0 I x →L Tensor0SSpace s I x = TensorRSSpace 0 s I x`, a
`(0, s)`-tensor. -/
def appCcFib (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    TensorRSSpace 0 s I x :=
  (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the operator-field action fibre field.** The `(0, s)`-tensor fibre
field `x ↦ appCcFib g r s Φ W x = (Φ x).comp (W x)` is a smooth section: pointwise on any smooth
`(0, 0)`-tensor `Y`, its value `Φ x (W x (Y x))` is smooth by two applications of
`ContMDiff.clm_bundle_apply` (the smoothness of `Φ` and `W` applied through the bundle
evaluation), and `contMDiff_clm_section_of_pointwise` lifts that per-vector smoothness to the
operator-valued section. -/
theorem appCcFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (appCcFib (I := I) (M := M) g r s Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => appCcFib (I := I) (M := M) g r s Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      (appCcFib (I := I) (M := M) g r s Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

set_option backward.isDefEq.respectTransparency false in
/-- **The operator-field action of an `(r, s)`-tensor field on a `(0, r)`-tensor**, as a smooth
compactly-supported `(0, s)`-tensor. The fibre value at `x` is the fibrewise composition
`(Φ x).comp (W x)` (`appCcFib`), smooth by `appCcFib_contMDiff`; on the closed manifold it has
compact support. This is the typed operator-field action through which an `(r, s)`-operator-field
section acts on a `(0, r)`-tensor section, the section-level companion of the composition
evaluation `riemannianFiberNormSq_appCLM_le`. -/
def appCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => appCcFib (I := I) (M := M) g r s Φ W x
      contMDiff_toFun := appCcFib_contMDiff (I := I) (M := M) g r s Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `appCc g r s Φ W` at `x` is the fibrewise composition
`(Φ x).comp (W x)`. Definitional. -/
@[simp] lemma appCc_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    (appCc (I := I) (M := M) g r s Φ W).toSection x =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) := rfl

end Connection
end Integral
end DifferentialGeometry

end
