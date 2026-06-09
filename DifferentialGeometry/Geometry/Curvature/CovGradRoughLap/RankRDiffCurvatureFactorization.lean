import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRPureRCurvatureTower

/-!
# The full Hom-bundle operator-field action and the `(∇R)·` factorisation at valence `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
**full Hom-bundle operator-field action** `appFullRS` at a generic contravariant valence `r`, and uses
it to express the order-`1` moving-centre pure-Riemann differentiated trace `genuinePureRDiffOpRS g r 1
rr` (the genuine `(∇R) W` contraction `covGrad(R W) − R(∇W)`, `RankRPureRCurvatureTower`) as the
**value-local** action of a fixed smooth full Hom-bundle curvature-jet field.

## Why a *full* Hom action `appFullRS`, not the codomain-only `appCcRS`

At contravariant rank `0` the order-`0` moving-centre pure-Riemann curvature endomorphism factors as a
codomain-only **post-composition** `appCc Φ₀ W = Φ₀.comp W` by a fixed `(s, s)`-operator field `Φ₀`
(`exists_pureRGenuineDiffOp_base_appCc`, sorry-free at rank `0`): a `(0, s)`-tensor `W` *is* a map
`Tensor0SSpace 0 → Tensor0SSpace s`, and the curvature acts entirely on its `Tensor0SSpace s` codomain.

At a generic contravariant valence `r ≥ 1` the curvature `riemannOp (tensorCov g r rr)` acts on the
*full* `(r, rr)`-tensor — both the contravariant `(0, r)` branch and the covariant `(0, rr)` branch of the
point-level slot formula `riemannOp_tensorCovRS_apply_eval` — so the order-`0` endomorphism does **not**
post-compose: it is the genuine **full Hom-bundle** action of a fibrewise operator
`Θ x : TensorRSSpace r rr I x →L TensorRSSpace r rr I x` on the *whole* fibre `W x`.  The full Hom-bundle
action `appFullRS Θ W` (`(appFullRS Θ W).toSection x = Θ x (W.toSection x)`) is the rank-`r` carrier of
this two-sided curvature contraction, distinct from the codomain-only `appCcRS` post-composition (which
operates at the `Tensor0SSpace` level): the operator `Θ x` is a continuous-linear endomorphism of the
*full* tensor fibre `TensorRSSpace r rr I x = Tensor0SSpace r I x →L Tensor0SSpace rr I x`.

## What is proved vs. posited

* `appFullRSFib` / `appFullRS` / `appFullRS_toSection` — the full Hom-bundle operator-field action at
  valence `r` and its definitional fibre-value formula; smoothness via the same
  `contMDiff_clm_section_of_pointwise` bridge the codomain-only action uses, lifted to full tensor
  fibres.  `ℝ`-bilinearity (`appFullRS_add_right`, `appFullRS_smul_right`, `appFullRSFib_add_left`).
  **Proved.**
* `riemannianFiberNormSq_appFullRS_clm_apply_le` — the per-point fibrewise Cauchy–Schwarz
  `rfns(Ψ x v) ≤ ‖Ψ x‖² · rfns(v)` for the full Hom-bundle action, the verbatim full-fibre lift of the
  *proved* contravariant-`0` `riemannianFiberNormSq_clm_apply_le` through the public bridge
  `riemannianFiberNormSq_eq_bundle_norm_sq'`.  **Proved.**
* `genuinePureRDiffOpRS_one_local` — the value-locality of the order-`1` trace (the consumer interface the
  differentiated `(∇R)·` tower needs): its fibre value at `x` depends only on `W x`.  **Proved** over the
  `(∇R)·` factorisation child.

The two genuine analytic LEAVES (each a precise valence-`r` full-Hom statement, distinct from any *proved*
rank-`0` / codomain-only node) are:

* `exists_genuinePureRDiffOpRS_one_appFullRS` — the value-local full-Hom factorisation of the order-`1`
  trace `genuinePureRDiffOpRS g r 1 rr = appFullRS Θ` for a *fixed* smooth full-Hom curvature-jet field
  `Θ` (the curvature derivative `∇R` as a full Hom endomorphism).  Its two irreducible facts are (i) the
  value-locality / `∇W`-cancellation of the order-`1` trace and (ii) the base-point smoothness of `Θ`; both
  rest on the full-Hom covariant product rule `covGrad_appFullRS_eq` (`∇(R·W) = (∇R)·W + R·(∇W)` for the
  abstract second-order Hom-bundle `Hom(T^{r,rr}, T^{r,rr+1})`).  The precise missing prerequisite is the
  generic Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` *instantiated on that
  second-order Hom-bundle* `Hom(TensorRSSpace r rr, TensorRSSpace r (rr + 1))`, which carries **no** bundle
  instance suite (`TopologicalSpace (TotalSpace …)` / `FiberBundle` / `VectorBundle` /
  `ContMDiffVectorBundle`, nor a computable Hom-model normed structure) — unlike the *first-order*
  `Hom(Tensor0S r, Tensor0S s)` carrier `tensorRSCovariantDerivative` (whose `Tensor0S` source/target have
  the full global instance suite).  Building that second-order Hom-bundle instance tower is a multi-file
  infrastructure node (see the per-leaf docstring);
* `exists_continuous_riemannianFiberNormSq_homSection_clm_le` — the **continuous per-point** `g`-fibre-
  operator contraction envelope `rfns(Ψ x v) ≤ Cop x · rfns(v)` (`Cop : M → ℝ` continuous nonnegative) for a
  fixed smooth full Hom-bundle section `Ψ`.  This is the genuine atomic primitive: the base-point
  *continuity* of the `g`-fibre operator norm `x ↦ ‖Ψ x‖_g²` of a smooth Hom-bundle section — the full-Hom
  analogue of the *proved* continuous curvature-operator envelope
  `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`.  The abstract
  `Hom(T^{r,a}, T^{r,c})` bundle is no `SmoothCcTensor`, so the tensor-section route
  `exists_bound_riemannianFiberNormSq_smoothCcTensor` does not apply.

Over this continuous-envelope leaf, the uniform `g`-fibre-operator bound
`exists_uniform_riemannianFiberNormSq_homSection_clm_le` and hence the full-Hom contraction bound
`exists_uniform_riemannianFiberNormSq_appFullRS_le` are **proved** (compactness uniformisation of `Cop`,
then `appFullRS_toSection`).  Consumers transitively depend on these two leaves' `sorryAx`.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`.  The construction stays
intrinsic: `covGrad` covariant gradients, the full `(r, rr)`-tensor curvature carrier, and the full
Hom-bundle action only.
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
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The full Hom-bundle operator-field action at valence `r` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise full Hom-bundle operator-field action value at valence `r`.** The fibre value at `x`
of the action of a smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x`
on an `(r, a)`-tensor `W`: the fibrewise application `Ψ x (W x) : TensorRSSpace r c I x`.  Unlike the
codomain-only `appCcRSFib` (post-composition at the `Tensor0SSpace` level), `Ψ x` is a continuous-linear
endomorphism-type map of the *full* tensor fibre. -/
def appFullRSFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    TensorRSSpace r c I x :=
  Ψ x (W.toSection x)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the full Hom-bundle operator-field action fibre field at valence `r`.**
If the full Hom-bundle field `Ψ` is a smooth `Hom(T^{(r,a)}, T^{(r,c)})`-bundle section, then the
`(r, c)`-tensor fibre field `x ↦ appFullRSFib g r a c Ψ W x = Ψ x (W x)` is a smooth section, by the
single `ContMDiff.clm_bundle_apply` evaluation `(Ψ x) (W x)` against the smooth `(r, a)`-section `W`. -/
theorem appFullRSFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        (appFullRSFib (I := I) (M := M) g r a c Ψ W x)) :=
  ContMDiff.clm_bundle_apply (b := id) hΨ W.toSection.contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- **The full Hom-bundle operator-field action of a smooth Hom field on an `(r, a)`-tensor**, as a
smooth compactly-supported `(r, c)`-tensor. The fibre value at `x` is `Ψ x (W x)` (`appFullRSFib`),
smooth by `appFullRSFib_contMDiff`; on the closed manifold it has compact support. The full-tensor-fibre
lift of `appCcRS` (which post-composes at the `Tensor0SSpace` level). -/
def appFullRS (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r c where
  toSection :=
    { toFun := fun x : M => appFullRSFib (I := I) (M := M) g r a c Ψ W x
      contMDiff_toFun := appFullRSFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `appFullRS g r a c Ψ hΨ W` at `x` is `Ψ x (W x)`. Definitional. -/
@[simp] lemma appFullRS_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) :
    (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x = Ψ x (W.toSection x) := rfl

/-! ## Bilinearity of the full Hom-bundle action -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is additive in the contracted `(r, a)`-tensor. -/
theorem appFullRS_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W₁ W₂ : SmoothCcTensor g r a) :
    appFullRS (I := I) (M := M) g r a c Ψ hΨ (W₁ + W₂) =
      appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁ + appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁ +
        appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x) =
      (appFullRS (I := I) (M := M) g r a c Ψ hΨ W₁).toSection x +
        (appFullRS (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection, appFullRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [map_add (Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is `ℝ`-homogeneous in the contracted `(r, a)`-tensor. -/
theorem appFullRS_smul_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (k : ℝ) (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    appFullRS (I := I) (M := M) g r a c Ψ hΨ (k • W) =
      k • appFullRS (I := I) (M := M) g r a c Ψ hΨ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x) =
      k • (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [map_smul (Ψ x)]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The full Hom-bundle action is additive in the operator-field factor (fibre-value form). -/
theorem appFullRSFib_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ₁ Ψ₂ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    appFullRSFib (I := I) (M := M) g r a c (fun y => Ψ₁ y + Ψ₂ y) W x =
      appFullRSFib (I := I) (M := M) g r a c Ψ₁ W x +
        appFullRSFib (I := I) (M := M) g r a c Ψ₂ W x := by
  rw [appFullRSFib, appFullRSFib, appFullRSFib, ContinuousLinearMap.add_apply]

/-! ## The per-point fibrewise Cauchy–Schwarz for the full Hom-bundle action at valence `r`

The fibre value `Ψ x (W x)` of the full Hom-bundle action is a continuous-linear-map evaluation between
finite-dimensional tensor fibres; the intrinsic-fibre-norm / `g`-bundle-norm bridge
`riemannianFiberNormSq_eq_bundle_norm_sq'` turns the fibre operator-norm bound `‖φ v‖ ≤ ‖φ‖ · ‖v‖` into
the squared `rfns` bound, exactly as in the proved contravariant-`0` `riemannianFiberNormSq_clm_apply_le`,
lifted to the full `(r, a)` / `(r, c)` fibres. -/

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The per-point fibrewise Cauchy–Schwarz for the full Hom-bundle action at valence `r`.** For a
fibrewise continuous-linear operator `φ : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x` between the
*full* tensor fibres at `x`, there is a nonnegative fibre-operator constant `Cφ` (the squared `g`-fibre
operator norm of `φ`) with `rfns(φ v) ≤ Cφ · rfns(v)` for every fibre tensor `v`.  The verbatim full-fibre
lift of `riemannianFiberNormSq_clm_apply_le` (contravariant `0`), proved through the public
intrinsic-fibre-norm / `g`-bundle-norm bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`. -/
theorem riemannianFiberNormSq_appFullRS_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (φ : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace r a I x,
      riemannianFiberNormSq (I := I) (M := M) g r c x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  let φg : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
    LinearMap.toContinuousLinearMap (φ.toLinearMap)
  have hφg_apply : ∀ v, φg v = φ v := fun v => by
    change (LinearMap.toContinuousLinearMap (φ.toLinearMap)) v = φ v
    rw [LinearMap.coe_toContinuousLinearMap']; rfl
  refine ⟨‖φg‖ ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r c x (φ v),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r a x v, ← hφg_apply v]
  calc ‖φg v‖ ^ 2 ≤ (‖φg‖ * ‖v‖) ^ 2 := by
          apply sq_le_sq'
          · nlinarith [φg.le_opNorm v, norm_nonneg (φg v), norm_nonneg v, norm_nonneg φg]
          · exact φg.le_opNorm v
    _ = ‖φg‖ ^ 2 * ‖v‖ ^ 2 := by ring

/-! ## The directional and section-level covariant product rule for the full Hom-bundle action

The covariant derivative of the full Hom-bundle action `appFullRS Ψ W` (fibre value `Ψ x (W x)`) splits
— directionally and at a point — into the second-order Hom-bundle Leibniz
```
∇_v (Ψ · W) = (∇^Hom_v Ψ)(W x) + Ψ x (∇_v W),
```
an equation of `(r, c)`-tensors, where `∇^Hom Ψ = homTensorRSCovariantDerivative (LeviCivita g) Ψ`
(`SecondOrderHomBundle`) is the second-order Hom-bundle covariant derivative of `Ψ` and
`∇_v W = tensorCovDerivAt g r a W x v` is the `(r, a)`-tensor directional derivative.  This is the exact
full-fibre analogue of the codomain-only `tensorCovDerivAt_appCcRS_eq`, lifted from the post-composition
to the genuine full Hom-bundle action through the second-order Hom-bundle covariant derivative built in
`SecondOrderHomBundle`. -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The directional covariant product rule for the full Hom-bundle action.** For a smooth full
Hom-bundle field `Ψ` (smoothness witnessed by `hΨ`) and a smooth `(r, a)`-tensor `W`, the directional
covariant derivative of the full Hom-bundle action `appFullRS Ψ hΨ W` decomposes as
```
∇_v (Ψ · W) = (∇^Hom_v Ψ)(W x) + Ψ x (∇_v W).
```
**Proof.** The fibre value of `appFullRS Ψ hΨ W` is `Ψ y (W y)` (`appFullRS_toSection`), so its directional
covariant derivative is `tensorRSCovariantDerivative … (fun y => Ψ y (W y)) x v`; the raw-section apply of
the second-order Hom-bundle covariant derivative
(`homTensorRSCovariantDerivative_apply_of_mdifferentiableAt`) reads this as
`(∇^Hom_v Ψ)(W x) + Ψ x (∇_v W)` (rearranging the product-rule subtraction). -/
theorem tensorCovDerivAt_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) (v : E) :
    (show TensorRSSpace r c I x from
        tensorCovDerivAt (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) x v) =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
          homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v) (W.toSection x) +
        (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
          (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v) := by
  -- The fibre field of `appFullRS Ψ hΨ W` is `y ↦ Ψ y (W y)`.
  have hval : (fun y : M => (appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection y) =
      (fun y : M => (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W.toSection y)) := by
    funext y; rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W y]
  -- Differentiability of `Ψ`, `W`, and the constant-`v` direction field at `x`.
  have hΨ_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x :=
    hΨ.contMDiffAt.mdifferentiableAt (by simp)
  have hW_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W.toSection y)) x :=
    W.toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨Vsec, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hV_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Vsec y)) x :=
    Vsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- Rewrite the LHS directional derivative through the Hom product rule applied at the direction `v`.
  rw [tensorCovDerivAt_def (I := I) (M := M) g r c (appFullRS (I := I) (M := M) g r a c Ψ hΨ W) x v,
    hval]
  rw [show v = (Vsec : Π z : M, TangentSpace I z) x from hVx.symm]
  -- `homTensorRSCovariantDerivative … Ψ x (Vsec x) (W x) = ∇^{(r,c)}(Ψ·W) − Ψ(∇^{(r,a)} W)`.
  have hprod := homTensorRSCovariantDerivative_apply_of_mdifferentiableAt I M r a c
    (LeviCivita (I := I) g) Ψ (fun y : M => W.toSection y) (fun y : M => Vsec y)
    hΨ_diff hW_diff hV_diff
  -- Rearrange `∇^{(r,c)}(Ψ·W) = (∇^Hom Ψ)(W) + Ψ(∇^{(r,a)} W)`.
  rw [eq_sub_iff_add_eq] at hprod
  rw [tensorCovDerivAt_def (I := I) (M := M) g r a W x ((Vsec : Π z : M, TangentSpace I z) x)]
  rw [← hprod]

/-! ## Generic full-Hom factorisation of a value-local `ℝ`-linear smooth fibre operation

A fibre operation `F : SmoothCcTensor g r a → SmoothCcTensor g r c` that is (i) **value-local** (its
fibre value at `x` depends only on the contracted section's fibre value `W x`), (ii) `ℝ`-**linear** at
the fibre-value level, and (iii) **smooth-coefficient** (sends smooth sections to smooth sections — built
in to the `SmoothCcTensor` codomain) factors through a *fixed* smooth full Hom-bundle field
`Θ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x`:
```
(F W).toSection x = Θ x (W.toSection x).
```
The fibrewise operator `Θ x` is the value-local fibre operation read on `W x` (well-defined by
value-locality, `ℝ`-linear by linearity, continuous on the finite-dimensional fibre via
`LinearMap.toContinuousLinearMap`); its base-point smoothness is the `contMDiff_clm_section_of_pointwise`
pointwise bridge, with the pointwise smooth input `x ↦ Θ x (Z x) = (F Z).toSection x` being the smooth
`SmoothCcTensor` `F Z`.  This is the generic engine behind both the order-`0` and order-`1` valence-`r`
full-Hom factorisations (the rank-`0` mirror `pureREndoOp_contMDiff` / `pureRGenuineEndoFib_eq_comp` uses
the codomain-only post-composition because the rank-`0` curvature acts only on the codomain; at valence
`r ≥ 1` the curvature reads the *whole* fibre, so the generic value-local fibre operation is needed). -/

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **A chosen smooth compactly-supported `(r, a)`-tensor realising a prescribed fibre value at `x`.**
The `SmoothCcTensor` wrapper (compact support is automatic on the closed manifold) of the smooth section
`ContMDiffSection.exists_eq_at` produces with value `v` at `x`. -/
private noncomputable def chooseSecAt
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The chosen section realises its prescribed fibre value at `x`. -/
private lemma chooseSecAt_eq
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    (chooseSecAt (I := I) (M := M) g r a x v).toSection x = v :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise operator extracted from a value-local `ℝ`-linear fibre operation.** For
`F : SmoothCcTensor g r a → SmoothCcTensor g r c` value-local and `ℝ`-linear at the fibre-value level,
the linear-map-to-CLM closure on the finite-dimensional fibre `TensorRSSpace r a I x` of the fibre
operation `v ↦ (F (chooseSecAt v)).toSection x` (`chooseSecAt v` any smooth section with value `v` at
`x`).  The source fibre carries the `g`-fibre `RiemannianBundle` inner-product normed structure (the
default model-norm instances suppressed), under which it is finite-dimensional Hausdorff and the linear
map closes to a continuous-linear map. -/
private noncomputable def valueLocalLinearHomFib
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (x : M) : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) := inferInstance
  haveI : T2Space (TensorRSSpace r a I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TensorRSSpace r a I x =>
        (F (chooseSecAt (I := I) (M := M) g r a x v)).toSection x
      map_add' := fun v w => by
        have hsum : (chooseSecAt (I := I) (M := M) g r a x (v + w)).toSection x =
            (chooseSecAt (I := I) (M := M) g r a x v +
              chooseSecAt (I := I) (M := M) g r a x w).toSection x := by
          rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
            chooseSecAt_eq, chooseSecAt_eq, chooseSecAt_eq]
        rw [hloc _ _ x hsum, hadd]
      map_smul' := fun k v => by
        have hsm : (chooseSecAt (I := I) (M := M) g r a x (k • v)).toSection x =
            (k • chooseSecAt (I := I) (M := M) g r a x v).toSection x := by
          rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
            chooseSecAt_eq, chooseSecAt_eq]
        rw [hloc _ _ x hsm, hsmul]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise operator reads the contracted section's value.** `valueLocalLinearHomFib F … x`
applied to `W.toSection x` returns `(F W).toSection x`, for any smooth section `W` — by value-locality,
the value at `x` does not depend on which section realises `W.toSection x` (the chosen one or `W`). -/
private lemma valueLocalLinearHomFib_apply
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (W : SmoothCcTensor g r a) (x : M) :
    valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (W.toSection x) =
      (F W).toSection x := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  rw [valueLocalLinearHomFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  exact hloc _ W x (chooseSecAt_eq (I := I) (M := M) g r a x (W.toSection x))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the value-local linear fibre operator field.** Via the pointwise
`contMDiff_clm_section_of_pointwise` bridge: for any smooth `(r, a)`-section `Z`,
`x ↦ valueLocalLinearHomFib F … x (Z x) = (F Z).toSection x` is the smooth `SmoothCcTensor` `F Z`. -/
private theorem valueLocalLinearHomFib_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
        (valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel r a ℝ E) (V₁ := fun z : M => TensorRSSpace r a I z)
    (F₂ := TensorRSModel r c ℝ E) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)
  intro Z
  set Wσ : SmoothCcTensor g r a := ⟨Z, HasCompactSupport.of_compactSpace _⟩ with hWσ
  have hpt : ∀ x : M, valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (Z x) =
      (F Wσ).toSection x := fun x =>
    valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc Wσ x
  refine (F Wσ).toSection.contMDiff.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (TensorRSModel r c ℝ E)
    (E := fun z : M => TensorRSSpace r c I z) x) (hpt x)).symm ▸ rfl

/-! ## The `(∇R)·` factorisation of the order-`1` moving-centre pure-Riemann trace (precise child)

The order-`1` moving-centre pure-Riemann differentiated trace `genuinePureRDiffOpRS g r 1 rr` is the
genuine `(∇R) W` contraction `covGrad(R W) − R(∇W)`.  At a generic contravariant valence `r ≥ 1` the
order-`0` curvature endomorphism `genuinePureREndo0RS g r rr` is the genuine full `(r, rr)`-tensor
curvature trace (both branches of `riemannOp_tensorCovRS_apply_eval`), so the differentiated trace factors
**value-locally** as the full Hom-bundle action `appFullRS Θ_rr W` of a *fixed* smooth full Hom-bundle
curvature-jet field `Θ_rr : Π x, TensorRSSpace r rr I x →L TensorRSSpace r (rr + 1) I x` — the curvature
derivative `∇R` read as a fibrewise operator on the full tensor fibre, the input derivative `∇W`
cancelling by the full Hom-bundle covariant product rule.  This is the exact valence-`r` mirror of the
rank-`0` *proved* `diffCurvGenuineDiffOp_zero_eq_appCc` (`op 0 = appCc Φ₀ W`, where the codomain-only
`appCc` post-composition suffices because the rank-`0` curvature acts only on the codomain). -/

set_option backward.isDefEq.respectTransparency false in
/-- **Child (the value-locality of the order-`1` differentiated pure-Riemann trace — the `∇W`
cancellation / differential-Bianchi content).** For two smooth compactly-supported `(r, rr)`-tensors
`W₁, W₂` agreeing *only* at the single fibre value `x` (`W₁.toSection x = W₂.toSection x`, not their
jets), the order-`1` differentiated trace fibre values coincide:
`(genuinePureRDiffOpRS g r 1 rr W₁).toSection x = (genuinePureRDiffOpRS g r 1 rr W₂).toSection x`.

**Why this is TRUE (the irreducible content).** The order-`1` trace is the genuine differentiated
curvature `(∇R) W = covGrad(R W) − R(∇W)`.  Both `covGrad(R W)` (reading the one-jet of `W` through the
order-`0` curvature endomorphism `R = genuinePureREndo0RS`) and `R(∇W)` (the rank-cast order-`0` curvature
on the gradient `∇W`) separately read the one-jet of `W` at `x`; in their *difference* the input
derivative `∇W` **cancels** by the second-order Hom-bundle covariant product rule
`∇_v(R·W) = (∇^Hom_v R)(W x) + R(∇_v W)` (`tensorCovDerivAt_appFullRS_eq`, proved above): the directional
reading of `covGrad(R W)` is `(∇^Hom R)(W x)` — value-local in `W x` — plus the spectator `R(∇_v W)`,
which is exactly the rank-cast `R(∇W)` term subtracted off (the curvature reading of the gradient
spectator, `genuinePureRDiffOp0_covGrad_fib_eq`).  The remaining `(∇^Hom R)(W x)` reads only the fibre
value `W x`, so two sections agreeing at `x` give equal order-`1` traces.  This is the differential
Bianchi / curvature-derivative-is-a-field content at valence `r`; the `∇W` cancellation is the single
genuinely-irreducible analytic primitive (the rank-`0` mirror is the spectator decomposition
`covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator`).  Posited here as one precise
true child; consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate reading (the order-`1` trace independent of `W x`) is rejected: the trace is
the genuine `(∇R) W`, nonzero for a non-parallel `W` on a non-flat manifold, so the value at `x` genuinely
depends on `W x`. -/
theorem genuinePureRDiffOpRS_one_valueLocal
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W₁ W₂ : SmoothCcTensor g r rr) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The order-`1` differentiated pure-Riemann trace is additive at the fibre-value level.** Derived
from the section-level `ℝ`-bilinearity `genuinePureRDiffOpRS_one_linear` (`c₁ = c₂ = 1`). -/
private lemma genuinePureRDiffOpRS_one_add_fib
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W₁ W₂ : SmoothCcTensor g r rr) (x : M) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr (W₁ + W₂)).toSection x =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x +
        (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x := by
  have h := genuinePureRDiffOpRS_one_linear (I := I) (M := M) g r rr 1 1 W₁ W₂
  rw [one_smul, one_smul, one_smul, one_smul] at h
  rw [h, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The order-`1` differentiated pure-Riemann trace is `ℝ`-homogeneous at the fibre-value level.**
Derived from the section-level `ℝ`-bilinearity `genuinePureRDiffOpRS_one_linear` (second slot zero). -/
private lemma genuinePureRDiffOpRS_one_smul_fib
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (k : ℝ) (W : SmoothCcTensor g r rr) (x : M) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr (k • W)).toSection x =
      k • (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W).toSection x := by
  have h := genuinePureRDiffOpRS_one_linear (I := I) (M := M) g r rr k 0 W W
  rw [zero_smul, add_zero, zero_smul, add_zero] at h
  rw [h, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The `(∇R)·` value-local full-Hom factorisation of the order-`1` trace (the leaf).** The smooth
full Hom-bundle curvature-jet field `Θ rr := valueLocalLinearHomFib (genuinePureRDiffOpRS g r 1 rr)` is
the order-`1` differentiated trace read fibrewise: its fibre value at `x` reads only `W x` (value-locality
`genuinePureRDiffOpRS_one_valueLocal`, `ℝ`-linearity `genuinePureRDiffOpRS_one_{add,smul}_fib`), closed to
a continuous-linear endomorphism on the finite-dimensional fibre, smooth in `x` by the pointwise
`SmoothCcTensor`-section bridge `valueLocalLinearHomFib_contMDiff`.  The factorisation
`(genuinePureRDiffOpRS g r 1 rr W).toSection x = Θ rr x (W x)` is `valueLocalLinearHomFib_apply`. -/
theorem exists_genuinePureRDiffOpRS_one_appFullRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ (Θ : (rr : ℕ) → Π x : M, TensorRSSpace r rr I x →L[ℝ] TensorRSSpace r (rr + 1) I x),
      (∀ rr : ℕ, ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r rr ℝ E →L[ℝ] TensorRSModel r (rr + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r rr ℝ E →L[ℝ] TensorRSModel r (rr + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r rr I z →L[ℝ] TensorRSSpace r (rr + 1) I z) x (Θ rr x))) ∧
      ∀ (rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W).toSection x =
          Θ rr x (W.toSection x) := by
  refine ⟨fun rr => valueLocalLinearHomFib (I := I) (M := M) g r rr (rr + 1)
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr)
      (genuinePureRDiffOpRS_one_add_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_smul_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_valueLocal (I := I) (M := M) g r rr), fun rr => ?_, fun rr W x => ?_⟩
  · exact valueLocalLinearHomFib_contMDiff (I := I) (M := M) g r rr (rr + 1)
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr)
      (genuinePureRDiffOpRS_one_add_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_smul_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_valueLocal (I := I) (M := M) g r rr)
  · exact (valueLocalLinearHomFib_apply (I := I) (M := M) g r rr (rr + 1)
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr)
      (genuinePureRDiffOpRS_one_add_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_smul_fib (I := I) (M := M) g r rr)
      (genuinePureRDiffOpRS_one_valueLocal (I := I) (M := M) g r rr) W x).symm

set_option linter.unusedSectionVars false in
/-- **The order-`1` moving-centre pure-Riemann trace is value-local in the contracted section.** For two
smooth compactly-supported `(r, rr)`-tensors `W₁, W₂` agreeing at `x`, the order-`1` differentiated trace
fibre values coincide.  The consumer-facing alias of the value-locality child
`genuinePureRDiffOpRS_one_valueLocal` (the `∇W`-cancellation / differential-Bianchi primitive); consumers
transitively depend on its `sorryAx`. -/
theorem genuinePureRDiffOpRS_one_local
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W₁ W₂ : SmoothCcTensor g r rr) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x :=
  genuinePureRDiffOpRS_one_valueLocal (I := I) (M := M) g r rr W₁ W₂ x hW

/-! ## The uniform full-Hom contraction bound and the differentiated `(∇R)·` tower jet envelope

The differentiated `(∇R)·` tower `diffCurvGenuineTowerOpRS` is the exact covariant-Leibniz remainder
recursion off the order-`1` trace `genuinePureRDiffOpRS g r 1 rr`, whose value-local full-Hom
factorisation (`exists_genuinePureRDiffOpRS_one_appFullRS`) makes the whole tower a finite sum of full
Hom-bundle actions of the *fixed* iterated curvature jets `∇^{≤ p}(∇R)` on the covariant jets `∇^{≤ p}W`
of the contracted section (the full-Hom normal form `exists_diffCurvGenuineTowerOpRS_normalFormFull`).
Each fixed smooth full-Hom field is uniformly fibre-operator-bounded over the compact `M` by the
curvature-jet sup `‖∇^{≤ p + 1} R‖_∞` (`exists_uniform_riemannianFiberNormSq_appFullRS_le`); the finite
sum is accumulated by `riemannianFiberNormSq_sum_le_card_mul`, giving the tight `p + 1` window
(the section entering at order `0`). -/

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **Child (the continuous per-point `g`-fibre-operator contraction envelope of a smooth full Hom-bundle
section).** For a *fixed* smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c
I x` on a Riemannian manifold there is a **continuous** nonnegative function `Cop : M → ℝ` with the
per-point fibrewise contraction bound
```
rfns(Ψ x v) ≤ Cop x · rfns(v)
```
at every point `x` and every `(r, a)`-tensor fibre value `v`.

**Why this is TRUE.** Each fibre evaluation obeys the per-point fibrewise Cauchy–Schwarz
`rfns(Ψ x v) ≤ ‖Ψ x‖_g² · rfns(v)` (`riemannianFiberNormSq_appFullRS_clm_apply_le`, *proved*), where
`‖Ψ x‖_g` is the operator norm of `Ψ x` taken in the installed `g`-fibre `RiemannianBundle` inner-product
structures on `TensorRSSpace r a` / `TensorRSSpace r c`.  The genuinely-irreducible analytic content is the
**base-point continuity** `Cop x := ‖Ψ x‖_g²`: the `g`-fibre operator norm of the continuous Hom-bundle
section `Ψ` is continuous in `x` (the fibre inner products vary continuously with `g`, and `Ψ` varies
continuously in the model trivialisation; this is genuine *continuity*, never the chart-selection-*uniform*
operator-norm bound which is unbounded on multi-chart manifolds).  This is the exact full-Hom analogue of
the *proved* per-point continuous curvature-operator envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`
(`UniformProportionalCurvatureSup`); the abstract `Hom(T^{r,a}, T^{r,c})` bundle is *not* a `SmoothCcTensor`
of any rank (it is a higher-order operator bundle with no chart-component continuity API, so the
tensor-section route `exists_bound_riemannianFiberNormSq_smoothCcTensor` does not apply), so the operator-
norm continuity is the single precise atomic primitive of the uniform contraction bound, posited here.
Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate `Cop ≡ 0` is rejected: the bound at any `v` with `rfns(v) > 0` and
`Ψ x v ≠ 0` forces `Cop x > 0`; the smallest valid value is the genuine squared `g`-fibre operator norm
`‖Ψ x‖_g²`, positive wherever `Ψ x ≠ 0`. -/
theorem exists_continuous_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  sorry

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **Child (uniform `g`-fibre-operator boundedness of a smooth full Hom-bundle section), assembled from
the continuous envelope and compactness.** For a *fixed* smooth full Hom-bundle field
`Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed Riemannian manifold there is a single
nonnegative constant `C`, uniform over `M`, with the per-point fibrewise contraction bound
```
rfns(Ψ x v) ≤ C · rfns(v)
```
for every point `x` and every `(r, a)`-tensor fibre value `v`.

**Proof.** By the continuous per-point envelope `exists_continuous_riemannianFiberNormSq_homSection_clm_le`
there is a continuous nonnegative `Cop : M → ℝ` with `rfns(Ψ x v) ≤ Cop x · rfns(v)`; on the compact `M`
the continuous `Cop` has bounded range (`(isCompact_univ).image Cop_cont |>.bddAbove`), so
`C := max C₀ 0 ≥ Cop x` uniformly, and `Cop x · rfns(v) ≤ C · rfns(v)` by `rfns(v) ≥ 0`.  This is the exact
full-Hom mirror of `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`'s
continuous-envelope-to-uniform-sup step.  Consumers transitively depend on the continuous envelope child's
`sorryAx`.

**Non-vacuity.** A degenerate `C < 0` is rejected: the conclusion `rfns(Ψ x v) ≤ C · rfns(v)` at any `v`
with `rfns(v) > 0` and `Ψ x v ≠ 0` forces `C > 0`; the smallest valid `C` is the genuine uniform squared
`g`-fibre operator-norm sup, positive for a nonzero `Ψ`. -/
theorem exists_uniform_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  obtain ⟨Cop, hCop_cont, hCop_nn, hCop_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  have hCpt := (isCompact_univ (X := M)).image hCop_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v => ?_⟩
  have hCop_le : Cop x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  refine le_trans (hCop_bound x v) ?_
  exact mul_le_mul_of_nonneg_right hCop_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The uniform full-Hom contraction bound, the `‖∇^{≤ p} R‖_∞` curvature-jet sup.** For a *fixed*
smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed
Riemannian manifold there is a single nonnegative constant `C`, uniform over `M`, with
```
rfns(Ψ x (W x)) ≤ C · rfns(W x)
```
for every `(r, a)`-tensor fibre value and every point `x`.  The full-fibre analogue of the *proved*
`exists_uniform_riemannianFiberNormSq_appCcRS_le` (the codomain-only post-composition bound).

**Proof.** The fibre value of `appFullRS Ψ hΨ W` at `x` is `Ψ x (W x)` (`appFullRS_toSection`), so the
claim is the per-fibre-value uniform `g`-fibre-operator contraction bound
`exists_uniform_riemannianFiberNormSq_homSection_clm_le` specialised to the fibre value `v = W.toSection x`.
Consumers transitively depend on that child's `sorryAx`. -/
theorem exists_uniform_riemannianFiberNormSq_appFullRS_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g r a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r c x
          ((appFullRS (I := I) (M := M) g r a c Ψ hΨ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨C, hC_nn, fun W x => ?_⟩
  rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W x]
  exact hC x (W.toSection x)

end Connection
end Integral
end DifferentialGeometry

end
