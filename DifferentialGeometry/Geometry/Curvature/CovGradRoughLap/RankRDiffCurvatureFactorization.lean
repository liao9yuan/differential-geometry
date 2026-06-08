import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS
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
  abstract `Hom(T^{r,rr}, T^{r,rr+1})` bundle), absent sorry-free below this file (the codomain-only
  `appCcRS` post-composition `diffCurvGenuineDiffOp_zero_eq_appCc` misses the contravariant curvature branch
  `riemannOp_tensorCovRS_apply_eval`, and the full `TensorRS` operator bundle carries no chart-component
  continuity API the rank-`0` `pureREndoOp_contMDiff` relied on);
* `exists_uniform_riemannianFiberNormSq_homSection_clm_le` — the uniform `g`-fibre-operator bound
  `rfns(Ψ x v) ≤ C · rfns(v)` (`C` uniform over the compact `M`) for a fixed smooth full Hom-bundle section
  `Ψ`.  This is the genuine atomic primitive isolated by decomposing the uniform full-Hom contraction
  bound: the uniform fibre-operator boundedness of a smooth full Hom-bundle section over a compact base —
  the full-Hom analogue of the *tensor*-section bound `exists_bound_riemannianFiberNormSq_smoothCcTensor`,
  which does NOT apply since the abstract `Hom(T^{r,a}, T^{r,c})` bundle is no `SmoothCcTensor`.  The
  contraction bound `exists_uniform_riemannianFiberNormSq_appFullRS_le` is *proved* over this leaf
  (specialise to the fibre value `v = W x`, `appFullRS_toSection`).

Consumers transitively depend on these two leaves' `sorryAx`.

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

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **Child (the `(∇R)·` value-local full-Hom factorisation of the order-`1` trace).** For a closed smooth
Riemannian manifold `(M, g)` and a fixed contravariant valence `r` there is a *fixed* smooth full
Hom-bundle curvature-jet field family
`Θ : (rr : ℕ) → Π x, TensorRSSpace r rr I x →L TensorRSSpace r (rr + 1) I x` such that the order-`1`
moving-centre pure-Riemann differentiated trace `genuinePureRDiffOpRS g r 1 rr` is its **value-local** full
Hom-bundle action:
```
(genuinePureRDiffOpRS g r 1 rr W).toSection x = Θ rr x (W.toSection x).
```
The fibre value at `x` reads only the fibre value `W x` against the fixed smooth curvature-jet operator
`Θ rr x` (the curvature derivative `∇R(x)` as a full Hom endomorphism).

**Why this is TRUE.** The genuine `(∇R) W = covGrad(R W) − R(∇W)` factors value-locally as the full
Hom-bundle action `appFullRS Θ W` of the *fixed* smooth full-tensor curvature-jet field `Θ rr x`.  Two
genuinely-irreducible analytic facts combine: (i) **value-locality + `ℝ`-linearity** of the order-`1`
trace at the fibre-value level — both `covGrad(op 0 rr W)` and `cast(op 0 (rr + 1)(∇W))` separately read
the one-jet of `W` at `x`, but their *difference* is the genuine `(∇R) W` in which the input derivative
`∇W` *cancels* by the full-tensor Hom-bundle covariant product rule `∇(R·W) = (∇R)·W + R·(∇W)` (the
source/target two-sided Hom Leibniz of the full `(r, rr)`-tensor curvature `riemannOp (tensorCov g r rr)`),
leaving a fibrewise operator `Θ rr x` reading only `W x` (this is **false for a generic
order-`0`-value-local tower** — the abstract claim is Lean-refuted at `(p, rr) = (1, 0)`,
`OperatorFieldEvaluationLeibniz`: with `op 0 0 := 0`, `op 0 1 := id` the recursion forces
`op 1 0 W = −cast(∇W)`, reading the one-jet, *not* value-local; only the genuine curvature operator, whose
order-`0` coefficient is the smooth `∇R = ∇(g, R)`, has the cancellation); and (ii) **base-point
smoothness** of the extracted full-Hom curvature-coefficient field `Θ rr`, the valence-`r` full-Hom
analogue of the rank-`0` *proved* `pureREndoOp_contMDiff` (the ~600-line unit-scalar-lift reduction to the
moving-frame endomorphism smoothness `genuinePureREndoFibRS_contMDiff`).  Fact (i) needs the full-tensor
Hom-bundle covariant product rule for the abstract `Hom(T^{r,rr}, T^{r,rr+1})` bundle
(`covGrad_appFullRS_eq`), and fact (ii) needs the pointwise smoothness route
`contMDiff_clm_section_of_pointwise` lifted to that abstract Hom bundle — both absent sorry-free below
this file (the codomain-only `appCcRS` post-composition misses the contravariant curvature branch
`riemannOp_tensorCovRS_apply_eval`, and the full `TensorRS` operator bundle carries no chart-component
continuity API).  Posited here as one precise true child.  Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A degenerate factorisation `Θ ≡ 0` is rejected on any non-flat manifold: the order-`1`
trace `genuinePureRDiffOpRS g r 1 rr W` is the genuine differentiated curvature `(∇R) W`, genuinely
non-zero (`∇R ≠ 0`) for a non-parallel `W`, so `Θ rr x` cannot be the zero operator (else the LHS would
vanish identically). -/
theorem exists_genuinePureRDiffOpRS_one_appFullRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ (Θ : (rr : ℕ) → Π x : M, TensorRSSpace r rr I x →L[ℝ] TensorRSSpace r (rr + 1) I x),
      (∀ rr : ℕ, ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r rr ℝ E →L[ℝ] TensorRSModel r (rr + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r rr ℝ E →L[ℝ] TensorRSModel r (rr + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r rr I z →L[ℝ] TensorRSSpace r (rr + 1) I z) x (Θ rr x))) ∧
      ∀ (rr : ℕ) (W : SmoothCcTensor g r rr) (x : M),
        (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W).toSection x =
          Θ rr x (W.toSection x) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The order-`1` moving-centre pure-Riemann trace is value-local in the contracted section.** For two
smooth compactly-supported `(r, rr)`-tensors `W₁, W₂` agreeing at `x`, the order-`1` differentiated trace
fibre values coincide.  **Proof.** By the `(∇R)·` value-local full-Hom factorisation
`exists_genuinePureRDiffOpRS_one_appFullRS`, both fibre values are `Θ rr x (Wᵢ.toSection x)` of the *same*
fixed smooth full-Hom curvature-jet field `Θ rr x`; since `W₁.toSection x = W₂.toSection x`, the two are
equal.  Consumers transitively depend on the factorisation child's `sorryAx`. -/
theorem genuinePureRDiffOpRS_one_local
    (g : SmoothRiemannianMetric I M) (r rr : ℕ)
    (W₁ W₂ : SmoothCcTensor g r rr) (x : M)
    (hW : W₁.toSection x = W₂.toSection x) :
    (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₁).toSection x =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 1 rr W₂).toSection x := by
  obtain ⟨Θ, _hΘ, hfac⟩ := exists_genuinePureRDiffOpRS_one_appFullRS (I := I) (M := M) g r
  rw [hfac rr W₁ x, hfac rr W₂ x, hW]

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
/-- **Child (uniform `g`-fibre-operator boundedness of a smooth full Hom-bundle section).** For a *fixed*
smooth full Hom-bundle field `Ψ : Π x, TensorRSSpace r a I x →L TensorRSSpace r c I x` on a closed
Riemannian manifold there is a single nonnegative constant `C`, uniform over `M`, with the per-point
fibrewise contraction bound
```
rfns(Ψ x v) ≤ C · rfns(v)
```
for every point `x` and every `(r, a)`-tensor fibre value `v`.

**Why this is TRUE.** Each fibre evaluation obeys the per-point fibrewise Cauchy–Schwarz
`rfns(Ψ x v) ≤ ‖Ψ x‖_g² · rfns(v)` (`riemannianFiberNormSq_appFullRS_clm_apply_le`, *proved*), where
`‖Ψ x‖_g` is the operator norm of `Ψ x` taken in the installed `g`-fibre `RiemannianBundle` inner-product
structures on `TensorRSSpace r a` / `TensorRSSpace r c`.  The squared `g`-fibre operator norm
`x ↦ ‖Ψ x‖_g²` of the *fixed smooth* full Hom-bundle section `Ψ` is a continuous function on the compact
`M` (the `g`-fibre operator norm of a continuous Hom-bundle section is continuous in the base point: the
fibre inner products vary continuously with `g`, and `Ψ` varies continuously in the model trivialisation;
this is genuine *continuity*, never the chart-selection-*uniform* operator-norm bound which is unbounded on
multi-chart manifolds), so it attains a finite uniform maximum `C` over the compact base.  The uniform
`g`-fibre-operator boundedness of a fixed smooth full Hom-bundle section over a compact base — the genuine
full-Hom analogue of the *tensor*-section bound `exists_bound_riemannianFiberNormSq_smoothCcTensor` (which
does **not** apply: the abstract `Hom(T^{r,a}, T^{r,c})` bundle is *not* a `SmoothCcTensor` of any rank,
it is a higher-order operator bundle with no chart-component continuity API) — is absent sorry-free below
this file, so it is the single precise true child of the uniform contraction bound.  Consumers transitively
depend on `sorryAx`.

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
  sorry

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
