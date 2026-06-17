import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel

/-!
# The connection-difference vector as the inverse-Gram raise of the metric-difference covariant gradient

For a closed smooth Riemannian manifold `(M, g₀)` modelled on a real inner-product space `E`, a second
metric `g₁`, and a smooth `(0, 2)`-tensor section `S` whose extracted bilinear form is the metric
difference `g₁ − g₀`, this file expresses the **connection-difference tensor** `A = connDiff g₁ g₀`
(the intrinsic Christoffel variation `δΓ = ∇₁ − ∇₀`, the bedrock of the `(A)` Lichnerowicz `_core` for
the Ricci–DeTurck linearization) through the **bundled covariant gradient of the metric-difference
section**.

The classical Koszul / Christoffel-difference identity gives `A` only in its `g₁`-LOWERED form
(`connDiff_koszul_metricDiff`):
$$
  2\,g_1\bigl(A(Y, X), Z\bigr)
    = (\nabla^0_X h)(Y, Z) + (\nabla^0_Y h)(X, Z) - (\nabla^0_Z h)(X, Y),
    \qquad h = g_1 - g_0,\ \nabla^0 = \mathrm{LeviCivita}\,g_0,
$$
where `connDiff g₁ g₀ x (Y x) (X x) = ∇¹_X Y − ∇⁰_X Y` (Mathlib convention) and each `∇⁰ h` is the
Leibniz-defect `metricDiffCovDeriv`.  The metric-difference covariant-gradient bridge
(`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'`) reads each `∇⁰ h` term as the unit-evaluated bundled
covariant gradient `covGrad g₀ 0 2 S` (since `metricDiffCovDeriv g₀ g₀ = 0`).  Composing the two yields
the LOWERED bridge `connDiff_inner_eq_half_covGradKoszul`.

The genuinely new step is the **inverse-Gram raise**: the lowered identity holds for every test vector
`Z`, and the right-hand side is tensorial in `Z`, so non-degeneracy of `g₁`
(`SmoothRiemannianMetric.eq_of_inner_eq`) un-pairs it.  The raised vector is the inverse-metric sharp
`♯_{g₁}` (`inverseMetricSharpFib`, the index-raising operator of the cometric `g₁⁻¹`) applied to the
half-symmetrised Koszul covector, which is exactly the `(0, 2)`-covariant gradient `covGrad g₀ 0 2 S`
contracted to a covector in its trailing slot.  This is the `δΓ = ½ g₁⁻¹ (∇₀ h + ∇₀ h − ∇₀ h)`
formula of the Ricci–DeTurck development in raised form, the substitution the Lichnerowicz `_core`
consumes for the bare connection-difference value `A(V, W)`.

## Main results

* `connDiff_inner_eq_half_covGradKoszul` — the LOWERED bridge: twice the `g₁`-pairing of the
  connection-difference value `A(Y, X)` against `Z` equals the symmetric Koszul combination of the
  unit-evaluated covariant gradient `covGrad g₀ 0 2 S`.

* `connDiff_eq_appCc_invGram_covGrad` — **the inverse-Gram raise (headline)**: the connection-difference
  value `connDiff g₁ g₀ x (Y x) (X x)` equals the inverse-metric sharp `♯_{g₁}` of the half-symmetrised
  Koszul covector `koszulCovGradCovec g₀ g₁ S X Y x`, whose `g₁`-flat (`cotangentToDual`) evaluation on
  any vector is the half Koszul combination of `covGrad g₀ 0 2 S`.  This is the genuine raise of the
  lowered Koszul identity by the cometric operator field.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Abbreviation for the unit-evaluated covariant-gradient Koszul sum -/

/-- The unit-evaluated bundled covariant gradient `covGrad g₀ 0 2 S` read on the cons-tuple
`(X x, Y x, Z x)`: the `(0, 2)` Leibniz-defect covariant derivative `(∇₀_X (g₁ − g₀))(Y, Z)` when the
bilinear form of `S` is the metric difference (`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'`). -/
private def covGradEval (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
      (unitZeroSec (I := I) (M := M) x))
    (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))

/-! ## The lowered Koszul bridge through the covariant gradient -/

set_option linter.unusedSectionVars false in
/-- **The metric-difference Koszul covariant-gradient bridge (lowered form).**

Suppose the extracted bilinear form of the smooth `(0, 2)`-tensor section `S` is, at every base point
and on every pair of tangent vectors, the metric difference `g₁ − g₀` (a genuine hypothesis on `S`,
NOT the conclusion — the realize-tie content for `h = g₁ − g₀`).  Then twice the `g₁`-pairing of the
connection-difference value `connDiff g₁ g₀ x (Y x) (X x)` against `Z x` is the symmetric Koszul
combination of the unit-evaluated bundled covariant gradient `covGrad g₀ 0 2 S`:
```
2 g₁(connDiff g₁ g₀ (Y, X), Z)
  = covGrad(S)(X, Y, Z) + covGrad(S)(Y, X, Z) − covGrad(S)(Z, X, Y).
```
This composes the `g₁`-lowered Christoffel-difference Koszul identity `connDiff_koszul_metricDiff`
(through `metricDiffCovDeriv g₁ g₀`) with the covariant-gradient bridge
`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'` (which reads each `metricDiffCovDeriv g₁ g₀` term as
the unit-evaluated `covGrad`, since `metricDiffCovDeriv g₀ g₀ = 0`). -/
theorem connDiff_inner_eq_half_covGradKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    2 * g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      covGradEval (I := I) (M := M) g₀ S X Y Z x
        + covGradEval (I := I) (M := M) g₀ S Y X Z x
        - covGradEval (I := I) (M := M) g₀ S Z X Y x := by
  -- Each `covGradEval` term is `metricDiffCovDeriv g₁ g₀ − metricDiffCovDeriv g₀ g₀`, and
  -- `metricDiffCovDeriv g₀ g₀ = 0` since `∇₀` is metric-compatible with `g₀`.
  have hzero : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      metricDiffCovDeriv (I := I) g₀ g₀ (fun b => P b) (fun b => Q b) (fun b => R b) x = 0 := by
    intro P Q R
    unfold metricDiffCovDeriv
    rw [sub_self]
  -- Rewrite each `covGradEval` via bridge #3 (`g₁' := g₀`), then drop the vanishing `g₀ g₀` term.
  have hXYZ : covGradEval (I := I) (M := M) g₀ S X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil X Y Z x, hzero X Y Z, sub_zero]
  have hYXZ : covGradEval (I := I) (M := M) g₀ S Y X Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Y b) (fun b => X b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Y X Z x, hzero Y X Z, sub_zero]
  have hZXY : covGradEval (I := I) (M := M) g₀ S Z X Y x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Z b) (fun b => X b) (fun b => Y b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Z X Y x, hzero Z X Y, sub_zero]
  rw [hXYZ, hYXZ, hZXY]
  -- The remaining identity is the lowered Christoffel-difference Koszul identity in `metricDiffCovDeriv`
  -- form, with the three smooth fields supplied differentiably.
  exact connDiff_koszul_metricDiff (I := I) g₁ g₀
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt

/-! ## The half-symmetrised Koszul covector and the inverse-Gram raise -/

/-- **The half-symmetrised Koszul covector of the metric-difference covariant gradient.**

The `(0, 1)`-covector at `x` whose `g₁`-flat (`cotangentToDual`) evaluation on a tangent vector `ζ` is
the half symmetric Koszul combination of the unit-evaluated bundled covariant gradient
`covGrad g₀ 0 2 S` (the content of `koszulCovGradCovec_dual_apply_covGrad`):
```
cotangentToDual (koszulCovGradCovec g₀ g₁ X Y x) ζ
  = ½ (covGrad(S)(X, Y, ζ) + covGrad(S)(Y, X, ζ) − covGrad(S)(ζ, X, Y)).
```
Concretely it is the `dualToCotangent` packaging of the `g₁`-flat of the connection-difference value
`connDiff g₁ g₀ x (Y x) (X x)`.  Packaging through the `g₁`-flat makes the covector manifestly a
continuous linear functional (and extension-independent); the covariant-gradient evaluation is then
supplied by the lowered bridge `connDiff_inner_eq_half_covGradKoszul` (it does not depend on the
section `S` until that bridge is invoked, so `S` is not part of the covector datum). -/
def koszulCovGradCovec (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace 1 I x :=
  dualToCotangent (I := I)
    ((g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x))).toLinearMap)

set_option linter.unusedSectionVars false in
/-- The `g₁`-flat (`cotangentToDual`) of the half-symmetrised Koszul covector reproduces the metric
pairing of the connection-difference value: `cotangentToDual (koszulCovGradCovec …) ζ
= g₁(connDiff g₁ g₀ (Y, X), ζ)`. -/
@[simp] theorem koszulCovGradCovec_dual_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) ζ := by
  rw [koszulCovGradCovec, cotangentToDual_dualToCotangent]
  rfl

set_option linter.unusedSectionVars false in
/-- **The covariant-gradient evaluation of the half-symmetrised Koszul covector.**

Under the metric-difference hypothesis `hbil` on `S`, the `g₁`-flat of the Koszul covector evaluated on
the value `Z x` of a smooth field `Z` is the half symmetric Koszul combination of the unit-evaluated
covariant gradient `covGrad g₀ 0 2 S`:
```
cotangentToDual (koszulCovGradCovec g₀ g₁ X Y x) (Z x)
  = ½ (covGrad(S)(X, Y, Z) + covGrad(S)(Y, X, Z) − covGrad(S)(Z, X, Y)).
```
This identifies the Koszul covector with the trailing-slot contraction of `covGrad g₀ 0 2 S`; it is the
lowered bridge `connDiff_inner_eq_half_covGradKoszul` read through the covector packaging. -/
theorem koszulCovGradCovec_dual_apply_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) (Z x) =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S X Y Z x
          + covGradEval (I := I) (M := M) g₀ S Y X Z x
          - covGradEval (I := I) (M := M) g₀ S Z X Y x) := by
  rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x (Z x)]
  have h := connDiff_inner_eq_half_covGradKoszul (I := I) (M := M) g₀ g₁ S hbil X Y Z x
  linarith [h]

set_option linter.unusedSectionVars false in
/-- **The inverse-Gram raise of the metric-difference covariant gradient (headline).**

The connection-difference value `connDiff g₁ g₀ x (Y x) (X x)` (the intrinsic Christoffel variation
`δΓ = ∇₁ − ∇₀` evaluated at `Y` in direction `X`) is the inverse-metric sharp `♯_{g₁}`
(`inverseMetricSharpFib`, the index-raising operator of the cometric `g₁⁻¹`) of the half-symmetrised
Koszul covector `koszulCovGradCovec g₀ g₁ X Y x`, whose `g₁`-flat evaluation is, on any smooth section
`S` realising the metric difference `g₁ − g₀`, the half symmetric Koszul combination of the bundled
covariant gradient `covGrad g₀ 0 2 S` (`koszulCovGradCovec_dual_apply_covGrad`):
```
connDiff g₁ g₀ x (Y x) (X x)
  = ♯_{g₁} (½ (covGrad(S)(X, Y, ·) + covGrad(S)(Y, X, ·) − covGrad(S)(·, X, Y))).
```
This is the `δΓ = ½ g₁⁻¹ (∇₀ h + ∇₀ h − ∇₀ h)` formula of the Ricci–DeTurck development in raised
form: the lowered Koszul identity `connDiff_inner_eq_half_covGradKoszul` holds for every test vector and
its right-hand side is tensorial, so non-degeneracy of `g₁` (`SmoothRiemannianMetric.eq_of_inner_eq`)
un-pairs it.  It is the substitution the `(A)` Lichnerowicz `_core` consumes for the bare
connection-difference value. -/
theorem connDiff_eq_appCc_invGram_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) := by
  -- Non-degeneracy of `g₁`: it suffices to match the `g₁`-pairing against every test vector `ζ`.
  refine (SmoothRiemannianMetric.eq_of_inner_eq g₁ (fun ζ => ?_)).symm
  -- The sharp un-pairs against the `g₁`-flat of the Koszul covector (`inverseMetricSharpFib_inner`),
  -- which is precisely `g₁(connDiff (Y, X), ζ)` (`koszulCovGradCovec_dual_apply`).
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ,
      cotangentToDualLinear_apply,
      koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x ζ]

/-! ## The differentiated connection difference (the value-level order-graded product rule) -/

set_option linter.unusedSectionVars false in
/-- **The differentiated connection difference, order-graded (value level).**

The directional covariant derivative `covDerivConnDiff g₀ g₁ X Z Y x` of the connection-difference
tensor `A = connDiff g₁ g₀` under the `g₀`-Levi-Civita connection (`= (∇₀_X A)(Z, Y)` in the
consumer's `X Z Y` slot order) is the order-graded covariant product rule of the inverse-Gram raise
`connDiff_eq_appCc_invGram_covGrad`.  Writing `K = koszulCovGradCovec g₀ g₁ Z Y` for the `g₁`-flat
Koszul covector of the metric-difference covariant gradient, `A(Z, Y) = ♯_{g₁}(K)` (leaf (1)), so
differentiating covariantly in `X` along `∇₀` and using the difference one-form `connDiff` to swap
`∇₀ ↔ ∇₁` together with the `∇₁`-parallelism of `♯_{g₁}`
(`inverseMetricSharpField_covGrad_eq_zero`) gives
```
(∇₀_X A)(Z, Y)
  = ♯_{g₁}(∇₁_X K)                                   -- the order-2 PRINCIPAL: the further covariant
                                                       --   gradient of K (carrying ∇₀²(metric diff)),
                                                       --   raised by the cometric ♯_{g₁};
    − A(♯_{g₁}(K), X)                                -- the order-1 CROSS term ∇₀(g₁⁻¹) (the genuine
                                                       --   endpoint coefficient: the Christoffel
                                                       --   difference applied to the raised K);
    − A(Y, ∇₀_X Z) − A(∇₀_X Y, Z),                   -- the two order-1 SLOT corrections of the
                                                       --   (1, 2)-tensor covariant derivative,
```
where `∇₁_X K := dualToCotangent ((cotangentCov (LeviCivita g₁)) (b ↦ cotangentToCLM (K b)) x (X x))`
is the `g₁`-cotangent covariant derivative of the Koszul covector, `A(·, ·) = connDiff g₁ g₀ x · ·`,
and `∇₀_X Z = (LeviCivita g₀) Z x (X x)`.  The principal `♯_{g₁}(∇₁_X K)` is the order-2 term the
Ricci–DeTurck `C₂` linearization expands; the three `connDiff` terms are the order-1 cross
coefficients (`A = δΓ`, the intrinsic Christoffel variation).  This is the value-level identity the
Ricci/Lie arms consume (the `appCc` packaging happens later, at the `(0, 2)` output level). -/
theorem covDerivConnDiff_eq_invGramSharp_graded
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := by
  classical
  -- The `g₁`-flat Koszul covector field and the raised connection-difference field.
  set K : Π b : M, Tensor0SSpace 1 I b :=
    fun b => koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b with hKdef
  -- Leaf (1), pointwise: `A(Z, Y) = ♯_{g₁}(K)` as a field equality.
  have hWeq : (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    exact (connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ Z Y b).symm
  set W : Π b : M, TangentSpace I b :=
    fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b) with hWdef
  -- Smoothness of the raised field `W` (`connDiff` of two smooth fields, first slot `Y`).
  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) x :=
    (hW_sm x).mdifferentiableAt (by simp)
  -- Same differentiability transported across `hWeq` to the `♯_{g₁}(K)` form (for the parallelism).
  have hWsharp_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (K b))) x := by
    have hfun : (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (inverseMetricSharpFib (I := I) g₁ b (K b))) =
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) := by
      funext b; rw [congrFun hWeq b]
    rw [hfun]; exact hW_at
  -- The `∇₀ ↔ ∇₁` swap on the raised field via the difference one-form `connDiff g₁ g₀`.
  have hswap : (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x) =
      (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (W x) (X x) := by
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => W b) (x := x) hW_at (X x)
    rw [h]; abel
  -- The `∇₁`-parallelism of the cometric raise applied to the Koszul covector field `K`.
  have hpar := inverseMetricSharpField_covGrad_eq_zero (I := I) g₁ K hWsharp_at (X x)
  -- Rewrite `(LeviCivita g₁) W` through `hWeq` into the `♯_{g₁}(K)` form, then apply `hpar`.
  have hW1 : (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I) (K b)) x (X x))) := by
    rw [show (fun b => W b) =
        (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) from hWeq.symm]
    exact hpar
  -- `W x = ♯_{g₁}(K x)` for the cross term.
  have hWx : W x = inverseMetricSharpFib (I := I) g₁ x (K x) := by
    have := congrFun hWeq x
    rw [hWdef]; exact this.symm
  -- The definitional unfolding of `covDerivConnDiff` (the bridge's `hexpand`, value level).
  have hexpand : covDerivConnDiff (I := I) g₀ g₁
        (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := rfl
  rw [hexpand, hswap, hW1, hWx]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
