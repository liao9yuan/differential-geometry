import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

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

/-! ## The cotangent connection-difference bridge (the dual of `connDiff`) -/

set_option linter.unusedSectionVars false in
/-- **The cotangent connection-difference bridge (value level).**

The induced cotangent covariant derivatives of the two `g₁`/`g₀`-Levi-Civita connections differ on a
smooth covector field `θ` exactly by the dual action of the (tangent) connection-difference tensor
`A = connDiff g₁ g₀`.  Writing `∇^{g}_K θ := cotangentCov (LeviCivita g) θ` for the cotangent covariant
derivative, evaluated at `x` in direction `v` on a test vector `w`,
```
(∇^{g₁}_K θ)(v)(w) − (∇^{g₀}_K θ)(v)(w) = −θ x (connDiff g₁ g₀ x w v).
```
This is the dual of the difference-tensor convention `connDiff g₁ g₀ x (σ x) v = ∇¹_v σ − ∇⁰_v σ`
(`connDiff_apply`): the cotangent connection is defined by the dual-pairing Leibniz rule
`cotangentScalar (cov) θ x X Y = X(θ(Y)) − θ(∇_X Y)` (`cotangentScalar_def`), whose first
(exterior-derivative) term is connection-independent and cancels in the difference, leaving the
covariant-derivative term `−θ(∇¹_X Y − ∇⁰_X Y) = −θ(connDiff g₁ g₀ (Y, X))`.  It is the genuine
order-dropping dual connection-difference, the last connection-conversion bridge the SP2-endpoint
principal alignment consumes (`cotangentCov(LeviCivita g₁) → cotangentCov(LeviCivita g₀)`). -/
theorem cotangentCov_leviCivita_diff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v) := by
  classical
  -- Extend `v`, `w` to smooth tangent fields so the defining `Φ`-formula applies for both connections.
  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXdef
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hX := smoothExtensionTangent_mdiff (I := I) x v x
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  -- Both cotangent covariant derivatives evaluate to the `cotangentScalar` Leibniz formula.
  have h₁ : ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₁).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₁) hθ hX hY]
  have h₀ : ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hX hY]
  rw [h₁, h₀, cotangentScalar_def, cotangentScalar_def]
  -- The connection-independent exterior-derivative terms cancel; the difference is the dual `connDiff`.
  have hconn : PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v =
      (LeviCivita (I := I) g₁).toFun Y x v - (LeviCivita (I := I) g₀).toFun Y x v := by
    have := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    rw [hYx] at this
    exact this
  rw [hconn, hXx]
  rw [map_sub]
  ring

set_option linter.unusedSectionVars false in
/-- **The continuous-linear realization of the half-symmetrised Koszul covector.**

The `cotangentToCLM` realization of the Koszul covector `koszulCovGradCovec g₀ g₁ Z Y b` is the
metric flat of the connection-difference value: `cotangentToCLM (K b) = g₁(connDiff g₁ g₀ (Y, Z), ·)`.
This is the `dualToCotangent`/`cotangentToCLM` round-trip `cotangentToDual_dualToCotangent` read
through the definition `koszulCovGradCovec = dualToCotangent (g₁(connDiff g₁ g₀ (Y, Z), ·).toLinearMap)`;
it identifies the cotangent field the SP2-endpoint principal differentiates with the smooth metric flat
`metricFlat g₁` of the smooth connection-difference vector field. -/
theorem cotangentToCLM_koszulCovGradCovec
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) =
      g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
  rw [koszulCovGradCovec]
  apply ContinuousLinearMap.ext
  intro w
  exact cotangentToDual_dualToCotangent (I := I)
    ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap) ▸
      (rfl : cotangentToDual (I := I) (dualToCotangent (I := I)
        ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap)) w =
        cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) w)

set_option linter.unusedSectionVars false in
/-- **Smoothness of the Koszul cotangent realization (cotangent-differentiability).**

The covector field `b ↦ cotangentToCLM (koszulCovGradCovec g₀ g₁ Z Y b)` the SP2-endpoint principal
differentiates is cotangent-differentiable (`MDiffAtCotangent`) at every point.  By
`cotangentToCLM_koszulCovGradCovec` it equals the metric flat `metricFlat g₁ (connDiff g₁ g₀ (Y, Z))`
of the smooth connection-difference vector field (`connDiff_contMDiff`, smooth in the first slot `Y`,
direction `Z`); `metricFlat` of a differentiable vector field is cotangent-differentiable
(`metricFlat_mdiff`).  This discharges the `hθ` hypothesis of `cotangentCov_leviCivita_diff` for the
SP2-endpoint principal. -/
theorem koszulCovGradCovecCLM_mdiffAtCotangent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x := by
  have hflat : (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) =
      metricFlat (I := I) g₁
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    rw [cotangentToCLM_koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b]
    rfl
  rw [hflat]
  -- The connection-difference vector field is smooth (first slot `Y`, direction `Z`), so its
  -- metric flat is cotangent-differentiable.
  have hconn_sm := PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hconn_at := (hconn_sm x).mdifferentiableAt (by simp)
  exact metricFlat_mdiff (I := I) g₁ hconn_at

/-! ## The SP2-endpoint principal alignment (`cotangentCov(LeviCivita g₁) → cotangentCov(LeviCivita g₀)`) -/

set_option linter.unusedSectionVars false in
/-- **The SP2-endpoint principal alignment to the `g₀`-cotangent covariant derivative.**

The SP2-endpoint order-2 principal differentiates the Koszul covector with the *`g₁`*-cotangent
covariant derivative `cotangentCov (LeviCivita g₁)`.  Applying the cotangent connection-difference
bridge `cotangentCov_leviCivita_diff` (the dual of `connDiff g₁ g₀`) converts it to the
*`g₀`*-cotangent covariant derivative plus an order-`1` `connDiff` correction: evaluating both sides on
a test vector `w`,
```
(∇^{g₁}_K (cotangentToCLM K_S))(X x)(w)
  = (∇^{g₀}_K (cotangentToCLM K_S))(X x)(w)
    − cotangentToCLM (K_S x) (connDiff g₁ g₀ x w (X x)).
```
The principal `∇^{g₀}_K (cotangentToCLM K_S)` is the genuine `g₀`-covariant derivative of the Koszul
covector — the order-2 PRINCIPAL the Ricci–DeTurck `C₂` linearization expands as the iterated
covariant gradient `∇₀²` of the metric-difference section — while the `connDiff` term is the order-`1`
endpoint correction.  This is the last connection-conversion step: with it the SP2-endpoint principal
is expressed against the *background* connection `∇₀`, where the iterated-covariant-gradient calculus
(`covGrad`/`iteratedCovGrad`) applies. -/
theorem covDerivConnDiff_principal_align
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b : M => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w (X x)) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x
  have hbridge := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ (X x) w
  -- `hbridge : (∇^{g₁}_K θ)(X x)(w) − (∇^{g₀}_K θ)(X x)(w) = −θ x (connDiff g₁ g₀ x w (X x))`,
  -- where `θ x = cotangentToCLM (K x)` definitionally.
  linarith [hbridge]

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

/-! ## The two-endpoint mean-value telescope of the differentiated connection difference -/

set_option linter.unusedSectionVars false in
/-- **The two-endpoint differentiated connection difference, order-graded (value level).**

For a common base metric `g₀` and two endpoint metrics `g₁, g₁'` (in the consumer the realized
metrics `realize(g₀ + T)`, `realize(g₀ + T')` with section difference `S = T − T'`), the difference of
the differentiated connection-differences `covDerivConnDiff g₀ g₁ X Z Y x − covDerivConnDiff g₀ g₁' X Z
Y x` is the order-graded mean-value Leibniz telescope of the single-endpoint inverse-Gram raise
`covDerivConnDiff_eq_invGramSharp_graded` (leaf SP1'), assembled by applying SP1' at each endpoint and
subtracting term by term, with the principal term further telescoped by the add-subtract-middle-term
rule into a *same-operator-on-covector-difference* arm plus an *operator-difference-on-endpoint* arm.

Writing `K_g := koszulCovGradCovec g₀ g Z Y` for the `g`-flat Koszul covector of the metric-difference
covariant gradient (`covGrad g₀ 0 2` of the section realising `g − g₀`), `A_g := connDiff g g₀` for the
intrinsic Christoffel variation `δΓ`, `∇^g` the `g`-Levi-Civita connection, `∇^g_K` its induced
cotangent covariant derivative, and `♯_g := inverseMetricSharpFib g` the cometric raise, the identity is
```
covDerivConnDiff g₀ g₁ X Z Y x − covDerivConnDiff g₀ g₁' X Z Y x
  = ( ♯_{g₁}(∇^{g₁}_X K_{g₁}) − ♯_{g₁}(∇^{g₁}_X K_{g₁'}) )      -- (P) PRINCIPAL, order-2 in S:
                                                                 --   the SAME operators ♯_{g₁}∇^{g₁}
                                                                 --   on the covector difference K_S;
    + ( ♯_{g₁}(∇^{g₁}_X K_{g₁'}) − ♯_{g₁'}(∇^{g₁'}_X K_{g₁'}) ) -- (O) OPERATOR-DIFFERENCE, order-0:
                                                                 --   ♯_{g₁}∇^{g₁} − ♯_{g₁'}∇^{g₁'} on the
                                                                 --   ENDPOINT covector K_{g₁'};
    − ( A_{g₁}(♯_{g₁}(K_{g₁}), X) − A_{g₁'}(♯_{g₁'}(K_{g₁'}), X) ) -- (C) order-1 cross difference (δΓ);
    − ( A_{g₁}(Y, ∇^{g₀}_X Z) − A_{g₁'}(Y, ∇^{g₀}_X Z) )          -- (S₁) order-1 slot difference;
    − ( A_{g₁}(∇^{g₀}_X Y, Z) − A_{g₁'}(∇^{g₀}_X Y, Z) ).         -- (S₂) order-1 slot difference.
```

The principal arm (P) carries the second covariant gradient `∇₀² S` of the metric-difference section
(the covector difference `K_{g₁} − K_{g₁'}` is, under the realize-tie, the Koszul covector of the
section difference `S = T − T'`, by `covGrad_sub`), raised by the single cometric `♯_{g₁}`; it is the
order-2 PRINCIPAL the Ricci–DeTurck `C₂` linearization expands.  The operator-difference arm (O) is
order-`0` in `S` as a value: it splits, via the inverse-metric-difference multiplier
`gInvDiffRaisedEndo_eq_metricSharp_flatDiff` (for `♯_{g₁} − ♯_{g₁'}`, linear in `S(x)` as a value) and
the connection-difference cocycle `connDiff_cocycle` (for `∇^{g₁} − ∇^{g₁'} = connDiff g₁ g₁'`,
order-`≤ 1`), into the genuine endpoint coefficients acting on the endpoint development `∇^{g₁'} K_{g₁'}`
— the order-`0`/cross arm the Ricci/Lie arms package into `Rₘ`/`Lₘ`.  The cross and slot arms
(C, S₁, S₂) are the order-`1` `connDiff` couplings.  The operator coefficients (`♯_{g₁}`, `∇^{g₁}`, the
endpoint development of `K_{g₁'}`) are kept symbolic — they are the endpoint-dependent coefficients the
arms package afterward.  This is the value-level two-endpoint identity both the Ricci-arm telescope
(`ricciTensor_sub_eq_palatini_telescope`) and the Lie arm consume. -/
theorem covDerivConnDiff_diff_endpoint_graded
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x
        - covDerivConnDiff (I := I) g₀ g₁' (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
          - inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        + (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x)))
            - inverseMetricSharpFib (I := I) g₁' x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (inverseMetricSharpFib (I := I) g₁' x
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)) (X x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)) := by
  rw [covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁ X Y Z x,
      covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁' X Y Z x]
  abel

/-! ## The corrected order-2 combined three-trace coefficient field `R₂`

The numerically-verified order-2 PRINCIPAL of the Ricci–DeTurck connection-difference is NOT the bare
cometric double trace of the two leading covariant slots `{0, 1}`.  Writing
`D = iteratedCovGrad g₀ 0 2 2 S` for the second covariant gradient of the metric-difference section `S`
— a `(0, 4)`-tensor with slots `(deriv2, deriv1, S1, S2)` — and `g₁^{·}` for the cometric raise
`cometricLmodel g₁`, the traced principal is
```
P(Z, Y)
  = ½ ∑ₖ ( D(♯b^k, Z, Y, b_k) + D(♯b^k, Y, Z, b_k) − D(♯b^k, b_k, Z, Y) ),
```
a COMBINED three-trace: the bare double trace `cometricDoubleTrace` captures ONLY the third Koszul term
`−D(♯b^k, b_k, Z, Y)` (the `{0, 1}`-slot trace), while the first two Koszul terms
`D(♯b^k, Z, Y, b_k) + D(♯b^k, Y, Z, b_k)` are `{0, 3}`-cross traces (`T₀₃`).  This section builds the
combined operator `R₂` realising `P` as the `appCc`/`unitModel` read-off of `D`, the order-2 building
block the Ricci-arm eval-matching (`deTurckRicciArm_appCc_graded`) consumes.

The `{0, 3}`-cross trace is the `{0, 1}`-cometric double trace of the slot-reindexed tensor: the
permutation `koszulSlotPerm` of `Fin 4` (fixing slot `0`, cycling `1 → 2 → 3 → 1`) carries the trace pair
`{0, 3}` onto the leading pair `{0, 1}` while leaving the output indices `(Z, Y)` in the trailing slots,
so `T₀₃(D)(Z, Y) = modelDoubleTrace 2 ♯ (domDomCongr koszulSlotPerm D) (Z, Y)`. -/

/-- The slot permutation of `Fin 4` that carries the `{0, 3}`-trace pair onto the leading `{0, 1}` pair:
it fixes slot `0` (the cometric-raised slot) and cycles `1 → 2 → 3 → 1` so that, after the reindexing
`domDomCongr koszulSlotPerm`, the original `{0, 3}` slots become the leading `{0, 1}` trace pair and the
original `{1, 2}` slots (carrying the output indices `Z, Y`) become the trailing `{2, 3}` output slots. -/
def koszulSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.Perm.decomposeFin.symm (0, finRotate 3)

set_option linter.unusedSectionVars false in
/-- The model-fibre value of `koszulSlotPerm` on the four slots: it fixes `0` and cycles
`1 ↦ 2 ↦ 3 ↦ 1`. -/
private theorem koszulSlotPerm_apply :
    koszulSlotPerm 0 = 0 ∧ koszulSlotPerm 1 = 2 ∧ koszulSlotPerm 2 = 3 ∧ koszulSlotPerm 3 = 1 := by
  unfold koszulSlotPerm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The combined model three-trace operator of the corrected order-2 principal.**

For a model cometric raise `L : Tensor0SModel 1 → E` (`L = cometricLmodel g₁ x`), the combined
three-trace `(0, 4) → (0, 2)` model operator
```
combinedTrace42Model L D (Z, Y)
  = ½ ( modelDoubleTrace 2 L (domDomCongr koszulSlotPerm D) (Z, Y)        -- T₀₃^{Z,Y}
      + modelDoubleTrace 2 L (domDomCongr koszulSlotPerm D) (Y, Z)        -- T₀₃^{Y,Z}
      − modelDoubleTrace 2 L D (Z, Y) ),                                  -- {0,1}-double trace
```
assembled from the `{0, 1}`-cometric double trace `modelDoubleTrace` (the third Koszul term) and its
slot-reindexed forms (the two `{0, 3}`-cross Koszul terms).  This is the model reading of the order-2
coefficient `R₂`. -/
noncomputable def combinedTrace42Model
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap)
      + (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((modelDoubleTrace (E := E) 2 L).comp
            ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
              koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap))
      - modelDoubleTrace (E := E) 2 L)

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the combined model three-trace.**  On a `Fin 2`-tuple `m = (Z, Y)`,
the combined three-trace reads off the sum of the two `{0, 3}`-cross Koszul traces minus the
`{0, 1}`-double trace, halved:
```
combinedTrace42Model L D m
  = ½ ∑ₖ ( D(L b^k, m 0, m 1, b_k) + D(L b^k, m 1, m 0, b_k) − D(L b^k, b_k, m 0, m 1) ).
```
Definitional through `modelDoubleTrace_apply` and the slot-reindexing `domDomCongr koszulSlotPerm`. -/
theorem combinedTrace42Model_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![m 0, m 1, (Module.finBasis ℝ E) k])
            + D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![m 1, m 0, (Module.finBasis ℝ E) k])
            - D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) m))) := by
  classical
  obtain ⟨hp0, hp1, hp2, hp3⟩ := koszulSlotPerm_apply
  -- The `domDomCongrₗᵢ` continuous-linear-equiv reading reduces to the bare `domDomCongr` reindex.
  have hcongr_eq : ∀ (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr koszulSlotPerm D' := by
    intro D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  have hswap_eq : ∀ (T : Tensor0SBundle.Tensor0SModel 2 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap T =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) T := by
    intro T
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  -- Tuple reading of the `{0, 3}`-cross trace `T₀₃` on a `Fin 2`-tuple `mm`.
  have hT03 : ∀ (mm : Fin 2 → E),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) mm =
        ∑ k : Fin (Module.finrank ℝ E),
          D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
              ![mm 0, mm 1, (Module.finBasis ℝ E) k]) := by
    intro mm
    rw [modelDoubleTrace_apply (E := E) 2 L _ mm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    have hperm : koszulSlotPerm j = ![(0 : Fin 4), 2, 3, 1] j := by
      fin_cases j
      · exact hp0
      · exact hp1
      · exact hp2
      · exact hp3
    rw [hperm]
    fin_cases j <;> rfl
  rw [combinedTrace42Model]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  -- The third (un-permuted) term: the bare `{0, 1}`-double trace.
  rw [modelDoubleTrace_apply (E := E) 2 L D m]
  -- The first {0,3}-cross term, through `domDomCongr koszulSlotPerm`.
  rw [ContinuousLinearMap.comp_apply, hcongr_eq, hT03 m]
  -- The second {0,3}-cross term: output swap then `T₀₃` at the swapped tuple `(m 1, m 0)`.
  rw [ContinuousLinearMap.comp_apply, hswap_eq, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousLinearMap.comp_apply, hcongr_eq, hT03 (fun i => m (Equiv.swap (0 : Fin 2) 1 i))]
  -- Combine the three sums termwise.
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- Only the second `{0, 3}`-cross term differs: its tuple `(m (swap 0), m (swap 1)) = (m 1, m 0)`.
  have htuple : (![m (Equiv.swap (0 : Fin 2) 1 0), m (Equiv.swap (0 : Fin 2) 1 1),
        (Module.finBasis ℝ E) k] : Fin 3 → E) = ![m 1, m 0, (Module.finBasis ℝ E) k] := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [htuple]

/-! ## The corrected order-2 coefficient field `R₂` as a smooth `(4, 2)`-operator field -/

/-- **The fibrewise corrected order-2 combined three-trace operator.**  At a base point `x`, the
combined three-trace `combinedTrace42Model (cometricLmodel g₁ x)` of the two leading-plus-trailing
covariant slots, transported through the fibre/model continuous-linear equivalences to a fibre operator
`Tensor0SSpace 4 I x →L Tensor0SSpace 2 I x`.  This is the order-2 PRINCIPAL coefficient: it contracts a
`(0, 4)`-tensor `D = ∇₀² S` (slots `(deriv2, deriv1, S1, S2)`) by the COMBINED cometric `g₁⁻¹` trace
`½(T₀₃^{Z,Y} + T₀₃^{Y,Z} − cometricDoubleTrace)` of the corrected Koszul principal.  It depends on `g₁`
only through the SMOOTH cometric Hom-section `inverseMetricSharpField`; NO chart-selected ambient frame. -/
noncomputable def ricciArmPrincipalCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- The model image of `ricciArmPrincipalCoeffFib` is the combined three-trace `combinedTrace42Model`
against the cometric reading of `g₁`.  Definitional, since `Tensor0SSpace.toModel` is the identity
equivalence. -/
@[simp] theorem ricciArmPrincipalCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffFib (I := I) g₁ x D) =
      combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the corrected order-2 coefficient field.**  The fibre field
`x ↦ ricciArmPrincipalCoeffFib g₁ x` is a smooth section of the `(4, 2)`-tensor bundle.  Its smoothness
routes through the globally-smooth cometric Hom-section `inverseMetricSharpField`: by
`contMDiff_clm_section_of_pointwise` it reduces, on a smooth `(0, 4)`-field `Y`, to the model
combination `½(T₀₃ + (output swap) T₀₃ − {0,1}-trace)`, each summand a `±1`/output-reindexed value of
the SMOOTH rank-generic cometric double-trace field `cometricDoubleTraceFib g₁ 2`
(`cometricDoubleTraceFib_contMDiff`) applied to a constant-reindexed smooth `(0, 4)`-field.  NO
chart-selected, non-`∇₀`-parallel ambient frame enters.  Non-vacuous (the genuine combined cometric
trace field, smooth, not the zero field). -/
theorem ricciArmPrincipalCoeffFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffFib (I := I) g₁ x)
  intro Y
  -- The constant model slot-reindex carrying `{0, 3}` onto the leading `{0, 1}` trace pair.
  let κ : Equiv.Perm (Fin 4) := koszulSlotPerm
  -- A constant model slot-reindex of a smooth `(0, d)`-tensor field is smooth: its trivialised
  -- basis coordinate at `τ` is the `(τ ∘ ρ)`-coordinate of the original (a relabeling), through
  -- `contMDiff_multilinearSection_iff_coord` (the proof of `domDomCongrField_contMDiff`, inline on a
  -- bare `Tensor0SSpace` section to avoid the `SmoothCcTensor 0 d` vs `Tensor0SModel d` packaging).
  have hreindex : ∀ {d : ℕ} (ρ : Equiv.Perm (Fin d))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro d ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  -- The smooth `(0, 4)`-section reindexed by `κ`.
  have hYκ := hreindex κ (fun x => Y x) Y.contMDiff
  -- The smooth `{0,1}`-double-trace of `Yκ`: the smooth field `cometricDoubleTraceFib g₁ 2` applied.
  have hT03field := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYκ
  -- The smooth `{0,1}`-double-trace of `Y` itself.
  have hCDTfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) Y.contMDiff
  -- The output swap of the first cross trace.
  have hswapfield := hreindex (Equiv.swap (0 : Fin 2) 1)
    (fun x => (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        cometricDoubleTraceFib (I := I) g₁ 2 x)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
    hT03field
  -- Assemble: `R₂Fib (Y x) = ½ • (T₀₃ + swap T₀₃ − CDT)` at the fibre level.
  have hcomb := ((hT03field.add_section hswapfield).sub_section hCDTfield).const_smul_section
    (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)
  -- The fibre identity: `R₂Fib (Y x) = ½ • ((T₀₃ x + swap T₀₃ x) − CDT x)`.
  have hfib : ricciArmPrincipalCoeffFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        ((((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr κ
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
            + Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
                          Tensor0SBundle.Tensor0SSpace 2 I x from
                        cometricDoubleTraceFib (I := I) g₁ 2 x)
                      (Tensor0SBundle.Tensor0SSpace.ofModel
                        (ContinuousMultilinearMap.domDomCongr κ
                          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x) (Y x)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42Model]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  -- Lift the fibre identity to the total-space equality.
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

/-- **The corrected order-2 coefficient field `R₂` as a smooth compactly-supported `(4, 2)`-tensor.**
The fibre value at `x` is `ricciArmPrincipalCoeffFib g₁ x` (smooth by
`ricciArmPrincipalCoeffFib_contMDiff`); on the closed manifold it has compact support.  This is the
order-2 PRINCIPAL coefficient operator field of the Ricci–DeTurck connection-difference: the COMBINED
three-trace `½(T₀₃^{Z,Y} + T₀₃^{Y,Z} − cometricDoubleTrace)` of the corrected Koszul principal (NOT the
bare `{0, 1}`-cometric double trace), whose `appCc`-action on `D = ∇₀² S` reproduces the traced principal
`P` (`ricciArmPrincipalCoeff_appCc_eq_combinedTrace`). -/
noncomputable def ricciArmPrincipalCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmPrincipalCoeff g₀ g₁` at `x` is the fibre operator
`ricciArmPrincipalCoeffFib g₁ x`.  Definitional. -/
@[simp] theorem ricciArmPrincipalCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x) := rfl

/-! ## The corrected order-2 connector: the `appCc`-action of `R₂` is the combined three-trace `P` -/

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the corrected order-2 coefficient `R₂` is the combined
three-trace principal `P`.**

For any smooth `(0, 4)`-tensor field `W` (in the consumer `W = iteratedCovGrad g₀ 0 2 2 (T − T')` the
second covariant gradient of the metric-difference section), the `unitModel` read-off of the operator-field
action `appCc g₀ 4 2 R₂ W` at `x` on a tangent pair `v` is the combined three-trace `P` of the unit-form
`D = unitModel g₀ 4 W x` of `W` against the cometric `g₁⁻¹`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂ W) x v
  = ½ ∑ₖ ( D(♯b^k, v 0, v 1, b_k) + D(♯b^k, v 1, v 0, b_k) − D(♯b^k, b_k, v 0, v 1) ),
  ♯ = cometricLmodel g₁ x,  D = unitModel g₀ 4 W x.
```
This is the corrected order-2 PRINCIPAL building block: the combined three-trace `R₂` realises the traced
Palatini principal `P = ∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K))i` (the first two `{0, 3}`-cross Koszul terms plus
the `{0, 1}`-double-trace term), NOT the bare cometric double trace.  It composes `appCc_toSection`
(`(R₂ x).comp (W x)`), the definitional identity `R₂ x = ricciArmPrincipalCoeffFib g₁ x` with model image
`combinedTrace42Model (cometricLmodel g₁ x)` (`ricciArmPrincipalCoeffFib_toModel`), and the read-off
`combinedTrace42Model_apply`. -/
theorem ricciArmPrincipalCoeff_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) := by
  -- `unitModel (appCc R₂ W) x v = toModel ((R₂ x).comp (W x) (unit)) v`.
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeffFib_toModel,
    combinedTrace42Model_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

/-! ## The corrected order-2 match (the building block the Ricci arm consumes)

The corrected order-2 PRINCIPAL building block: the traced principal `P` (the `{0, 3}`-cross plus the
`{0, 1}`-double-trace combined three-trace) is the `appCc`/`unitModel` read-off of the combined coefficient
`R₂ = ricciArmPrincipalCoeff g₀ g₁` on the second covariant gradient `W₂ = iteratedCovGrad g₀ 0 2 2 (T − T')`
of the metric-difference section.  Stated as the corrected order-2 building block the Ricci arm's
eval-matching `deTurckRicciArm_appCc_graded` (free `R₂` existential) instantiates: for the perturbation
difference `S = T − T'`, the order-2 PRINCIPAL coefficient `R₂` realises the corrected principal trace, with
the order-`0`/`1` lower-order remainder carried by the sibling coefficients `R₀, R₁` (not discharged here —
the order-2 PRINCIPAL is the deliverable of this node). -/

set_option linter.unusedSectionVars false in
/-- **The corrected order-2 match (the order-2 PRINCIPAL building block).**

For the perturbation difference `S` (in the consumer `S = T − T'`), the `appCc`/`unitModel` read-off of the
combined coefficient `R₂ = ricciArmPrincipalCoeff g₀ g₁` on the second covariant gradient
`W₂ = iteratedCovGrad g₀ 0 2 2 S` is the corrected order-2 PRINCIPAL combined three-trace `P` of the unit
form `D = unitModel g₀ 4 W₂ x` against the cometric `g₁⁻¹`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂ (iteratedCovGrad g₀ 0 2 2 S)) x v
  = ½ ∑ₖ ( D(♯b^k, v 0, v 1, b_k) + D(♯b^k, v 1, v 0, b_k) − D(♯b^k, b_k, v 0, v 1) ),
  ♯ = cometricLmodel g₁ x,  D = unitModel g₀ 4 (iteratedCovGrad g₀ 0 2 2 S) x.
```
This is exactly the corrected order-2 coefficient the Ricci-arm grading `deTurckRicciArm_appCc_graded`
(free `R₂` existential) provides; the order-`0`/`1` lower-order corrections are the sibling coefficients
`R₀, R₁` carried alongside.  It is the specialization of `ricciArmPrincipalCoeff_appCc_eq_combinedTrace` to
the order-2 iterated covariant gradient `W₂`.

**What is proven here:** the `appCc`/`unitModel` read-off of the genuinely-built combined-three-trace
coefficient `R₂` is the EXPLICIT corrected-principal trace formula `P` (the `{0, 3}`-cross plus the
`{0, 1}`-double trace, the structure the dim-`4` random-SPD numeric check confirms is the order-2 trace —
NOT the bare cometric double trace, which captures only the third Koszul term).  The remaining identification
of this explicit `P` with the SP2-endpoint Palatini traced principal `∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K))i`
(through the cotangent-cov ↔ tensor-cov-deriv connector `cotangentCov_eq_tensorCovDerivAt_ccTensor01`, the
metric-compat parallelism `inverseMetricSharpField_covGrad_eq_zero`, the covGrad bridge
`connDiffSection_covGrad_eq_covDerivConnDiff`, and the Palatini frame-trace) is the CARRIED connector
residual the Ricci-arm eval-matching assembles; it is not discharged in this node, whose deliverable is the
corrected order-2 coefficient `R₂` and its `appCc`-read-off. -/
theorem covDerivConnDiff_tracedPrincipal_eq_appCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) :=
  ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v

/-! ## The second-order Koszul covariant-gradient bridge (the SP2-endpoint deep prerequisite) -/

/-- The scalar `(0, 3)` evaluation field of an abstract `(0, 3)`-tensor section `V` on three smooth
vector fields `A, B, C`: `b ↦ V(b)(A b, B b, C b)`. -/
private def triEvalFn (V : Π b : M, Tensor0SSpace 3 I b)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SSpace.toModel (V b) (Fin.cons (A b) (Fin.cons (B b) ![C b]))

set_option linter.unusedSectionVars false in
/-- The partial evaluation `y ↦ curriedSection W y (Y y)` of a `(0, s + 1)`-tensor section `W`
differentiable at `x` against a smooth vector field `Y` is a `(0, s)`-tensor section differentiable
at `x`. -/
private lemma triMDiffAt_curried
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

-- The abstract (0,3) Leibniz-defect: 3-slot peel.

set_option linter.unusedSectionVars false in
/-- **The abstract `(0, 3)`-tensor covariant-derivative Leibniz-defect (tuple form).** For an abstract
`(0, 3)`-tensor section `V` differentiable at `x`, a direction `v`, and three smooth vector fields
`A, B, C`, the model value of `∇³_v V` read on the cons-tuple `(A x, B x, C x)` decomposes by the
covariant Leibniz product rule applied to the three slots, with `∇₀ = LeviCivita g₀`:
```
toModel(∇³_v V x)(A x, B x, C x)
  = ∂_v (b ↦ V(b)(A b, B b, C b))
    − V(x)(∇₀_v A, B x, C x) − V(x)(A x, ∇₀_v B, C x) − V(x)(A x, B x, ∇₀_v C).
```
The three-fold leading-slot peel `tensor0SCovariantDerivative_succ_consEval_peel`. -/
private theorem tensor0SCovariantDerivative03_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 3 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 3 V x)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun V x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x])) =
      directionalDeriv (I := I) (triEvalFn (I := I) (M := M) V A B C) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
  classical
  set W₂ : Π b : M, Tensor0SSpace 2 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (A b) with hW₂
  have hW₂_mdiff : TensorSectionMDiffAt (I := I) 2 W₂ x :=
    triMDiffAt_curried (I := I) (M := M) 2 V hV A
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M W₂ b (B b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    triMDiffAt_curried (I := I) (M := M) 1 W₂ hW₂_mdiff B
  -- Peel slot A off the rank-3 derivative.
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 2 V hV A v (Fin.cons (B x) ![C x])
  -- Peel slot B off the rank-2 derivative of W₂.
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 W₂ hW₂_mdiff B v ![C x]
  -- Peel slot C off the rank-1 derivative of W₁.
  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff C v (fun i => Fin.elim0 i)
  -- The rank-0 base reads as the directional derivative of the scalar tri-evaluation.
  have hbase : Tensor0SSpace.toModel
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)).toFun
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I) (triEvalFn (I := I) (M := M) V A B C) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) =
        triEvalFn (I := I) (M := M) V A B C := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0)
            (T := W₁)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
      change Tensor0SSpace.toModel (W₁ b) (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [hW₁]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
      rw [hW₂]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (A b))
        (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := V b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
      rw [triEvalFn]
      apply congrArg
      funext k
      fin_cases k <;> rfl
    rw [hscalar]
  -- Correction slot C: reads W₁ x on cons-tuple, uncurries through W₂ x then V x.
  have hcorrC : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ x (B x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ x) (v0 := B x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  -- Correction slot B: reads W₂ x on cons-tuple, uncurries through V x.
  have hcorrB : Tensor0SSpace.toModel (W₂ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
          (Fin.cons (C x) (fun i => Fin.elim0 i))) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x])) := by
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  -- Assemble.
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (A y)) = W₂ from rfl]
  rw [hpeel2]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M W₂ y (B y)) = W₁ from rfl]
  rw [show (![C x] : Fin 1 → E) = Fin.cons (C x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel3, hbase, hcorrC, hcorrB]
  have hfin1 : ∀ (u : TangentSpace I x), (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons u (fun i => Fin.elim0 i) := by
    intro u; funext k; refine Fin.cases rfl (fun j => j.elim0) k
  rw [hfin1 ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v),
      hfin1 (C x)]
  ring

set_option linter.unusedSectionVars false in
/-- The unit-evaluated `(0, 3)`-field of the FIRST covariant gradient `covGrad g₀ 0 2 S`, as an abstract
`(0, 3)`-tensor section (`unitEvalSection` of `covGrad g₀ 0 2 S`). -/
private def covGrad2UnitV (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    Π b : M, Tensor0SSpace 3 I b :=
  unitEvalSection (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)

set_option linter.unusedSectionVars false in
/-- `covGradEval g₀ S A B C` is the `triEvalFn` of the unit-evaluated first covariant gradient. -/
private lemma covGradEval_eq_triEvalFn (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) =
      triEvalFn (I := I) (M := M) (covGrad2UnitV (I := I) (M := M) g₀ S) A B C := rfl

set_option linter.unusedSectionVars false in
/-- The unit-evaluated first covariant gradient is differentiable at every point. -/
private lemma covGrad2UnitV_mdiff (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    TensorSectionMDiffAt (I := I) 3 (covGrad2UnitV (I := I) (M := M) g₀ S) x := by
  have h := contMDiff_unitEvalSection (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)
  exact (h x).mdifferentiableAt (by simp)

set_option linter.unusedSectionVars false in
/-- The abstract `(0, 3)` covariant derivative of the unit-evaluated first covariant gradient `V` is the
unit-evaluation of the SECOND covariant gradient `iteratedCovGrad g₀ 0 2 2 S`, read on the cons-tuple
`(v, m)`: `toModel(∇³_v V x)(m) = unitModel g₀ 4 (∇₀²S) x (v, m)`. -/
private lemma covGrad2UnitV_nabla3_eq_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x) (m : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v) m =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x (Fin.cons v m) := by
  classical
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 2 S =
      covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hunit : unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x := rfl
  rw [unitModel, hunit, hiter,
    covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x (Fin.cons v m)]
  have hvt : Matrix.vecTail (Fin.cons v m) = m := by
    funext k; simp only [Matrix.vecTail, Function.comp]; rw [Fin.cons_succ]
  have h0 : (Fin.cons v m : Fin 4 → TangentSpace I x) 0 = v := rfl
  rw [h0, hvt, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x v,
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x v]
  rfl

set_option linter.unusedSectionVars false in
/-- **The directional-derivative Leibniz defect of the first covariant-gradient evaluation.** The
directional derivative of `b ↦ covGradEval g₀ S A B C b` along `v` is the unit-evaluation of the SECOND
covariant gradient `iteratedCovGrad g₀ 0 2 2 S` on `(v, A x, B x, C x)`, plus the three order-1 frame
corrections (the first covariant gradient applied to the frame derivatives `∇₀_v A`, `∇₀_v B`, `∇₀_v C`):
```
∂_v (covGradEval g₀ S A B C)
  = unitModel g₀ 4 (∇₀²S) x (v, A x, B x, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(∇₀_v A, B x, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(A x, ∇₀_v B, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(A x, B x, ∇₀_v C).
```
This is `tensor0SCovariantDerivative03_consEval_leibnizDefect` for the unit-evaluated first covariant
gradient `V`, with the principal `∇³_v V` read off as the second covariant gradient
(`covGrad2UnitV_nabla3_eq_iteratedCovGrad`). -/
private lemma covGradEval_directionalDeriv
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x v =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons v (Fin.cons (A x) (Fin.cons (B x) ![C x])))
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => A b) x v, B x, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, (LeviCivita (I := I) g₀).toFun (fun b => B b) x v, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, B x, (LeviCivita (I := I) g₀).toFun (fun b => C b) x v] := by
  classical
  have hpeel := tensor0SCovariantDerivative03_consEval_leibnizDefect (I := I) (M := M) g₀
    (covGrad2UnitV (I := I) (M := M) g₀ S) (covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x) A B C v
  have hprin := covGrad2UnitV_nabla3_eq_iteratedCovGrad (I := I) (M := M) g₀ S x v
    (Fin.cons (A x) (Fin.cons (B x) ![C x]))
  rw [covGradEval_eq_triEvalFn (I := I) (M := M) g₀ S A B C]
  rw [show directionalDeriv (I := I) (triEvalFn (I := I) (M := M)
        (covGrad2UnitV (I := I) (M := M) g₀ S) A B C) x v =
      Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v]))
      from by rw [hpeel]; ring]
  rw [hprin]
  rfl

set_option linter.unusedSectionVars false in
/-- The first covariant-gradient evaluation `b ↦ covGradEval g₀ S A B C b` is differentiable at `x`:
the unit-evaluated first covariant gradient is a smooth `(0, 3)`-section, curried against the three
smooth fields `A, B, C`, whose scalar evaluation is `covGradEval`. -/
private lemma covGradEval_mdifferentiableAt
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x := by
  classical
  have h3 := covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x
  have h2 := triMDiffAt_curried (I := I) (M := M) 2 (covGrad2UnitV (I := I) (M := M) g₀ S) h3 A
  have h1 := triMDiffAt_curried (I := I) (M := M) 1
    (fun y : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) y (A y))
    h2 B
  have h0 := triMDiffAt_curried (I := I) (M := M) 0
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) z (A z))
      y (B y)) h1 C
  have hscalar := (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section (I := I) (M := M)
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M
          (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) (x := x)).mpr h0
  have hfun : Tensor0SNabla.scalarFn I M
      (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) =
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) := by
    funext b
    set V₃ : Π y : M, Tensor0SSpace 3 I y := covGrad2UnitV (I := I) (M := M) g₀ S with hV₃
    set W₂ : Π y : M, Tensor0SSpace 2 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M V₃ z (A z) with hW₂
    set W₁ : Π y : M, Tensor0SSpace 1 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M W₂ z (B z) with hW₁
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
      (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V₃ b (A b))
      (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V₃)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V₃ b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
    rw [hV₃, covGradEval, covGrad2UnitV, unitEvalSection]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  rw [hfun] at hscalar
  exact hscalar

set_option linter.unusedSectionVars false in
/-- **The second-order Koszul covariant-gradient bridge (the SP2-endpoint deep prerequisite).**

The `g₀`-cotangent covariant derivative of the half-Koszul covector field
`b ↦ cotangentToCLM (koszulCovGradCovec g₀ g₁ Z Y b)`, taken in direction `X` and read (via the
`g₁`-flat round trip `cotangentToDual ∘ dualToCotangent`) on a test vector `ζ`, is the half-Koszul
combination of the SECOND covariant gradient `iteratedCovGrad g₀ 0 2 2 S` (the order-2 PRINCIPAL the
Ricci–DeTurck `C₂` linearization expands) PLUS the order-1 FRAME remainder built from the FIRST
covariant gradient `covGrad g₀ 0 2 S` applied to the `∇₀`-frame derivatives `∇₀_X Z`, `∇₀_X Y`:
```
cotangentToDual (∇^{g₀}_K (cotangentToCLM K_S))(X)(ζ)
  = ½ ( D(X, Z, Y, ζ) + D(X, Y, Z, ζ) − D(X, ζ, Z, Y) )                 -- order-2 PRINCIPAL, D = ∇₀²S
    + ½ ( C(∇₀_X Z, Y, ζ) + C(Z, ∇₀_X Y, ζ)
        + C(∇₀_X Y, Z, ζ) + C(Y, ∇₀_X Z, ζ)
        − C(ζ, ∇₀_X Z, Y) − C(ζ, Z, ∇₀_X Y) ),                          -- order-1 FRAME remainder, C = ∇₀S
```
where `D = unitModel g₀ 4 (∇₀²S)`, `C = unitModel g₀ 3 (∇₀S)`, and `∇₀_X Z = (LeviCivita g₀) Z x (X x)`.

The frame remainder does NOT vanish (a `dim`-`3`/`4` random numeric check confirms the six terms do not
cancel, since the first covariant gradient is not symmetric in its three slots); it is the order-1
lower-order correction the connector absorbs.  The `ζ`-slot frame corrections of the three Koszul terms
cancel exactly against the `−θ(∇₀_X ζ)` term of the cotangent Leibniz rule (the cotangent covariant
derivative freezes the test vector), leaving only the `Z`/`Y`-slot frame corrections above.

The route is the second covariant Leibniz peel: `cotangentCov (LeviCivita g₀)` reduces, via
`cotangentCovAt_apply_of_diff`, to the Leibniz defect `cotangentScalar` (`∂_X(θ(ζ)) − θ(∇₀_X ζ)`);
under the metric-difference hypothesis `hbil` each `θ(ζ)` pairing is the half-Koszul combination of the
first covariant-gradient evaluation `covGradEval` (`koszulCovGradCovec_dual_apply_covGrad`), whose
directional derivative is the second covariant gradient plus its three frame corrections
(`covGradEval_directionalDeriv`). -/
theorem koszulCovGradCovec_covDeriv_eq_secondCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I)
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x))) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![X x, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)]) := by
  classical
  rw [cotangentToDual_apply, dualToCotangent_apply]
  -- The covector field is cotangent-differentiable at `x`.
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x
  -- Smooth extensions of `X x` and `ζ`.
  let ζf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩
  have hζfx : ζf x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  have hXfx : Xf x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hXfmd := smoothExtensionTangent_mdiff (I := I) x (X x) x
  have hζfmd := smoothExtensionTangent_mdiff (I := I) x ζ x
  -- Reduce the cotangent covariant derivative to the Leibniz defect `cotangentScalar`.
  have hcov : ((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun)
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (fun b => Xf b) (fun b => ζf b) := by
    rw [cotangentCov_toFun, cotangentCovFun_apply, ← hXfx, ← hζfx]
    exact cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hXfmd hζfmd
  rw [ContinuousLinearMap.coe_coe, hcov, cotangentScalar_def]
  -- The pairing `b ↦ θ_b(ζf_b)` is the half-Koszul combination of the first covariant gradient.
  have hpairfun : (fun b : M => (cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =
      (fun b : M => (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S Z Y ζf b
          + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
          - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
    funext b
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y ζf b
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b) =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) (ζf b) from rfl]
    rw [h]
  -- Differentiate the half-Koszul pairing: linearity + the three `covGradEval` directional derivatives.
  have hext : extDerivFun (I := I)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) =
      (1 / 2 : ℝ) *
        (directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Z Y ζf b) x (Xf x)
          + directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Y Z ζf b) x (Xf x)
          - directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S ζf Z Y b) x (Xf x)) := by
    have hf := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Z Y ζf x
    have hg := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Y Z ζf x
    have hh := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S ζf Z Y x
    -- The pairing function has the half-Koszul `HasMFDerivAt` derivative at `x`.
    have hmf0 := (((hf.hasMFDerivAt.add hg.hasMFDerivAt).sub hh.hasMFDerivAt).const_smul
      (1 / 2 : ℝ))
    have heq : (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =ᶠ[nhds x]
        ((1 / 2 : ℝ) • (fun b : M =>
          covGradEval (I := I) (M := M) g₀ S Z Y ζf b
            + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
            - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
      filter_upwards [Filter.univ_mem] with b _
      rw [Pi.smul_apply, smul_eq_mul]
      exact congrFun hpairfun b
    have hmf := hmf0.congr_of_eventuallyEq heq
    change mfderiv I 𝓘(ℝ, ℝ)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) = _
    rw [hmf.mfderiv]
    rfl
  rw [hext, hXfx]
  -- The `θ(∇₀_X ζf)` term: the half-Koszul evaluation on the frame derivative `∇₀_X ζf`.
  have hθext : (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x))
        ((LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)) =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, Y x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![Y x, Z x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x), Z x, Y x]) := by
    set w : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x) with hw
    -- Extend `w` to a smooth field; the Koszul covector evaluation on `w` reads via `_dual_apply_covGrad`.
    let wf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x w, smoothExtensionTangent_contMDiff (I := I) x w⟩
    have hwfx : wf x = w := smoothExtensionTangent_eq (I := I) x w
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y wf x
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) w =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x) (wf x) from by
      rw [hwfx]; rfl]
    rw [h]
    -- Each `covGradEval … wf … x` reads as `unitModel g₀ 3 (covGrad g₀ 0 2 S) x` on the vector `w`.
    have hcg : ∀ (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
        covGradEval (I := I) (M := M) g₀ S A B wf x =
          unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![A x, B x, w] := by
      intro A B
      rw [covGradEval, unitModel, hwfx]; rfl
    have hcg2 : covGradEval (I := I) (M := M) g₀ S wf Z Y x =
        unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![w, Z x, Y x] := by
      rw [covGradEval, unitModel, hwfx]; rfl
    rw [hcg Z Y, hcg Y Z, hcg2]
  rw [hθext]
  -- Expand the three covGradEval directional derivatives (principal + frame).
  rw [covGradEval_directionalDeriv (I := I) (M := M) g₀ S Z Y ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S Y Z ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S ζf Z Y x (X x)]
  rw [hζfx]
  -- Normalize the principal cons-tuples to matrix notation, then the ζ-slot frame corrections cancel.
  have ht1 : (Fin.cons (X x) (Fin.cons (Z x) (Fin.cons (Y x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Z x, Y x, ζ] := by funext k; fin_cases k <;> rfl
  have ht2 : (Fin.cons (X x) (Fin.cons (Y x) (Fin.cons (Z x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Y x, Z x, ζ] := by funext k; fin_cases k <;> rfl
  have ht3 : (Fin.cons (X x) (Fin.cons ζ (Fin.cons (Z x) ![Y x])) : Fin 4 → TangentSpace I x) =
      ![X x, ζ, Z x, Y x] := by funext k; fin_cases k <;> rfl
  rw [ht1, ht2, ht3]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
