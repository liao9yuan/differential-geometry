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

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
