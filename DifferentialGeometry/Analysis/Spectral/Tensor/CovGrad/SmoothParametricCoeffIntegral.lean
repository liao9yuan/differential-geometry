import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference

/-!
# The fibre Bochner path integral of a smooth operator-coefficient family

For a closed smooth Riemannian manifold `(M, g₀)`, this file builds the **general parametric
Bochner integral tool** behind the Ricci–DeTurck linearization's path-integral coefficient
construction: it integrates a smooth family `Φ : ℝ → SmoothCcTensor g₀ r s` of operator-coefficient
fields over `[0, 1]` *pointwise in the fibre*, producing a single smooth coefficient field, and
records that the integral commutes with the `appCc`/`unitModel` read-off.

Each fibre `TensorRSSpace r s I x = Tensor0SSpace r I x →L Tensor0SSpace s I x` is finite-dimensional,
so the pointwise interval Bochner integral is well defined.  Working through the model-fibre coordinate
`TensorRSSpace.toModel` (which identifies the fibre with the fixed Banach space
`TensorRSModel r s ℝ E`), the integral `∫ t in 0..1, (Φ t).toModel x dt` is the ordinary interval
Bochner integral in that fixed space; `TensorRSSpace.ofModel` transports it back to the fibre.  Its
smoothness in the base point follows from the *joint* `(s, x)`-smoothness of the family by
differentiation under the integral sign; on the closed manifold the resulting section has compact
support automatically.

## The general tool

* `pathIntegralCoeffField Φ hΦ : SmoothCcTensor g₀ r s` — the pointwise fibre interval Bochner integral
  of the family, with model-fibre value `(pathIntegralCoeffField Φ hΦ).toSection x |>.toModel =
  ∫ t in 0..1, (Φ t).toSection x |>.toModel` (`pathIntegralCoeffField_toModel`);
* `pathIntegralCoeffField_appCc_eq` — the `appCc`/`unitModel` ↔ `intervalIntegral` swap: the operator
  read-off of the integrated coefficient on a fixed contracted tensor `W` equals the `s`-integral over
  `[0, 1]` of the per-`s` read-offs,
  ```
  unitModel g₀ s' (appCc g₀ r s' (pathIntegralCoeffField Φ hΦ) W) x v
    = ∫ s in 0..1, unitModel g₀ s' (appCc g₀ r s' (Φ s) W) x v ds.
  ```
  The fibrewise composition `A ↦ A.comp (W x)` and unit evaluation (whose model read-off is
  `toModel_tensorRS_apply`), the model read-off `toModel`, and the evaluation at the tangent tuple `v`
  are each *fixed* continuous-linear in the integrated coefficient, so the Bochner integral commutes
  with them in the fixed model fibre (`ContinuousLinearMap.intervalIntegral_apply` /
  `ContinuousLinearMap.intervalIntegral_comp_comm`).

## The posited smooth-parametric-integral kernel

The single analytic kernel is the *parametric-integral section smoothness*
`contMDiff_pathIntegralFib_of_jointContMDiff`: the pointwise interval Bochner integral of a jointly
`(s, x)`-smooth family of `(r, s)`-tensor bundle sections is again a smooth section.  This is
differentiation under the integral sign in charts, iterated to all orders; Mathlib packages the
first-order `HasFDerivAt`/`HasDerivAt`-under-integral lemmas but not the manifold-section `ContMDiff`
parametric integral, so it is posited here as the irreducible smooth-parametric-integral input and
recursed into downstream.  Its predicate genuinely constrains the constructed section to the fibrewise
integral (it is consumed only as the smoothness of that exact fibre formula). -/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The pointwise fibre interval-integral map of a coefficient family.**

The fibre value at `x` is the interval Bochner integral, computed in the fixed model fibre
`TensorRSModel r s ℝ E`, of the model-fibre family `t ↦ (Φ t).toSection x |>.toModel`, transported
back to the fibre by `TensorRSSpace.ofModel`.  This is the underlying map of `pathIntegralCoeffField`;
its base-point smoothness is supplied by the posited parametric-integral kernel and its compact support
by the closed manifold. -/
def pathIntegralFib (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (x : M) : TensorRSSpace r s I x :=
  TensorRSSpace.ofModel (∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)))

set_option linter.unusedSectionVars false in
/-- The model-fibre value of `pathIntegralFib` is the interval Bochner integral of the model-fibre
family, by `toModel ∘ ofModel = id`. -/
@[simp] lemma pathIntegralFib_toModel (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (x : M) :
    TensorRSSpace.toModel (pathIntegralFib (I := I) (M := M) g₀ r s Φ x) =
      ∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)) := by
  rw [pathIntegralFib, TensorRSSpace.toModel_ofModel]

/-- **Posited smooth-parametric-integral kernel.** For a family `Φ : ℝ → SmoothCcTensor g₀ r s` whose
joint `(s, x)`-data `(x, t) ↦ (Φ t).toSection x` is a smooth section of the `(r, s)`-tensor bundle in
the base point uniformly in the parameter, the pointwise interval Bochner integral
`x ↦ pathIntegralFib g₀ r s Φ x` is again a smooth section.  This is differentiation under the integral
sign in charts, iterated to all orders (the manifold-section `ContMDiff` parametric integral), the
irreducible analytic input recursed into downstream. -/
theorem contMDiff_pathIntegralFib_of_jointContMDiff
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s)
    (hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (pathIntegralFib (I := I) (M := M) g₀ r s Φ x)) :=
  sorry

/-- **The fibre Bochner path integral of a smooth operator-coefficient family.**

For a jointly `(s, x)`-smooth family `Φ : ℝ → SmoothCcTensor g₀ r s`, the pointwise interval Bochner
integral over `[0, 1]`, packaged as a smooth compactly-supported `(r, s)`-tensor.  The model-fibre value
is `(pathIntegralCoeffField Φ hΦ).toSection x |>.toModel = ∫ t in 0..1, (Φ t).toSection x |>.toModel`
(`pathIntegralCoeffField_toModel`). -/
def pathIntegralCoeffField (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s)
    (hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M => pathIntegralFib (I := I) (M := M) g₀ r s Φ x
      contMDiff_toFun :=
        contMDiff_pathIntegralFib_of_jointContMDiff (I := I) (M := M) g₀ r s Φ hjoint }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The fibre value of `pathIntegralCoeffField` is `pathIntegralFib`. -/
@[simp] lemma pathIntegralCoeffField_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s)
    (hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1)))
    (x : M) :
    (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ hjoint).toSection x =
      pathIntegralFib (I := I) (M := M) g₀ r s Φ x := rfl

set_option linter.unusedSectionVars false in
/-- The model-fibre value of `pathIntegralCoeffField` is the interval Bochner integral of the
model-fibre family. -/
@[simp] lemma pathIntegralCoeffField_toModel (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s)
    (hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1)))
    (x : M) :
    TensorRSSpace.toModel
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ hjoint).toSection x) =
      ∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)) := by
  rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]

/-- **The `appCc`/`unitModel` ↔ `intervalIntegral` swap for the fibre path integral.**

For a jointly smooth family `Φ : ℝ → SmoothCcTensor g₀ r s'` whose model-fibre family
`t ↦ (Φ t).toSection x |>.toModel` is continuous at every base point `x`, and a fixed contracted
`(0, r)`-tensor `W`, the `unitModel` read-off of the integrated coefficient
`pathIntegralCoeffField Φ` acting on `W` equals the `s`-integral over `[0, 1]` of the per-`s`
read-offs:
```
unitModel g₀ s' (appCc g₀ r s' (pathIntegralCoeffField Φ hΦ) W) x v
  = ∫ s in 0..1, unitModel g₀ s' (appCc g₀ r s' (Φ s) W) x v ds.
```
The fibrewise composition `A ↦ A.comp (W x)` and unit evaluation read off through
`toModel_tensorRS_apply`, the model read-off `toModel`, and the evaluation at the tangent tuple `v` are
each fixed continuous-linear in the integrated coefficient, so the Bochner integral commutes with each
step in the fixed model fibre (`ContinuousLinearMap.intervalIntegral_apply` for the operator
evaluation, `ContinuousLinearMap.intervalIntegral_comp_comm` for the tuple evaluation). -/
theorem pathIntegralCoeffField_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r s' : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s') (W : SmoothCcTensor g₀ 0 r)
    (hjoint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s' ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s' ℝ E)
        (E := fun z : M => TensorRSSpace r s' I z) p.1 ((Φ p.2).toSection p.1)))
    (hcont : ∀ x : M, Continuous (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)))
    (x : M) (v : Fin s' → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s'
        (appCc (I := I) (M := M) g₀ r s'
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ hjoint) W) x v =
      ∫ t in (0 : ℝ)..1,
        unitModel (I := I) (M := M) g₀ s' (appCc (I := I) (M := M) g₀ r s' (Φ t) W) x v := by
  -- Abbreviate the fixed contracted-then-unit-evaluated `(0, r)`-tensor `u = (W x) unit`.
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  -- The model-fibre family `t ↦ (Φ t).toModel x` is interval-integrable (continuous on `[0,1]`).
  have hIIm : IntervalIntegrable (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) volume 0 1 :=
    (hcont x).intervalIntegrable 0 1
  -- Reduce both read-offs to the model-operator action at `u` and evaluation at `v`
  -- (`unitModel (appCc Ψ W) x v = ((Ψ x).toModel (u.toModel)) v`, via `toModel_tensorRS_apply`).
  have key : ∀ Ψ : SmoothCcTensor g₀ r s',
      unitModel (I := I) (M := M) g₀ s' (appCc (I := I) (M := M) g₀ r s' Ψ W) x v =
        ((TensorRSSpace.toModel (Ψ.toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro Ψ
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r s' x (Ψ.toSection x) u]
  -- Rewrite the integrated coefficient's read-off to the model operator at `u`, evaluated at `v`.
  rw [show unitModel (I := I) (M := M) g₀ s'
        (appCc (I := I) (M := M) g₀ r s'
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ hjoint) W) x v =
      ((TensorRSSpace.toModel
            ((pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ hjoint).toSection x))
          (Tensor0SSpace.toModel u)) v from key _]
  -- The integrated coefficient's model fibre is the model interval integral.
  rw [pathIntegralCoeffField_toModel]
  -- Push the model-operator evaluation at `u.toModel` through the interval integral.
  rw [ContinuousLinearMap.intervalIntegral_apply hIIm (Tensor0SSpace.toModel u)]
  -- Push the tuple evaluation at `v` (the `Tensor0SModel s'`-CMM application CLM) through the integral.
  have hcontApp : Continuous (fun t : ℝ =>
      (TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) :=
    (ContinuousLinearMap.apply ℝ (Tensor0SModel s' ℝ E) (Tensor0SSpace.toModel u)).continuous.comp
      (hcont x)
  have hIIapp : IntervalIntegrable (fun t : ℝ =>
      (TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) volume 0 1 :=
    hcontApp.intervalIntegrable 0 1
  -- The RHS integrand is the per-`t` model read-off at `v` (via `key`).
  rw [show (fun t : ℝ => unitModel (I := I) (M := M) g₀ s'
          (appCc (I := I) (M := M) g₀ r s' (Φ t) W) x v) =
        (fun t : ℝ => ((TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) v) from
    funext (fun t => key (Φ t))]
  -- Both sides: the CMM evaluation at `v` commutes with the interval integral (apply-CLM commute).
  exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s' => E) ℝ v) hIIapp).symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
