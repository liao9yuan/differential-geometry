import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceCarrier
import DifferentialGeometry.Geometry.Connection.TensorNabla.Slot0CurryCovariantLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-!
# The coefficient-generic slot-operator carrier calculus

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
**coefficient-generic** engine of which the Ricci-trace carriers (`RicciTraceCarrier`,
`NablaRicciTraceCarrier`) are instances: the leading-slot operator-field calculus for an
*arbitrary* smooth endomorphism coefficient field `A : x ↦ (T_x M →L T_x M)`, together with the
leading-slot curry carrier of a `(0, t + 1)`-tensor section against a smooth tangent field.

## The leading-slot curry carrier

* `curryCc g t P X : SmoothCcTensor g 0 t` — the smooth compactly-supported `(0, t)`-tensor
  section obtained by currying the smooth `(0, t + 1)`-section `P` against the smooth tangent
  field `X` in the leading covariant slot, `(curryCc P X)(X₁, …, X_t) = P(X, X₁, …, X_t)`
  (`tensor0SAsRS`-wrapped bare curry of the unit-section evaluation).
* `tensorCovDerivAt_curryCc_unitZeroSec` / `tensorCovDerivAt_curryCc_eq` — the **curry-Leibniz
  law**: the directional covariant derivative of the curried carrier is the curry of the
  derivative plus the `∇X`-correction,
  `∇_V (curryCc P X) = curry (∇_V P) (X x) + curry P (∇_V X)`.
  The directional core is the proven slot-`0` curry covariant Leibniz rule
  `tensor0S_curry_covApply_slot0_leibniz_fib` (`Slot0CurryCovariantLeibniz`), rearranged.

## The coefficient-generic slot-operator field

* `slotOpFib s A x` — the leading-slot precomposition of a `(0, s + 1)`-fibre tensor by the
  fibre endomorphism `A x` (the conjugation of right-composition through the leading-slot
  currying equivalence `tensor0S_curry`); `ricSlotOpFib g s x = slotOpFib s (ricEndoRaisedFib g) x`
  and `nablaRicSlotOpFib g X s x = slotOpFib s (nablaRicciEndo g X) x`.
* `slotOpField g s A hA : SmoothCcTensor g (s + 1) (s + 1)` — the fixed smooth operator field of
  a smooth coefficient `A` (smooth by `slotOpFib_contMDiff`).
* `slotTraceSection g s A hA S : SmoothCcTensor g 0 (s + 1)` — the trace-section carrier
  `appCc (slotOpField g s A hA) (∇S)`, the operator-field action on `∇S = covGrad g 0 s S`;
  the generic form of `ricTraceSection` and `nablaRicTraceSection`.
* `tensorCovDerivAt_slotOpField_eq_slotOpFib` — the **connector**: if the coefficient `A`
  differentiates covariantly to `A'` along `X` (the Leibniz law
  `∇_{X x}(A(Y)) = A' x (Y x) + A x (∇_{X x} Y)` for every smooth field `Y` — for
  `A = ricEndoRaisedFib g` this is the metric parallelism `leviCivita_covDeriv_ricEndoRaisedFib`
  with `A' = nablaRicciEndo g X`), then the directional covariant derivative of the fixed
  operator field is the slot operator of the differentiated coefficient,
  `∇_{X x} (slotOpField A) = slotOpFib A' x`.
* `covGrad_slotTraceSection_eq` — the covariant-gradient Leibniz split of the trace-section
  carrier through the operator-field product rule `covGrad_appCc_eq`.
* `tensorCovDerivAt_slotTraceSection_eq_add` — the directional Leibniz split with the
  differentiated-coefficient summand identified through the connector.

## The Ricci instances (certification corollaries)

The existing Ricci-specific decls are untouched; thin corollaries re-derive them from the
generic engine, certifying that the generalization is genuine:
`slotOpFib_ricEndoRaisedFib`, `slotOpFib_nablaRicciEndo`,
`slotOpField_ricEndoRaisedFib_eq_ricSlotOpField`,
`slotTraceSection_ricEndoRaisedFib_eq_ricTraceSection`,
`tensorCovDerivAt_slotOpField_ricEndoRaisedFib_eq_nablaRicSlotOpFib`,
`tensorCovDerivAt_slotTraceSection_ricEndoRaisedFib_eq`.

## The Parseval leading-slot pairing trace

The fixed-family Parseval pairing trace
`⟨A, B⟩_{0,s+1}(x) = ∑ a, ⟨A(V a x, ·), B(V a x, ·)⟩_{0,s}(x)` already exists as
`tensorInnerPointwise_succ_eq_parseval_sum_slot0`
(`FiberNormParseval/ParsevalLaplacianSlot0Expansion`), family-generic over a per-point Parseval
hypothesis; it is not re-derived here.

## Convention

All fibre operations are intrinsic to the metric `g`; the connection is the Levi-Civita
connection of `g`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle Tensor0SNabla

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Smoothness of the leading-slot curry read (private re-derivations)

These smoothness steps re-derive, from the public API, the chain that is `private` in
`Slot0CurryCovariantLeibniz`: the unit-evaluated section of a smooth `(0, k)`-tensor is smooth,
the `tensor0SAsRS`-wrap of a smooth `(0, t)`-fibre section is smooth, and hence the slot-`0`
`X`-read of a smooth `(0, t + 1)`-section is a smooth `(0, t)`-Hom-bundle section. -/

set_option linter.unusedSectionVars false in
/-- The scalar-extraction functional evaluates to `1` on the unit `(0, 0)`-tensor. -/
private lemma tensor00Scalar_unitZeroSec (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper of a fibre tensor evaluates at the unit to the tensor itself. -/
private lemma tensor0SAsRS_unit_eval (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) = C := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) =
      tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) • C from
    tensor0SAsRS_apply (I := I) (M := M) x C (unitZeroSec (I := I) (M := M) x)]
  rw [tensor00Scalar_unitZeroSec (I := I) (M := M) x, one_smul]

set_option linter.unusedSectionVars false in
/-- The scalar read of a smooth `(0, 0)`-tensor section is a smooth real function. -/
private lemma contMDiff_tensor00Scalar_read
    (Y : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun z : M => Tensor0SSpace 0 I z)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) := by
  have heq : (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) =
      Tensor0SNabla.scalarFn I M (fun y : M => Y y) := by
    funext y
    rfl
  rw [heq]
  exact (Tensor0SNabla.contMDiff_scalarFn_iff_section I M (fun y : M => Y y)).mpr Y.contMDiff

/-- If `C` is a smooth section of the `(0, t)`-tensor bundle, then `y ↦ tensor0SAsRS y (C y)` is
a smooth section of the `(0, t)`-Hom-tensor bundle: by the pointwise smoothness criterion it
suffices that the application to every smooth `(0, 0)`-section `Y` is smooth, and that
application is the scalar read of `Y` times `C`. -/
private lemma contMDiff_tensor0SAsRS_wrap (t : ℕ) {C : Π y : M, Tensor0SSpace t I y}
    (hC : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel t ℝ E)
        (E := fun z : M => Tensor0SSpace t I z) y (C y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y
        (tensor0SAsRS (I := I) (M := M) y (C y))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel t ℝ E) (V₂ := fun z : M => Tensor0SSpace t I z)
    (φ := fun y : M => tensor0SAsRS (I := I) (M := M) y (C y))
  intro Y
  have hsmul := ContMDiff.smul_section (n := (∞ : WithTop ℕ∞))
    (contMDiff_tensor00Scalar_read (I := I) (M := M) Y) hC
  refine hsmul.congr fun y => ?_
  rw [show ((fun z : M => tensor00Scalar (I := I) (M := M) z (Y z)) • C) y =
      tensor00Scalar (I := I) (M := M) y (Y y) • C y from rfl]
  rw [← tensor0SAsRS_apply (I := I) (M := M) y (C y) (Y y)]

set_option linter.unusedSectionVars false in
/-- The unit-evaluated section `y ↦ (Z y)(unitZeroSec y)` of a smooth compactly-supported
`(0, k)`-tensor is a smooth section of the `(0, k)`-tensor bundle. -/
private lemma contMDiff_unitEvalSection' (g : SmoothRiemannianMetric I M) (k : ℕ)
    (Z : SmoothCcTensor g 0 k) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SSpace k I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel k ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace k I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y))) :=
    Z.toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace k I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel k ℝ E) hϕ hv

set_option linter.unusedSectionVars false in
/-- The slot-`0` `X`-read of a smooth compactly-supported `(0, t + 1)`-tensor, in
`tensor0SAsRS`-wrapped Hom-bundle form, is a smooth section of the `(0, t)`-Hom-tensor
bundle. -/
private lemma contMDiff_slot0Read (g : SmoothRiemannianMetric I M) (t : ℕ)
    (P : SmoothCcTensor g 0 (t + 1)) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y
        (tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              P.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) := by
  have hUzS := contMDiff_unitEvalSection' (I := I) (M := M) g (t + 1) P
  have hcur : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace t I z) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            P.toSection y) (unitZeroSec (I := I) (M := M) y)))) :=
    fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
      (I := I) (M := M)
      (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (t + 1) I z from
        P.toSection z) (unitZeroSec (I := I) (M := M) z)) y (hUzS y)
  have hCs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel t ℝ E)
        (E := fun z : M => Tensor0SSpace t I z) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 1) I y from
            P.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) :=
    ContMDiff.clm_bundle_apply (b := fun y : M => y)
      (E₁ := TangentSpace I) (E₂ := fun z : M => Tensor0SSpace t I z)
      (F₁ := E) (F₂ := Tensor0SModel t ℝ E) hcur hX
  exact contMDiff_tensor0SAsRS_wrap (I := I) (M := M) t hCs

/-! ### The leading-slot curry carrier -/

/-- **The leading-slot curry carrier `curryCc g t P X`.** Currying a smooth compactly-supported
`(0, t + 1)`-tensor section `P` against a smooth tangent field `X` in the leading covariant
slot yields a smooth compactly-supported `(0, t)`-tensor section,
`(curryCc P X)(X₁, …, X_t) = P(X, X₁, …, X_t)`: the fibre value at `x` is the
`tensor0SAsRS`-wrap of the bare slot-`0` curry of the unit-section evaluation of `P` read at
`X x` (smooth by `contMDiff_slot0Read`; compactly supported on the closed manifold). -/
def curryCc (g : SmoothRiemannianMetric I M) (t : ℕ) (P : SmoothCcTensor g 0 (t + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : SmoothCcTensor g 0 t where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 0 t I x from
          tensor0SAsRS (I := I) (M := M) x
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
                P.toSection x) (unitZeroSec (I := I) (M := M) x))) (X x)))
      contMDiff_toFun := contMDiff_slot0Read (I := I) (M := M) g t P X.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `curryCc g t P X` at `x` is the `tensor0SAsRS`-wrapped bare
slot-`0` curry of the unit-section evaluation of `P` read at `X x`. Definitional. -/
@[simp] lemma curryCc_toSection (g : SmoothRiemannianMetric I M) (t : ℕ)
    (P : SmoothCcTensor g 0 (t + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (curryCc (I := I) (M := M) g t P X).toSection x =
      (show TensorRSSpace 0 t I x from
        tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
              P.toSection x) (unitZeroSec (I := I) (M := M) x))) (X x))) := rfl

set_option linter.unusedSectionVars false in
/-- **The unit-evaluation reading of the curry carrier.** The unit-section evaluation of
`curryCc g t P X` at `x` is the bare slot-`0` curry of the unit-section evaluation of `P`,
read at `X x`. -/
lemma curryCc_unitZeroSec_eval (g : SmoothRiemannianMetric I M) (t : ℕ)
    (P : SmoothCcTensor g 0 (t + 1))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        (curryCc (I := I) (M := M) g t P X).toSection x)
      (unitZeroSec (I := I) (M := M) x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x))) (X x) :=
  tensor0SAsRS_unit_eval (I := I) (M := M) t x _

set_option linter.unusedSectionVars false in
/-- **The curry-Leibniz law (unit-evaluation form).** The unit-section evaluation of the
directional covariant derivative of the curry carrier `curryCc g t P X`, in the direction
`V x` of a smooth tangent field `V`, is the slot-`0` curry of the unit-evaluated directional
covariant derivative of `P` read at `X x`, *plus* the slot-`0` curry of the unit-evaluated `P`
read at the Christoffel correction `(∇_V X)(x)`:
```
(∇_{V x} (curryCc P X))(unit) = curry((∇_{V x} P)(unit))(X x) + curry(P(x)(unit))((∇_V X)(x)).
```
This is the slot-`0` curry covariant Leibniz rule `tensor0S_curry_covApply_slot0_leibniz_fib`
(`Slot0CurryCovariantLeibniz`) rearranged: the curried-section covariant derivative there is
definitionally the directional covariant derivative of `curryCc g t P X`. -/
theorem tensorCovDerivAt_curryCc_unitZeroSec (g : SmoothRiemannianMetric I M) (t : ℕ)
    (P : SmoothCcTensor g 0 (t + 1))
    (V X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensorCovDerivAt (I := I) (M := M) g 0 t
          (curryCc (I := I) (M := M) g t P X) x (V x))
      (unitZeroSec (I := I) (M := M) x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (t + 1) P x (V x))
          (unitZeroSec (I := I) (M := M) x))) (X x) +
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)))
        ((LeviCivita (I := I) g).toFun (fun y : M => X y) x (V x)) := by
  have hLeib := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g t P
    (V := fun y : M => V y) (X := fun y : M => X y) V.contMDiff X.contMDiff x
  have hbridgeP : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
      covApply (tensorCov (I := I) g 0 (t + 1)) (fun y : M => V y)
        (fun y : M => P.toSection y) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (t + 1) P x (V x)) := rfl
  have hbridgeC : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
      covApply (tensorCov (I := I) g 0 t) (fun y : M => V y)
        (fun y : M => tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (t + 1) I y from
              P.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensorCovDerivAt (I := I) (M := M) g 0 t
          (curryCc (I := I) (M := M) g t P X) x (V x)) := rfl
  rw [hbridgeP, hbridgeC] at hLeib
  exact (sub_eq_iff_eq_add.mp hLeib.symm)

set_option linter.unusedSectionVars false in
/-- **The curry-Leibniz law (carrier form).** As `(0, t)`-tensor fibre values, the directional
covariant derivative of the curry carrier splits as the curried derivative plus the
`∇X`-correction:
```
∇_{V x} (curryCc P X)
  = tensor0SAsRS (curry((∇_{V x} P)(unit))(X x)) + tensor0SAsRS (curry(P(x)(unit))((∇_V X)(x))).
```
Unit-extensionality (`tensor0s_ext_unitZero`) reduces this to the unit-evaluation form
`tensorCovDerivAt_curryCc_unitZeroSec`, with the right side unwrapped by the unit-evaluation
of `tensor0SAsRS`. -/
theorem tensorCovDerivAt_curryCc_eq (g : SmoothRiemannianMetric I M) (t : ℕ)
    (P : SmoothCcTensor g 0 (t + 1))
    (V X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (show TensorRSSpace 0 t I x from
        tensorCovDerivAt (I := I) (M := M) g 0 t
          (curryCc (I := I) (M := M) g t P X) x (V x)) =
      tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (t + 1) P x (V x))
            (unitZeroSec (I := I) (M := M) x))) (X x)) +
      tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
            P.toSection x) (unitZeroSec (I := I) (M := M) x)))
          ((LeviCivita (I := I) g).toFun (fun y : M => X y) x (V x))) := by
  have hCLM : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
      tensorCovDerivAt (I := I) (M := M) g 0 t
        (curryCc (I := I) (M := M) g t P X) x (V x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (t + 1) P x (V x))
              (unitZeroSec (I := I) (M := M) x))) (X x)) +
        tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) t x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
              P.toSection x) (unitZeroSec (I := I) (M := M) x)))
            ((LeviCivita (I := I) g).toFun (fun y : M => X y) x (V x)))) := by
    refine PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) ?_
    rw [ContinuousLinearMap.add_apply]
    rw [tensor0SAsRS_unit_eval (I := I) (M := M) t x, tensor0SAsRS_unit_eval (I := I) (M := M) t x]
    exact tensorCovDerivAt_curryCc_unitZeroSec (I := I) (M := M) g t P V X x
  exact hCLM

/-! ### The coefficient-generic leading-slot operator field -/

set_option linter.unusedSectionVars false in
/-- **The coefficient-generic leading-slot fibre operator `slotOpFib s A x`.** On a
`(0, s + 1)`-tensor `D` it precomposes the leading covariant slot with the fibre endomorphism
`A x`: the conjugation of right-composition by `A x` through the leading-slot currying
equivalence `tensor0S_curry`. The coefficient-generic form of `ricSlotOpFib` (at
`A = ricEndoRaisedFib g`) and `nablaRicSlotOpFib` (at `A = nablaRicciEndo g X`). -/
def slotOpFib (s : ℕ) (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) (x : M) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp (A x))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_comp,
          map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_comp,
          map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option linter.unusedSectionVars false in
/-- The defining formula for `slotOpFib`. -/
@[simp] lemma slotOpFib_apply (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) (x : M)
    (D : Tensor0SSpace (s + 1) I x) :
    slotOpFib (I := I) (M := M) s A x D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp (A x)) := by
  rw [slotOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
/-- **The coefficient-generic leading-slot operator reads the new slot first.** On a tuple
`Fin.cons v0 vs`, the operator reads the direction `v0` off the leading covariant slot, applies
the coefficient endomorphism `A x` to it, and evaluates the curried tensor at the resulting
direction and `vs`. -/
lemma slotOpFib_apply_eval (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (slotOpFib (I := I) (M := M) s A x D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D (A x v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (slotOpFib (I := I) (M := M) s A x D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotOpFib (I := I) (M := M) s A x D) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp (A x) := by
    rw [slotOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the coefficient-generic leading-slot operator field.** For a
smooth coefficient endomorphism field `A`, the fibre field `x ↦ slotOpFib s A x` is a smooth
section of the `(s + 1, s + 1)`-tensor bundle. The proof is the coefficient-generic form of
`ricSlotOpFib_contMDiff`: by `contMDiff_clm_section_of_pointwise` it suffices that the value on
every smooth `(0, s + 1)`-tensor `Y` is smooth; that value is the uncurry of the
right-composition of the smooth curried section of `Y` with the smooth coefficient field. -/
theorem slotOpFib_contMDiff (s : ℕ)
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1) I z) x
        (slotOpFib (I := I) (M := M) s A x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => slotOpFib (I := I) (M := M) s A x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (slotOpFib (I := I) (M := M) s A x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (A x)))) := by
    funext x
    rw [slotOpFib_apply]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (A x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (A x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (A x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x) (A x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (A x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hA Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (A x)) hG

/-- **The coefficient-generic leading-slot operator field `slotOpField g s A hA`**, as a smooth
compactly-supported `(s + 1, s + 1)`-tensor section: the fixed smooth operator field of a smooth
coefficient endomorphism field `A` (smooth by `slotOpFib_contMDiff`; compactly supported on the
closed manifold). The coefficient-generic form of `ricSlotOpField` and `nablaRicSlotOpField`. -/
def slotOpField (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x))) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 1) (s + 1) I x from slotOpFib (I := I) (M := M) s A x)
      contMDiff_toFun := slotOpFib_contMDiff (I := I) (M := M) s hA }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `slotOpField g s A hA` at `x` is the fibre operator
`slotOpFib s A x`. Definitional. -/
@[simp] lemma slotOpField_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x))) (x : M) :
    (slotOpField (I := I) (M := M) g s A hA).toSection x =
      (show TensorRSSpace (s + 1) (s + 1) I x from slotOpFib (I := I) (M := M) s A x) := rfl

/-- **The coefficient-generic trace-section carrier `slotTraceSection g s A hA S`.** For a
smooth compactly-supported `(0, s)`-tensor `S` and a smooth coefficient endomorphism field `A`,
the operator-field action of `slotOpField g s A hA` on `∇S = covGrad g 0 s S`:
```
slotTraceSection g s A hA S := appCc (slotOpField g s A hA) (∇S),
```
the contraction of the `g`-lowered coefficient against the gradient slot of `∇S`, a smooth
compactly-supported `(0, s + 1)`-tensor. The coefficient-generic form of `ricTraceSection`
(at `A = ricEndoRaisedFib g`) and `nablaRicTraceSection` (at `A = nablaRicciEndo g X`). -/
def slotTraceSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (S : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 1) (s + 1)
    (slotOpField (I := I) (M := M) g s A hA) (covGrad (I := I) (M := M) g 0 s S)

set_option linter.unusedSectionVars false in
/-- **The fibre value of `slotTraceSection` is the fibrewise composition
`(slotOpFib s A x).comp (∇S x)`.** Definitional via `appCc_toSection`. -/
@[simp] lemma slotTraceSection_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (S : SmoothCcTensor g 0 s) (x : M) :
    (slotTraceSection (I := I) (M := M) g s A hA S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotOpFib (I := I) (M := M) s A x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [slotTraceSection,
    appCc_toSection (I := I) (M := M) g (s + 1) (s + 1)
      (slotOpField (I := I) (M := M) g s A hA) (covGrad (I := I) (M := M) g 0 s S) x]
  rfl

set_option linter.unusedSectionVars false in
/-- **The leading-slot reading of the trace-section carrier.** The unit-`(0, 0)`-evaluation of
`slotTraceSection g s A hA S`, read on a tuple `Fin.cons v0 vs`, equals the unit-evaluation of
`∇S = covGrad g 0 s S` with the leading slot precomposed by the coefficient endomorphism
`A x`. Coefficient-generic form of `nablaRicTraceSection_apply_leadingSlot`. -/
theorem slotTraceSection_apply_leadingSlot (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (S : SmoothCcTensor g 0 s) (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotTraceSection (I := I) (M := M) g s A hA S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (A x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (slotTraceSection (I := I) (M := M) g s A hA S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      slotOpFib (I := I) (M := M) s A x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [slotTraceSection_toSection]
    rfl
  rw [hval]
  rw [slotOpFib_apply_eval (I := I) (M := M) s A x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (A x v0) vs]

/-! ### The coefficient-generic connector `∇(slotOpField A) = slotOpFib A'` -/

set_option linter.unusedSectionVars false in
/-- **Leading-slot curry reading of the directional covariant derivative of `slotOpField`.**
If the coefficient `A` differentiates covariantly to `A'` along `X` at `x` (`hDeriv`), reading
the leading covariant slot of the directional covariant derivative of the fixed operator field
`slotOpField g s A hA` on a `(0, s + 1)`-fibre tensor `D` at slot direction `v0` recovers `D`
curried at the differentiated coefficient `A' x v0`. The coefficient-generic form of the curry
reading inside `tensorCovDerivAt_ricSlotOpField_eq_nablaRicSlotOpFib`: the Hom-connection
product rule expands the derivative on a local section through `D`; the curry-Leibniz rule
passes the connection through the leading-slot curry twice; the shared terms cancel and
`hDeriv` converts the surviving coefficient derivative into `A'`. -/
private theorem slotOp_core_curry_reading (g : SmoothRiemannianMetric I M) (s : ℕ)
    {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hDeriv : ∀ Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      (LeviCivita (I := I) g).toFun (fun y : M => A y (Y y)) x (X x) =
        A' x (Y x) + A x ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)))
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
            (slotOpField (I := I) (M := M) g s A hA) x (X x)) D)) v0 =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x D) (A' x v0) := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  have hZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (A y (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) hA Y.contMDiff
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => A y (Y y), hZ_smooth⟩
  set Φ := slotOpField (I := I) (M := M) g s A hA with hΦ
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Φ.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        Φ.toSection y) (w y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (s + 1) (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hCL_U := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      Φ.toSection y) (w y)) (x := x) hU_at Y (X x)
  have hCL_w := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g s
    (fun y : M => w y) (x := x) hw_at Z (X x)
  have hHL := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1)
    (LeviCivita (I := I) g) Φ.toSection w x (X x)
  have hfun : (fun y : M =>
        (Tensor0SNabla.curriedSection I M
            (fun y' : M => (show Tensor0SSpace (s + 1) I y' →L[ℝ] Tensor0SSpace (s + 1) I y' from
              Φ.toSection y') (w y')) y) (Y y)) =
      (fun y : M => (Tensor0SNabla.curriedSection I M (fun y' : M => w y') y) (Z y)) := by
    funext y
    change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          Φ.toSection y) (w y))) (Y y) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y (w y)) (A y (Y y))
    rw [hΦ, slotOpField_toSection, slotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [← hw, ← hY,
    tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1) Φ x (X x)]
  rw [hHL, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL_U.symm]
  rw [hfun]
  rw [show (fun y : M => Z y) = (fun y : M => A y (Y y)) from rfl] at hCL_w
  rw [hCL_w]
  have hEndo := hDeriv Y
  have hcurU : (Tensor0SNabla.curriedSection I M
        (fun y' : M => (show Tensor0SSpace (s + 1) I y' →L[ℝ] Tensor0SSpace (s + 1) I y' from
          Φ.toSection y') (w y')) x)
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x (w x))
        (A x ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x))) := by
    change (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          Φ.toSection x) (w x)))
        ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)) = _
    rw [hΦ, slotOpField_toSection, slotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hΦgrad : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
            (fun y : M => w y) x (X x)))) (Y x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
            (fun y : M => w y) x (X x)))
        (A x (Y x)) := by
    rw [hΦ, slotOpField_toSection, slotOpFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hZx : Z x = A x (Y x) := rfl
  have hcurW : (Tensor0SNabla.curriedSection I M (fun y' : M => w y') x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x (w x)) := rfl
  rw [hcurU, hΦgrad, hZx, hcurW]
  rw [hEndo, map_add]
  abel

set_option linter.unusedSectionVars false in
/-- **The coefficient-generic connector.** If the smooth coefficient endomorphism field `A`
differentiates covariantly to `A'` along the smooth tangent field `X` (the Leibniz law
`hDeriv : ∇_{X x}(A(Y)) = A' x (Y x) + A x (∇_{X x} Y)` for every smooth field `Y` and point
`x` — for `A = ricEndoRaisedFib g` this is the metric parallelism
`leviCivita_covDeriv_ricEndoRaisedFib` with `A' = nablaRicciEndo g X`), then the directional
covariant derivative of the fixed operator field `slotOpField g s A hA` in direction `X x` is
the slot operator of the differentiated coefficient:
```
∇_{X x} (slotOpField g s A hA) = slotOpFib s A' x.
```
The leading-slot precomposition conjugation is parallel; the connection differentiates only the
coefficient. Testing on a `(0, s + 1)`-tensor and a cons-tuple reads the right side via
`slotOpFib_apply_eval` and the left side via the curry reading `slotOp_core_curry_reading`. -/
theorem tensorCovDerivAt_slotOpField_eq_slotOpFib (g : SmoothRiemannianMetric I M) (s : ℕ)
    {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hDeriv : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M),
      (LeviCivita (I := I) g).toFun (fun y : M => A y (Y y)) x (X x) =
        A' x (Y x) + A x ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)))
    (x : M) :
    tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (slotOpField (I := I) (M := M) g s A hA) x (X x) =
      (show TensorRSSpace (s + 1) (s + 1) I x from
        slotOpFib (I := I) (M := M) s A' x) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          slotOpFib (I := I) (M := M) s A' x) D)
        (Fin.cons (m 0) (Matrix.vecTail m)) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (A' x (m 0))) (Matrix.vecTail m) from
    slotOpFib_apply_eval (I := I) (M := M) s A' x D (m 0) (Matrix.vecTail m)]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (slotOpField (I := I) (M := M) g s A hA) x (X x)) D) (m 0) (Matrix.vecTail m)]
  congr 1
  exact slotOp_core_curry_reading (I := I) (M := M) g s hA X x
    (fun Y => hDeriv Y x) D (m 0)

set_option linter.unusedSectionVars false in
/-- **The covariant-gradient Leibniz split of the trace-section carrier.** The covariant
gradient of `slotTraceSection g s A hA S = appCc (slotOpField g s A hA) (∇S)` splits into the
action of the gradient of the operator field on `∇S` plus the action of the passenger-slot
extension on `∇²S`. Direct instance of the covariant product rule `covGrad_appCc_eq`;
coefficient-generic form of `covGrad_ricTraceSection_eq`. -/
theorem covGrad_slotTraceSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 (s + 1)
        (slotTraceSection (I := I) (M := M) g s A hA S) =
      appCc (I := I) (M := M) g (s + 1) (s + 2)
          (covGrad (I := I) (M := M) g (s + 1) (s + 1)
            (slotOpField (I := I) (M := M) g s A hA))
          (covGrad (I := I) (M := M) g 0 s S) +
        appCc (I := I) (M := M) g (s + 2) (s + 2)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
            (slotOpField (I := I) (M := M) g s A hA))
          (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)) :=
  covGrad_appCc_eq (I := I) (M := M) g (s + 1) (s + 1)
    (slotOpField (I := I) (M := M) g s A hA) (covGrad (I := I) (M := M) g 0 s S)

set_option linter.unusedSectionVars false in
/-- **The directional covariant-derivative Leibniz split of the trace-section carrier, with the
differentiated-coefficient summand identified.** Under the coefficient derivative law `hDeriv`,
the directional covariant derivative of `slotTraceSection g s A hA S` along `X x` is the slot
operator of the differentiated coefficient acting on `∇S` plus the undifferentiated slot
operator acting on the differentiated gradient:
```
∇_{X x}(slotTraceSection A S)
  = (slotOpFib A' x).comp (∇S x) + (slotOpFib A x).comp (∇_{X x}(∇S)).
```
The directional operator-field product rule `tensorCovDerivAt_appCc_eq` splits the derivative;
the connector `tensorCovDerivAt_slotOpField_eq_slotOpFib` identifies the differentiated-operator
summand. Coefficient-generic form of `tensorCovDerivAt_ricTraceSection_eq_nablaRicTrace_add`. -/
theorem tensorCovDerivAt_slotTraceSection_eq_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x (A x)))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hDeriv : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M),
      (LeviCivita (I := I) g).toFun (fun y : M => A y (Y y)) x (X x) =
        A' x (Y x) + A x ((LeviCivita (I := I) g).toFun (fun y : M => Y y) x (X x)))
    (S : SmoothCcTensor g 0 s) (x : M) :
    (show TensorRSSpace 0 (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
          (slotTraceSection (I := I) (M := M) g s A hA S) x (X x)) =
      (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            slotOpFib (I := I) (M := M) s A' x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s S).toSection x)) +
        (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            slotOpFib (I := I) (M := M) s A x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) x (X x))) := by
  rw [show slotTraceSection (I := I) (M := M) g s A hA S =
      appCc (I := I) (M := M) g (s + 1) (s + 1) (slotOpField (I := I) (M := M) g s A hA)
        (covGrad (I := I) (M := M) g 0 s S) from rfl]
  rw [tensorCovDerivAt_appCc_eq (I := I) (M := M) g (s + 1) (s + 1)
    (slotOpField (I := I) (M := M) g s A hA) (covGrad (I := I) (M := M) g 0 s S) x (X x)]
  congr 1
  congr 1
  exact congrArg (fun (T : Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x) => T)
    (tensorCovDerivAt_slotOpField_eq_slotOpFib (I := I) (M := M) g s hA X hDeriv x)

/-! ### The Ricci instances (certification corollaries)

The generic engine reproduces the Ricci-specific carriers: the existing decls in
`RicciTraceCarrier` / `NablaRicciTraceCarrier` are untouched, and these corollaries certify
that they are instances of the coefficient-generic calculus at `A = ricEndoRaisedFib g`
(and `A' = nablaRicciEndo g X`). -/

set_option linter.unusedSectionVars false in
/-- The Ricci slot operator is the generic slot operator at the raised-Ricci coefficient. -/
lemma slotOpFib_ricEndoRaisedFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    slotOpFib (I := I) (M := M) s (fun y : M => ricEndoRaisedFib (I := I) g y) x =
      ricSlotOpFib (I := I) (M := M) g s x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [slotOpFib_apply, ricSlotOpFib_apply]

set_option linter.unusedSectionVars false in
/-- The differentiated-Ricci slot operator is the generic slot operator at the
differentiated-Ricci coefficient. -/
lemma slotOpFib_nablaRicciEndo (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (s : ℕ) (x : M) :
    slotOpFib (I := I) (M := M) s (fun y : M => nablaRicciEndo (I := I) g X y) x =
      nablaRicSlotOpFib (I := I) (M := M) g X s x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [slotOpFib_apply, nablaRicSlotOpFib_apply]

set_option linter.unusedSectionVars false in
/-- The Ricci slot-operator field is the generic slot-operator field at the raised-Ricci
coefficient. -/
theorem slotOpField_ricEndoRaisedFib_eq_ricSlotOpField (g : SmoothRiemannianMetric I M)
    (s : ℕ) :
    slotOpField (I := I) (M := M) g s (fun y : M => ricEndoRaisedFib (I := I) g y)
        (ricEndoRaisedFib_contMDiff (I := I) g) =
      ricSlotOpField (I := I) (M := M) g s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [slotOpField_toSection, ricSlotOpField_toSection]
  exact congrArg (fun (T : Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x) => T)
    (slotOpFib_ricEndoRaisedFib (I := I) (M := M) g s x)

set_option linter.unusedSectionVars false in
/-- The Ricci-trace carrier is the generic trace-section carrier at the raised-Ricci
coefficient. -/
theorem slotTraceSection_ricEndoRaisedFib_eq_ricTraceSection (g : SmoothRiemannianMetric I M)
    (s : ℕ) (S : SmoothCcTensor g 0 s) :
    slotTraceSection (I := I) (M := M) g s (fun y : M => ricEndoRaisedFib (I := I) g y)
        (ricEndoRaisedFib_contMDiff (I := I) g) S =
      ricTraceSection (I := I) (M := M) g s S := by
  rw [show ricTraceSection (I := I) (M := M) g s S =
      appCc (I := I) (M := M) g (s + 1) (s + 1) (ricSlotOpField (I := I) (M := M) g s)
        (covGrad (I := I) (M := M) g 0 s S) from rfl]
  rw [show slotTraceSection (I := I) (M := M) g s
        (fun y : M => ricEndoRaisedFib (I := I) g y)
        (ricEndoRaisedFib_contMDiff (I := I) g) S =
      appCc (I := I) (M := M) g (s + 1) (s + 1)
        (slotOpField (I := I) (M := M) g s (fun y : M => ricEndoRaisedFib (I := I) g y)
          (ricEndoRaisedFib_contMDiff (I := I) g))
        (covGrad (I := I) (M := M) g 0 s S) from rfl]
  rw [slotOpField_ricEndoRaisedFib_eq_ricSlotOpField (I := I) (M := M) g s]

set_option linter.unusedSectionVars false in
/-- **The generic connector reproduces the Ricci carrier-derivative connector.** At the
raised-Ricci coefficient, the coefficient derivative law is the metric parallelism
`leviCivita_covDeriv_ricEndoRaisedFib` (with `A' = nablaRicciEndo g X`), and the generic
connector `tensorCovDerivAt_slotOpField_eq_slotOpFib` yields the differentiated-Ricci slot
operator — re-deriving `tensorCovDerivAt_ricSlotOpField_eq_nablaRicSlotOpFib` from the
coefficient-generic engine. -/
theorem tensorCovDerivAt_slotOpField_ricEndoRaisedFib_eq_nablaRicSlotOpFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1)
        (slotOpField (I := I) (M := M) g s (fun y : M => ricEndoRaisedFib (I := I) g y)
          (ricEndoRaisedFib_contMDiff (I := I) g)) x (X x) =
      (show TensorRSSpace (s + 1) (s + 1) I x from
        nablaRicSlotOpFib (I := I) (M := M) g X s x) := by
  rw [tensorCovDerivAt_slotOpField_eq_slotOpFib (I := I) (M := M) g s
    (A' := fun y : M => nablaRicciEndo (I := I) g X y)
    (ricEndoRaisedFib_contMDiff (I := I) g) X
    (fun Y x' => leviCivita_covDeriv_ricEndoRaisedFib (I := I) (M := M) g X Y x') x]
  exact congrArg (fun (T : Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x) => T)
    (slotOpFib_nablaRicciEndo (I := I) (M := M) g X s x)

set_option linter.unusedSectionVars false in
/-- **The generic directional split reproduces the Ricci-trace Leibniz split.** At the
raised-Ricci coefficient, the generic directional split
`tensorCovDerivAt_slotTraceSection_eq_add` instantiates to the directional Leibniz split of the
Ricci-trace carrier, with the differentiated summand the differentiated-Ricci slot operator
acting on `∇S` — re-deriving `tensorCovDerivAt_ricTraceSection_eq_nablaRicTrace_add` from the
coefficient-generic engine. -/
theorem tensorCovDerivAt_slotTraceSection_ricEndoRaisedFib_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (show TensorRSSpace 0 (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S) x (X x)) =
      (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            nablaRicSlotOpFib (I := I) (M := M) g X s x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s S).toSection x)) +
        (show TensorRSSpace 0 (s + 1) I x from
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            ricSlotOpFib (I := I) (M := M) g s x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) x (X x))) := by
  rw [← slotTraceSection_ricEndoRaisedFib_eq_ricTraceSection (I := I) (M := M) g s S]
  rw [tensorCovDerivAt_slotTraceSection_eq_add (I := I) (M := M) g s
    (A' := fun y : M => nablaRicciEndo (I := I) g X y)
    (ricEndoRaisedFib_contMDiff (I := I) g) X
    (fun Y x' => leviCivita_covDeriv_ricEndoRaisedFib (I := I) (M := M) g X Y x') S x]
  rw [slotOpFib_nablaRicciEndo (I := I) (M := M) g X s x,
    slotOpFib_ricEndoRaisedFib (I := I) (M := M) g s x]

end Connection
end Integral
end DifferentialGeometry

end
