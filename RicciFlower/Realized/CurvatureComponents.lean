import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Realized.TensorRicciIdentity
import RicciFlower.Realized.LeviCivita.Koszul
import RicciFlower.Coordinates.NablaComponents.Basic
import RicciFlower.Tensor.RSTensor.Components

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointwise curvature components

This file records the metric-free, pointwise component layer used by curvature
calculations.  A tangent `Module.Basis` at one point is the primitive coordinate
object; local-frame statements are thin wrappers through `hframe.toBasisAt hx`.

No Christoffel or derivative curvature formula is stated here: those formulas
need either structure coefficients for a general frame or a holonomic-frame
hypothesis.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

/-- Two tensor slots encoded as a `Fin 2` index function. -/
def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun a => if a = 0 then i else j

/-- Four tensor slots encoded as a `Fin 4` index function. -/
def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun a => if a = 0 then i else if a = 1 then j else if a = 2 then k else l

/-- Pointwise Ricci component in a tangent basis. -/
def ricciCompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) : Real :=
  component0S (I := I) basis Ric (slots2 i j)

/-- Pointwise lowered Riemann component in a tangent basis. -/
def rm04CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) : Real :=
  component0S (I := I) basis Rm04 (slots4 i j k l)

@[simp]
theorem ricciCompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      Ric (vec2 (basis i) (basis j)) := by
  unfold ricciCompAt component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp

@[simp]
theorem rm04CompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) :
    rm04CompAt (I := I) basis Rm04 i j k l =
      Rm04 (vec4 (basis i) (basis j) (basis k) (basis l)) := by
  unfold rm04CompAt component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp

private theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change (0 : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (((T a : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) +
          (∑ i ∈ S, (T i : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real))) v) =
        (T a : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v +
          ∑ i ∈ S, (T i : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v
      rw [ContinuousMultilinearMap.add_apply, ih]

private theorem basisTensor0S_empty_eq_scalarOne
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (slots : Fin 0 -> Idx) :
    basisTensor0S (I := I) basis slots = scalarOne0S (I := I) x := by
  ext v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]
  have hcomp := basisTensor0S_component (I := I) basis slots slots
  have harg : (fun a : Fin 0 => basis (slots a)) = Fin.elim0 := Subsingleton.elim _ _
  change (basisTensor0S (I := I) basis slots) (fun a : Fin 0 => basis (slots a)) = 1
    at hcomp
  rw [harg] at hcomp
  simpa [scalarOne0S] using hcomp

/-- Components of the symbolically defined Ricci tensor are the components of
the tensor trace contraction of the `(1,3)` curvature tensor. -/
theorem ricciCompAt_eq_contractTrace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        Fin.elim0 (slots2 i j) := by
  unfold ricciCompAt componentRS ricciFromRm13At component0S
  rw [basisTensor0S_empty_eq_scalarOne (I := I) basis Fin.elim0]

/-- Basis-coordinate evaluation of the intrinsic trace contraction defining
Ricci from a `(1,3)` tensor. -/
theorem contract_trace13_component_basis
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) (basis i) (basis j)) := by
  haveI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  unfold contract_trace
  change ((model_contract_trace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (vec2 (basis i) (basis j)) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basis 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basis.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basis.coord a) (v 0) * 1 = (basis.coord a) (v 0)
    ring
  simp only [model_interior_product, model_tensorWithCovector_first, model_covectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpace_continuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
        (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 (basis i) (basis j))) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 (basis i) (basis j)))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 (basis i) (basis j) 1 = basis j
    simp [vec2]

/-- Basis-coordinate evaluation of the intrinsic trace contraction defining
Ricci from a `(1,3)` tensor, with arbitrary second and third inputs. -/
theorem ricciFromRm13At_apply_basis_trace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Y Z : TangentSpace I x) :
    ricciFromRm13At (I := I) (M := M) Rm13 (vec2 Y Z) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) Y Z) := by
  haveI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  change ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 Y Z) = _
  unfold contract_trace
  change ((model_contract_trace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (vec2 Y Z) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basis 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basis.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basis.coord a) (v 0) * 1 = (basis.coord a) (v 0)
    ring
  simp only [model_interior_product, model_tensorWithCovector_first, model_covectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpace_continuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => TangentSpace I x) 1)))
        (Fin.cons (basis a) (vec2 Y Z)) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 Y Z)) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 Y Z))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 Y Z 1 = Z
    simp [vec2]

/-- A lowered `(0,4)` tensor is obtained from a `(1,3)` tensor by lowering the
output slot with the metric. -/
def Rm04LowersRm13At
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) =
      Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)

/-- Realized `(1,3)` and lowered `(0,4)` curvature tensors are related by
metric lowering at a point. -/
theorem rm04LowersRm13At_of_realizes
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) :
    Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) := by
  intro W X Y Z
  let Wsec : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x W
  let Xsec : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x X
  let Ysec : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Y
  let Zsec : (p : M) -> TangentSpace I p := LeviCivita.tangentConstAt (I := I) x Z
  let alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W)
  have h04 := hRm04 Wsec Xsec Ysec Zsec x
  have h13 := hRm13 Xsec Ysec Zsec x alpha
  have h04' :
      Rm04 x (vec4 W X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov Xsec Ysec Zsec) x) := by
    dsimp [Wsec, Xsec, Ysec, Zsec] at h04
    rw [LeviCivita.tangentConstAt_self] at h04
    rw [LeviCivita.tangentConstAt_self] at h04
    rw [LeviCivita.tangentConstAt_self] at h04
    rw [LeviCivita.tangentConstAt_self] at h04
    exact h04
  have h13' :
      Rm13 x
          (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
          (vec3 X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov Xsec Ysec Zsec) x) := by
    dsimp [Xsec, Ysec, Zsec, alpha] at h13
    rw [LeviCivita.tangentConstAt_self] at h13
    rw [LeviCivita.tangentConstAt_self] at h13
    rw [LeviCivita.tangentConstAt_self] at h13
    simpa [tangentFlatLinear_apply, cotangentToDual_apply] using h13
  exact h04'.trans h13'.symm

/-- Metric skew-adjointness of the curvature endomorphism in `(1,3)` form:
`g(W,R(X,Y)Z) = -g(Z,R(X,Y)W)`. -/
def Rm13MetricSkewAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z) =
      -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W)

/-- Last-pair metric skew for a lowered Riemann tensor in RicciFlower's slot
order `Rm04(W,X,Y,Z) = g(W,R(X,Y)Z)`. -/
def Rm04OutputSkewAt
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm04 (vec4 W X Y Z) = -Rm04 (vec4 Z X Y W)

theorem rm13MetricSkewAt_of_rm04_outputSkew
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hSkew : Rm04OutputSkewAt (I := I) Rm04) :
    Rm13MetricSkewAt (I := I) g x Rm13 := by
  intro W X Y Z
  calc
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)
        = Rm04 (vec4 W X Y Z) := (hLower W X Y Z).symm
    _ = -Rm04 (vec4 Z X Y W) := hSkew W X Y Z
    _ = -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W) := by rw [hLower Z X Y W]

/-- Metric skew-adjointness of `(1,3)` curvature follows from a lowered
realization and output skew-adjointness of the lowered tensor. -/
theorem rm13MetricSkewAt_of_realizes_outputSkew
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g cov Rm04)
    {x : M}
    (hSkew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_rm04_outputSkew (I := I) g (Rm13 x) (Rm04 x)
    (rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x)
    hSkew

/-- The signed curvature trace appearing when commuting the first two slots of
`∇²α` for a one-form `α`.

The leading minus sign matches the realized convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`, since covectors see the negative
curvature action. -/
def curvatureTraceOneFormAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Y : TangentSpace I x) : Real :=
  -∑ i : Idx, ∑ j : Idx,
    gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))

/-- The metric trace of the one-form curvature commutator realizes a Ricci
pairing with a supplied vector.  In the scalar specialization, the vector is
`∇u`. -/
def CurvatureTraceOneFormEqRicVectorAt
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv Y =
      Ric x (vec2 Y curvatureVector)

theorem curvatureActionTraceEqualsRicVectorCoord_of_tensor
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hcurv : CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha
      basis gInv curvatureVector) :
    CurvatureActionTraceEqualsRicGradCoord gInv
      (fun i k j => -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
      (fun k => Ric x (vec2 (basis k) curvatureVector)) := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * -Rm13 x alpha (vec3 (basis i) (basis k) (basis j)))
        = curvatureTraceOneFormAt (I := I) Rm13 alpha basis gInv (basis k) := by
          unfold curvatureTraceOneFormAt
          simp_rw [mul_neg, Finset.sum_neg_distrib]
    _ = Ric x (vec2 (basis k) curvatureVector) := hcurv (basis k)

/-- Coordinate covectors are inverse-metric contractions of metric-lowered basis
covectors. -/
theorem basis_coord_eq_sum_inv_inner
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V := by
  symm
  calc
    (∑ k : Idx, gInv a k * g.inner x (basis k) V)
        = ∑ k : Idx, gInv a k *
            g.inner x (basis k) (∑ j : Idx, basis.coord j V • basis j) := by
          rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
    _ = ∑ k : Idx, ∑ j : Idx,
          gInv a k * (basis.coord j V * g.inner x (basis k) (basis j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ j : Idx, basis.coord j V *
          (∑ k : Idx, gInv a k * g.inner x (basis k) (basis j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ = ∑ j : Idx, basis.coord j V * (if a = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [(hinv a j).1]
    _ = basis.coord a V := by
          simp

theorem rm13_dualCoord_apply_eq_sum_inv_flat
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (a : Idx) (X Y Z : TangentSpace I x) :
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 X Y Z) =
      ∑ k : Idx,
        gInv a k *
          Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)))
            (vec3 X Y Z) := by
  have hdual :
      dualToCotangent (I := I) (basis.coord a) =
        ∑ k : Idx, gInv a k •
          dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)) := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext V
    simp [tangentFlatLinear_apply,
      basis_coord_eq_sum_inv_inner (I := I) g basis gInv hinv a V]
  rw [hdual]
  rw [_root_.map_sum Rm13]
  rw [tensor0SSpace_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [ContinuousMultilinearMap.smul_apply]
  simp [smul_eq_mul]

theorem curvatureTraceOneFormEqRicVectorAt_of_metric_dual
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hAlpha :
      alpha =
        dualToCotangent (I := I)
          ((tangentFlatLinear (I := I) g x) curvatureVector)) :
    CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13 alpha basis gInv
      curvatureVector := by
  intro Y
  unfold curvatureTraceOneFormAt
  rw [hAlpha]
  calc
    -(∑ i : Idx, ∑ j : Idx,
        gInv i j *
          Rm13 x
            (dualToCotangent (I := I)
              ((tangentFlatLinear (I := I) g x) curvatureVector))
            (vec3 (basis i) Y (basis j)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j *
              Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
          have hrewrite : ∀ i j : Idx,
              Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) curvatureVector))
                (vec3 (basis i) Y (basis j)) =
              -Rm13 x
                (dualToCotangent (I := I)
                  ((tangentFlatLinear (I := I) g x) (basis j)))
                (vec3 (basis i) Y curvatureVector) := by
            intro i j
            exact hSkew curvatureVector (basis i) Y (basis j)
          simp_rw [hrewrite]
          simp_rw [mul_neg, Finset.sum_neg_distrib]
          ring
    _ = ∑ i : Idx,
          Rm13 x (dualToCotangent (I := I) (basis.coord i))
            (vec3 (basis i) Y curvatureVector) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (rm13_dualCoord_apply_eq_sum_inv_flat (I := I) g basis gInv hinv
            (Rm13 x) i (basis i) Y curvatureVector).symm
    _ = ricciFromRm13At (I := I) (M := M) (Rm13 x)
          (vec2 Y curvatureVector) := by
          rw [ricciFromRm13At_apply_basis_trace (I := I) basis (Rm13 x)
            Y curvatureVector]
    _ = Ric x (vec2 Y curvatureVector) := by
          rw [hRic x]

/-- Coordinate form of `Ric(Y,Z) = trace (X |-> R(X,Y)Z)`, rewritten through a
lowered `(0,4)` Riemann tensor. With the convention
`Rm04(W,X,Y,Z) = g(W, R(X,Y)Z)`, the traced component is
`sum_{a,k} gInv a k * Rm04(e_k,e_a,e_i,e_j)`. -/
theorem ricciFromRm13_comp_eq_rm04_trace
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j := by
  rw [ricciCompAt_apply]
  change ((contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) = _
  rw [contract_trace13_component_basis (I := I) basis Rm13 i j]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hdual :
      dualToCotangent (I := I) (basis.coord a) =
        ∑ k : Idx, gInv a k •
          dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (basis k)) := by
    apply cotangentToDualLinear_injective (I := I) (x := x)
    ext V
    simp [tangentFlatLinear_apply,
      basis_coord_eq_sum_inv_inner (I := I) g basis gInv hinv a V]
  rw [hdual]
  rw [_root_.map_sum Rm13]
  rw [tensor0SSpace_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rw [ContinuousMultilinearMap.smul_apply]
  simp only [smul_eq_mul]
  rw [← hLower (basis k) (basis a) (basis i) (basis j)]
  rw [rm04CompAt_apply]

/-- Coordinate form of a Ricci tensor that is intrinsically the trace of a
`(1,3)` tensor, after lowering that `(1,3)` tensor to a `(0,4)` tensor. -/
theorem ricciComp_eq_rm04_trace_of_rm13
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hRic : Ric = ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis Rm04 k a i j := by
  rw [hRic]
  exact ricciFromRm13_comp_eq_rm04_trace (I := I) g basis gInv hinv Rm13 Rm04 hLower i j

theorem ricciComp_eq_rm04_trace_of_rm13_section
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x))
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      ∑ a : Idx, ∑ k : Idx,
        gInv a k * rm04CompAt (I := I) basis (Rm04 x) k a i j := by
  exact ricciComp_eq_rm04_trace_of_rm13 (I := I) g basis gInv hinv (Ric x) (Rm13 x)
    (Rm04 x) (hRic x) hLower i j

theorem ricciCompAt_eq_contractTrace_of_realizes
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (i j : Idx) :
    ricciCompAt (I := I) basis (Ric x) i j =
      componentRS (I := I) basis
        (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x (Rm13 x))
        Fin.elim0 (slots2 i j) := by
  rw [hRic x]
  exact ricciCompAt_eq_contractTrace (I := I) basis (Rm13 x) i j

/-- Pointwise trace realization of Ricci from a lowered Riemann tensor in a
tangent basis. -/
def RicciRealizesRm04TraceAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  forall X Y : TangentSpace I x,
    Ric (vec2 X Y) =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * Rm04 (vec4 (basis k) X Y (basis l))

/-- Pointwise trace realization of scalar curvature from a Ricci tensor in a
tangent basis. -/
def ScalarRealizesRicciTraceAt
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x)) : Prop :=
  scalar =
    ∑ i : Idx, ∑ j : Idx, gInv i j * Ric (vec2 (basis i) (basis j))

theorem ricciComp_eq_trace_rm04
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hRic : RicciRealizesRm04TraceAt (I := I) Ric Rm04 gInv basis)
    (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * rm04CompAt (I := I) basis Rm04 k i j l := by
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hRic (basis i) (basis j)

theorem scalar_eq_trace_ricci
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (scalar : Real)
    (Ric : Tensor02At (I := I) (M := M) x)
    (gInv : Idx -> Idx -> Real)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric gInv basis) :
    scalar =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ricciCompAt (I := I) basis Ric i j := by
  rw [hScalar]
  simp_rw [ricciCompAt_apply]

section LocalFrame

variable {u : Set M}

theorem ricciCompAt_eq_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ricciComp (I := I) Ric frame x i j := by
  unfold ricciCompAt ricciComp component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem rm04CompAt_eq_frame
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j k l : Idx) :
    rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j k l =
      rm04Comp (I := I) Rm04 frame x i j k l := by
  unfold rm04CompAt rm04Comp component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

theorem ricciTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04TraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro X Y
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    IsLocalFrameOn.toBasisAt_coe] using hRic x X Y

theorem scalarTraceAt_of_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    ScalarRealizesRicciTraceAt (I := I) (scalar x) (Ric x) (gInv x)
      (hframe.toBasisAt hx) := by
  simpa [ScalarRealizesRicciTraceAt, ScalarSectionRealizesRicciTraceInFrame,
    tensor02ToField, IsLocalFrameOn.toBasisAt_coe] using hScalar x

theorem ricciComp_eq_trace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  exact ricciComp_eq_trace_rm04 (I := I) (hframe.toBasisAt hx) (Ric x) (Rm04 x)
    (gInv x) (ricciTraceAt_of_frame (I := I) Ric Rm04 gInv frame hframe hRic hx) i j

theorem scalar_eq_trace_ricci_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j := by
  exact scalar_eq_trace_ricci (I := I) (hframe.toBasisAt hx) (scalar x) (Ric x)
    (gInv x) (scalarTraceAt_of_frame (I := I) scalar Ric gInv frame hframe hScalar hx)

end LocalFrame

section CoordinateChristoffelCurvature

open RicciFlower.Coordinates

variable [Module.Finite Real E] [CompleteSpace Real]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Christoffel coefficients in the chart-induced coordinate frame at `x₀`.

With this convention `christoffelCoordAt cov x₀ i j k` is `Γ^k_{ij}(x₀)`. -/
def christoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx E) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k

/-- The coordinate-frame Christoffel coefficient as a scalar function near `x₀`. -/
def christoffelCoordFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx E) (x : M) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k

/-- Directional derivative of a coordinate-frame Christoffel coefficient at `x₀`. -/
def christoffelCoordDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (dir i j k : CoordinateIdx E) : Real :=
  extDerivFun (I := I) (christoffelCoordFun (I := I) cov x₀ i j k) x₀
    (coordinateFrameAt (I := I) x₀ dir x₀)

/-- Coordinate curvature coefficient for the chart-induced coordinate frame.

The convention is
`R^m_{j i k} = ∂ᵢ Γ^m_{k j} - ∂ₖ Γ^m_{i j}
  + Γ^a_{k j} Γ^m_{i a} - Γ^a_{i j} Γ^m_{k a}`.
The bracket term is absent only for this coordinate frame. -/
def christoffelCurvCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i k j m : CoordinateIdx E) : Real :=
  christoffelCoordDerivAt (I := I) cov x₀ i k j m -
    christoffelCoordDerivAt (I := I) cov x₀ k i j m +
    (∑ a : CoordinateIdx E,
      christoffelCoordAt (I := I) cov x₀ k j a *
        christoffelCoordAt (I := I) cov x₀ i a m) -
    (∑ a : CoordinateIdx E,
      christoffelCoordAt (I := I) cov x₀ i j a *
        christoffelCoordAt (I := I) cov x₀ k a m)

/-- Coordinate-frame expansion of the connection curvature vector.

This is the geometric Christoffel-expansion frontier: it is where the product
rule for `∇_{eᵢ}(Γ^a_{kj} e_a)` and the coordinate-frame bracket-zero theorem
belong.  Downstream tensor statements should consume this predicate rather than
re-expanding vector-field covariant derivatives. -/
def ConnectionCurvatureCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) : Prop :=
  ∀ i k j : CoordinateIdx E,
    (connectionRiemannCurvatureField (I := I) cov
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ k)
      (coordinateFrameAt (I := I) x₀ j)) x₀ =
        ∑ m : CoordinateIdx E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m •
            coordinateFrameAt (I := I) x₀ m x₀

/-- Future producer theorem for `ConnectionCurvatureCoordAt`.

The proof should use `covariantDerivative_eq_sum_christoffel`, the coordinate
frame expansion product rule, and `coordinateFrameAt_bracket_zero`. -/
theorem connection_curvature_coord_of_christoffel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) :
    ConnectionCurvatureCoordAt (I := I) cov x₀ := by
  -- Frontier: this is the honest vector-field calculation
  -- `∇ᵢ(Γ^a_{kj} e_a) - ∇ₖ(Γ^a_{ij} e_a)` in the chart-induced coordinate
  -- frame, plus the already proved bracket-zero theorem for that frame.
  sorry

/-- The supplied `(1,3)` curvature tensor evaluates to the Christoffel
curvature coefficients in the chart-induced coordinate frame. -/
theorem rm13_eval_eq_christoffelCurvCoord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (i k j : CoordinateIdx E) :
    Rm13 x₀ alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
      ∑ m : CoordinateIdx E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
          alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀) := by
  rw [hRm (coordinateFrameAt (I := I) x₀ i)
    (coordinateFrameAt (I := I) x₀ k) (coordinateFrameAt (I := I) x₀ j)
    x₀ alpha]
  rw [hcurv i k j]
  change cotangentToDual (I := I) alpha
      (∑ m : CoordinateIdx E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m •
          coordinateFrameAt (I := I) x₀ m x₀) =
    ∑ m : CoordinateIdx E,
      christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
        alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [cotangentToDual_apply, smul_eq_mul]

/-- Coordinate Christoffel-form one-form Ricci identity.

This is the scalar-coordinate producer that should be discharged by expanding
`nabla0SFun` with the coordinate Christoffel formulas and commuting the scalar
second derivatives. -/
def OneFormThirdCommChristoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    Prop :=
  ∀ i k j : CoordinateIdx E,
    nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) -
      nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
        -∑ m : CoordinateIdx E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
            alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)

/-- The Christoffel-coordinate commutator implies the tensor one-form Ricci
identity once the supplied `Rm13` tensor is known to realize connection
curvature and the connection curvature has the Christoffel-coordinate expansion. -/
theorem one_form_third_comm_coord_of_christoffelCurv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x₀ alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  refine one_form_third_comm_of_coord_ijk (I := I) Rm13 alpha
    (coordinateFrameAt_toBasis (I := I) x₀) nabla2Alpha ?_
  intro i k j
  have hRmCoord := rm13_eval_eq_christoffelCurvCoord
    (I := I) cov Rm13 x₀ alpha hRm hcurv i k j
  have hcoord' := hcoord i k j
  simp only [coordinateFrameAt_toBasis_apply]
  rw [hRmCoord]
  exact hcoord'

end CoordinateChristoffelCurvature

end Realized
end RicciFlower
