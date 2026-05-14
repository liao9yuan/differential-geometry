import RicciFlower.RoughLaplacian
import RicciFlower.Realized.CurvatureTensor
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Tensor Ricci Identity Interfaces

This file gives short, reusable names for Ricci-identity statements without
depending on scalar Bochner.  The scalar Bochner file can specialize the
one-form interface by taking `alpha = du`, `dLapAlpha = d(Delta u)`, and
`curvatureVector = grad u`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Smooth covariant tensor sections used by the section-level
covariant-derivative API. -/
abbrev Tensor0SSection (s : ℕ) :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) s

/-- Smooth one-form sections used by the section-level covariant-derivative API. -/
abbrev OneFormSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 1

/-- Smooth covariant two-tensor sections used by the section-level derivative API. -/
abbrev TwoTensorSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 2

/-- A supplied `(0,2)` tensor field realizes the covariant derivative of a
bundled one-form at one point. -/
def NablaOneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    nablaAlpha x (vec2 (X x) Y) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X alpha x (fun _ : Fin 1 => Y)

/-- Section-level realization of `nablaAlpha = ∇ alpha`.

This is stronger than a single pointwise realization and is the information
needed to interpret a second derivative tensor as the true iterated derivative
of the original one-form. -/
def NablaOneFormSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, NablaOneFormRealizesAt (I := I) cov alpha (fun y => nablaAlpha y) x

/-- A supplied `(0,3)` tensor realizes the true second covariant derivative of a
bundled one-form at `x`: the bundled two-tensor section realizes `∇ alpha`,
and the supplied three-tensor is `∇(∇ alpha)` at `x`. -/
def Nabla2OneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
      nabla2Alpha (vec3 (X x) Y Z) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X nablaAlpha x (vec2 Y Z)

theorem nabla2OneFormRealizesAt_first
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha) :
    NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha :=
  h.1

theorem nabla2OneFormRealizesAt_apply
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 (X x) Y Z) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X nablaAlpha x (vec2 Y Z) :=
  h.2 X Y Z

/-- Build the existing pointwise second-one-form realization predicate from
two total covariant derivative realization steps. -/
theorem nabla2OneFormRealizesAt_of_totalNabla
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x
      (nabla2AlphaSec x) := by
  constructor
  · intro y X Y
    have h := h1 X y (fun _ : Fin 1 => Y)
    have hslots :
        Fin.cons (X y) (fun _ : Fin 1 => Y) = vec2 (I := I) (X y) Y := by
      funext i
      fin_cases i <;> simp [vec2, RicciFlower.Curvature.vec2]
    rw [hslots] at h
    exact h
  · intro X Y Z
    have h := h2 X x (vec2 (I := I) Y Z)
    have hslots :
        Fin.cons (X x) (vec2 (I := I) Y Z) = vec3 (I := I) (X x) Y Z := by
      funext i
      fin_cases i
      · simp [Fin.cons_zero, vec3, RicciFlower.Curvature.vec3]
      · change (vec2 (I := I) Y Z) 0 = Y
        simp [vec2, RicciFlower.Curvature.vec2]
      · change (vec2 (I := I) Y Z) 1 = Z
        simp [vec2, RicciFlower.Curvature.vec2]
    rw [hslots] at h
    exact h

/-- Component-level trailing-slot symmetry for a third covariant derivative
candidate `U`. -/
def Nabla2DuTrailingSymmCoord {Idx : Type*}
    (U : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i j k : Idx, U i j k = U i k j

/-- Component-level one-form Ricci identity, with the sign convention already
absorbed into `curvatureAction`. -/
def OneFormRicciIdentityCoord {Idx : Type*}
    (U curvatureAction : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i k j : Idx, U i k j - U k i j = curvatureAction i k j

/-- Component-level trace of the one-form curvature action gives the
Ricci-gradient component. -/
def CurvatureActionTraceEqualsRicGradCoord {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real) : Prop :=
  ∀ k : Idx,
    (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) = ricGrad k

/-- Pure finite-sum form of the Bochner one-form trace commutator.  The only
inputs are trailing symmetry, the one-form Ricci identity, and the traced
curvature-action identification. -/
theorem oneFormRicciTraceCommCoord_of_identities {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (U curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real)
    (h_symm : Nabla2DuTrailingSymmCoord U)
    (h_comm : OneFormRicciIdentityCoord U curvatureAction)
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv curvatureAction ricGrad) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k) =
        (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k)
        = ∑ i : Idx, ∑ j : Idx, gInv i j * U i k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_symm i j k]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * (U k i j + curvatureAction i k j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          have h : U i k j = U k i j + curvatureAction i k j := by
            calc
              U i k j = (U i k j - U k i j) + U k i j := by ring
              _ = curvatureAction i k j + U k i j := by rw [h_comm i k j]
              _ = U k i j + curvatureAction i k j := by ring
          rw [h]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) +
        (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) := by
          simp_rw [mul_add]
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
          rw [h_trace k]

section MixedComponentAlgebra

/-- Elementary multi-index probe.  It is the Kronecker delta at `L`. -/
def deltaMulti {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L A : Fin r -> Idx) : Real :=
  if A = L then 1 else 0

/-- Contract the upper multi-index of a mixed component array against a
covariant probe component array. -/
def contractUpper {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (theta : (Fin r -> Idx) -> Real)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) : Real :=
  ∑ L : Fin r -> Idx, theta L * beta L K

/-- Covariant curvature action on a component array.  The convention is
`R i j a b = R^a_{ijb}`, so covariant slots carry the negative sign. -/
def covariantCurvAction {Idx : Type*} [Fintype Idx] {n : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (A : (Fin n -> Idx) -> Real) (K : Fin n -> Idx) : Real :=
  -∑ q : Fin n, ∑ m : Idx,
    R i j m (K q) * A (Function.update K q m)

@[simp] theorem deltaMulti_self {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L : Fin r -> Idx) :
    deltaMulti L L = 1 := by
  simp [deltaMulti]

theorem deltaMulti_eq_zero_of_ne {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    {L A : Fin r -> Idx} (h : A ≠ L) :
    deltaMulti L A = 0 := by
  simp [deltaMulti, h]

@[simp] theorem contractUpper_deltaMulti {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (deltaMulti L) beta K = beta L K := by
  classical
  unfold contractUpper
  change (∑ A : Fin r -> Idx, deltaMulti L A * beta A K) = beta L K
  calc
    (∑ A : Fin r -> Idx, deltaMulti L A * beta A K)
        = deltaMulti L L * beta L K := by
          exact Fintype.sum_eq_single (α := Fin r -> Idx) (M := Real)
            (f := fun A : Fin r -> Idx => deltaMulti L A * beta A K) L
            (by
              intro A hA
              simp [deltaMulti, hA])
    _ = beta L K := by
          simp [deltaMulti]

private lemma deltaMulti_update_eq_one_iff {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    (L A : Fin r -> Idx) (p : Fin r) (m : Idx) :
    deltaMulti L (Function.update A p m) = 1 ↔
      Function.update A p m = L := by
  by_cases h : Function.update A p m = L
  · simp [deltaMulti, h]
  · simp [deltaMulti, h]

private lemma update_eq_of_update_eq {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    A = Function.update L p (A p) := by
  funext q
  by_cases hpq : q = p
  · subst hpq
    simp
  · have hq := congrFun h q
    simpa [Function.update, hpq] using hq

private lemma update_value_eq_of_update_eq {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    m = L p := by
  have hp := congrFun h p
  simpa using hp

private lemma update_update_same_apply {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    (L : Fin r -> Idx) (p : Fin r) (m : Idx) :
    Function.update (Function.update L p m) p (L p) = L := by
  funext q
  by_cases hpq : q = p
  · subst hpq
    simp
  · simp [Function.update, hpq]

private def updateSwapEquiv {Idx : Type*} [DecidableEq Idx] {r : ℕ}
    (p : Fin r) : ((Fin r -> Idx) × Idx) ≃ ((Fin r -> Idx) × Idx) where
  toFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  invFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  left_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp
  right_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp

private lemma sum_delta_update_pair {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (p : Fin r)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    (∑ A : Fin r -> Idx, ∑ m : Idx,
      R i j m (A p) * deltaMulti L (Function.update A p m) * beta A K)
      =
    ∑ m : Idx, R i j (L p) m *
      beta (Function.update L p m) K := by
  classical
  let F : ((Fin r -> Idx) × Idx) -> Real := fun Am =>
    R i j Am.2 (Am.1 p) *
      deltaMulti L (Function.update Am.1 p Am.2) * beta Am.1 K
  let G : ((Fin r -> Idx) × Idx) -> Real := fun Bm =>
    R i j (Bm.1 p) Bm.2 * deltaMulti L Bm.1 *
      beta (Function.update Bm.1 p Bm.2) K
  have hFG : ∑ Am, F Am = ∑ Bm, G Bm := by
    refine Fintype.sum_equiv (updateSwapEquiv (Idx := Idx) p) F G ?_
    intro Am
    cases Am with
    | mk A m =>
        simp [F, G, updateSwapEquiv]
  have hG :
      (∑ Bm, G Bm) =
        ∑ m : Idx, R i j (L p) m *
          beta (Function.update L p m) K := by
    calc
      (∑ Bm : (Fin r -> Idx) × Idx, G Bm)
          = ∑ B : Fin r -> Idx, ∑ m : Idx, G (B, m) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ B : Fin r -> Idx,
            (if B = L then
              ∑ m : Idx, R i j (L p) m *
                beta (Function.update L p m) K
            else 0) := by
              refine Fintype.sum_congr _ _ ?_
              intro B
              by_cases hB : B = L
              · subst hB
                simp [G, deltaMulti]
              · simp [G, deltaMulti, hB]
      _ = ∑ m : Idx, R i j (L p) m *
            beta (Function.update L p m) K := by
              let S : Real := ∑ m : Idx, R i j (L p) m *
                beta (Function.update L p m) K
              change (∑ B : Fin r -> Idx,
                (if B = L then S else 0)) = S
              calc
                (∑ B : Fin r -> Idx, (if B = L then S else 0))
                    = (if L = L then S else 0) := by
                      refine Fintype.sum_eq_single
                        (α := Fin r -> Idx) (M := Real)
                        (f := fun B : Fin r -> Idx =>
                          if B = L then S else 0) L ?_
                      intro B hB
                      simp [hB]
                _ = S := by simp
  calc
    (∑ A : Fin r -> Idx, ∑ m : Idx,
      R i j m (A p) * deltaMulti L (Function.update A p m) * beta A K)
        = ∑ Am : (Fin r -> Idx) × Idx, F Am := by
            rw [Fintype.sum_prod_type]
    _ = ∑ Bm : (Fin r -> Idx) × Idx, G Bm := hFG
    _ = ∑ m : Idx, R i j (L p) m *
          beta (Function.update L p m) K := hG

private lemma contractUpper_covariantCurvAction_deltaMulti
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K =
      -∑ p : Fin r, ∑ m : Idx,
        R i j (L p) m * beta (Function.update L p m) K := by
  classical
  unfold contractUpper covariantCurvAction
  simp_rw [neg_mul]
  calc
    (∑ A : Fin r -> Idx,
      -((∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m)) *
        beta A K))
        = -∑ A : Fin r -> Idx, (∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m)) *
            beta A K := by
            simp [Finset.sum_neg_distrib]
    _ = -∑ A : Fin r -> Idx, ∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m) *
            beta A K := by
            congr 1
            refine Fintype.sum_congr _ _ ?_
            intro A
            simp [Finset.sum_mul, mul_assoc]
    _ = -∑ q : Fin r, ∑ A : Fin r -> Idx, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m) *
            beta A K := by
            rw [Finset.sum_comm]
    _ = -∑ q : Fin r, ∑ m : Idx,
          R i j (L q) m * beta (Function.update L q m) K := by
            congr 1
            refine Fintype.sum_congr _ _ ?_
            intro q
            exact sum_delta_update_pair R i j L q beta K

/-- Pure component algebra behind Remark 14.13.  Contract a mixed tensor
against an elementary covariant probe, use the covariant curvature action on
the contraction and on the probe, and the upper-slot curvature terms appear
with the opposite sign. -/
theorem contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (K : Fin s -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) :
    covariantCurvAction R i j
        (contractUpper (deltaMulti L) beta) K -
      contractUpper
        (covariantCurvAction R i j (deltaMulti L)) beta K
      =
        (∑ p : Fin r, ∑ m : Idx,
          R i j (L p) m * beta (Function.update L p m) K) -
        (∑ q : Fin s, ∑ m : Idx,
          R i j m (K q) * beta L (Function.update K q m)) := by
  classical
  rw [contractUpper_covariantCurvAction_deltaMulti]
  unfold covariantCurvAction
  simp_rw [contractUpper_deltaMulti]
  ring

/-- Curvature action on mixed `(r,s)` components.  The convention is
`R i j a b = R^a_{ijb}`.  Upper slots have the positive sign and lower slots
have the covariant negative sign. -/
def mixedCurvAction {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (L : Fin r -> Idx) (K : Fin s -> Idx) : Real :=
  (∑ p : Fin r, ∑ m : Idx,
    R i j (L p) m * beta (Function.update L p m) K) -
  (∑ q : Fin s, ∑ m : Idx,
    R i j m (K q) * beta L (Function.update K q m))

/-- Component form of the mixed `(r,s)` Ricci identity for a precomputed
commutator component array. -/
def MixedRicciIdentityCoord {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) : Prop :=
  ∀ L K, commBeta L K = mixedCurvAction R i j beta L K

/-- Derive the mixed component Ricci identity from the covariant identity
applied to an elementary probe contraction and to the probe itself.

The input `hcontract` is the product rule for the commutator acting on
`contractUpper (deltaMulti L) beta`; `hcontractCov` and `hprobeCov` are the
already-known covariant Ricci identities for the contracted `(0,s)` tensor and
the probe `(0,r)` tensor. -/
theorem mixedRicciIdentityCoord_of_contract_probe_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe : (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcontract : ∀ L K,
      contractUpper (deltaMulti L) commBeta K =
        commContract L K - contractUpper (commProbe L) beta K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta := by
  classical
  intro L K
  have hprobeContract :
      contractUpper (commProbe L) beta K =
        contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
    unfold contractUpper
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [hprobeCov L A]
  have hcomm :
      commBeta L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K -
          contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
    calc
      commBeta L K = contractUpper (deltaMulti L) commBeta K := by
          rw [contractUpper_deltaMulti]
      _ = commContract L K - contractUpper (commProbe L) beta K := hcontract L K
      _ = covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K -
            contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
          rw [hcontractCov L K, hprobeContract]
  rw [hcomm, mixedCurvAction]
  exact contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction R i j L K beta

/-- Algebraic cancellation behind the commutator product rule for an
upper-slot contraction.

The hypotheses are the two second-product-rule expansions for derivative
orders `ij` and `ji`.  The conclusion is the commutator form:
`theta ⋅ commBeta = commContract - commTheta ⋅ beta`. -/
theorem contractUpper_commutator_of_second_product_rules
    {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (theta theta_i theta_j theta_ij theta_ji : (Fin r -> Idx) -> Real)
    (beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (contract_ij contract_ji : (Fin s -> Idx) -> Real)
    (hij : ∀ K,
      contract_ij K =
        contractUpper theta_ij beta K +
          contractUpper theta_j beta_i K +
          contractUpper theta_i beta_j K +
          contractUpper theta beta_ij K)
    (hji : ∀ K,
      contract_ji K =
        contractUpper theta_ji beta K +
          contractUpper theta_i beta_j K +
          contractUpper theta_j beta_i K +
          contractUpper theta beta_ji K)
    (K : Fin s -> Idx) :
    contractUpper theta (fun L K => beta_ij L K - beta_ji L K) K =
      (contract_ij K - contract_ji K) -
        contractUpper (fun L => theta_ij L - theta_ji L) beta K := by
  classical
  have hright :
      contractUpper theta (fun L K => beta_ij L K - beta_ji L K) K =
        contractUpper theta beta_ij K - contractUpper theta beta_ji K := by
    unfold contractUpper
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hleft :
      contractUpper (fun L => theta_ij L - theta_ji L) beta K =
        contractUpper theta_ij beta K - contractUpper theta_ji beta K := by
    unfold contractUpper
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hright, hleft, hij K, hji K]
  ring

/-- Component-level mixed Ricci identity from second-product-rule identities.

This packages the previous theorem into the input shape expected by
`mixedRicciIdentityCoord_of_contract_probe_identities`.  The remaining
geometric frontier is to supply the second-product-rule expansions for the
actual contraction of a probe tensor against a mixed tensor. -/
theorem mixedRicciIdentityCoord_of_second_product_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract contract_ij contract_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe probe_i probe_j probe_ij probe_ji :
      (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcommBeta : ∀ L K, commBeta L K = beta_ij L K - beta_ji L K)
    (hcommContract : ∀ L K, commContract L K = contract_ij L K - contract_ji L K)
    (hcommProbe : ∀ L A, commProbe L A = probe_ij L A - probe_ji L A)
    (hprod_ij : ∀ L K,
      contract_ij L K =
        contractUpper (probe_ij L) beta K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (deltaMulti L) beta_ij K)
    (hprod_ji : ∀ L K,
      contract_ji L K =
        contractUpper (probe_ji L) beta K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (deltaMulti L) beta_ji K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta := by
  classical
  refine mixedRicciIdentityCoord_of_contract_probe_identities
    R i j commBeta beta commContract commProbe ?_ hcontractCov hprobeCov
  intro L K
  have hprod :=
    contractUpper_commutator_of_second_product_rules
      (Idx := Idx) (r := r) (s := s)
      (theta := deltaMulti L)
      (theta_i := probe_i L)
      (theta_j := probe_j L)
      (theta_ij := probe_ij L)
      (theta_ji := probe_ji L)
      (beta := beta)
      (beta_i := beta_i)
      (beta_j := beta_j)
      (beta_ij := beta_ij)
      (beta_ji := beta_ji)
      (contract_ij := contract_ij L)
      (contract_ji := contract_ji L)
      (hij := hprod_ij L)
      (hji := hprod_ji L)
      K
  calc
    contractUpper (deltaMulti L) commBeta K =
        contractUpper (deltaMulti L)
          (fun A K => beta_ij A K - beta_ji A K) K := by
          unfold contractUpper
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [hcommBeta A K]
    _ = (contract_ij L K - contract_ji L K) -
        contractUpper (fun A => probe_ij L A - probe_ji L A) beta K := hprod
    _ = commContract L K - contractUpper (commProbe L) beta K := by
          rw [hcommContract L K]
          congr 1
          unfold contractUpper
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [hcommProbe L A]

end MixedComponentAlgebra

/-- Pointwise Ricci identity for the third covariant derivative of a one-form.

With the realized convention `Rm13 alpha X Y Z = alpha (R(X,Y)Z)`, the
covector commutator carries the negative sign:
`∇² alpha(X,Y,Z) - ∇² alpha(Y,X,Z) = -Rm13(alpha,X,Y,Z)`. -/
def OneFormThirdCovDerivCommAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z)

theorem one_form_third_covDeriv_comm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  h X Y Z

/-- Swap the first two slots of a `(0,3)` tensor. -/
def swapFirstTwo0S {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  A.domDomCongr (Equiv.swap (0 : Fin 3) 1)

@[simp] theorem swapFirstTwo0S_apply_vec3 {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    swapFirstTwo0S (I := I) A (vec3 X Y Z) = A (vec3 Y X Z) := by
  change A (fun i => (vec3 X Y Z) ((Equiv.swap (0 : Fin 3) 1) i)) =
    A (vec3 Y X Z)
  congr 1
  funext q
  fin_cases q <;> simp [Equiv.swap_apply_def, vec3, RicciFlower.Curvature.vec3]

/-- Promote the coordinate form of the one-form Ricci identity to the tensor
identity at a point. -/
theorem one_form_third_comm_of_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ slots : Fin 3 -> Idx,
      nabla2Alpha (fun a => basis (slots a)) -
        nabla2Alpha (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          -Rm13 x alpha (fun a => basis (slots a))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  have htensor :
      nabla2Alpha - swapFirstTwo0S (I := I) nabla2Alpha = -Rm13 x alpha := by
    apply ext0S_basis (I := I) basis
    intro slots
    simpa [component0S, swapFirstTwo0S] using hcoord slots
  intro X Y Z
  have h_eval := congrArg
    (fun A :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x =>
        A (vec3 X Y Z)) htensor
  simpa using h_eval

/-- A component-indexed version of `one_form_third_comm_of_coord`. -/
theorem one_form_third_comm_of_coord_ijk
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ i k j : Idx,
      nabla2Alpha (vec3 (basis i) (basis k) (basis j)) -
        nabla2Alpha (vec3 (basis k) (basis i) (basis j)) =
          -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_of_coord (I := I) Rm13 alpha basis nabla2Alpha fun slots => by
    have h := hcoord (slots 0) (slots 1) (slots 2)
    have hslots :
        (fun a => basis (slots a)) =
          vec3 (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [vec3, RicciFlower.Curvature.vec3]
    have hswap :
        (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          vec3 (basis (slots 1)) (basis (slots 0)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [Equiv.swap_apply_def, vec3, RicciFlower.Curvature.vec3]
    simpa [hslots, hswap] using h

/-- Pointwise trailing-slot symmetry of the second covariant derivative of a
one-form. For `alpha = du`, this is the Hessian symmetry input preserved in the
last two slots of `∇² alpha`. -/
def OneFormLastTwoSymmAt {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y)

theorem one_form_last_two_symm {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y) :=
  h X Y Z

/-- The traced Hessian-derivative term for a one-form candidate.  In the
scalar specialization `alpha = du`, this is the term that realizes
`d (Delta u)`. -/
def traceNablaOneFormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))

/-- Pointwise one-form trace commutator with an explicit curvature vector:
`tr_g ∇²α(.,.,Y) = tr_g ∇²α(Y,.,.) + Ric(Y,V)`. -/
def OneFormRicciTraceCommWithVectorAt
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    roughLap1FormAt (I := I) basis gInv nabla2Alpha Y =
      traceNablaOneFormAt (I := I) basis gInv nabla2Alpha Y +
        Ric x (vec2 Y curvatureVector)

/-- Coordinate components of a supplied second covariant derivative of a
one-form in a pointwise tangent basis. -/
def nabla2OneFormCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2Alpha (vec3 (basis i) (basis j) (basis k))

/-- Signed curvature-action components for a one-form.  The minus sign is the
covector curvature-action sign for the convention
`Rm13 alpha X Y Z = alpha (R(X,Y)Z)`. -/
def curvatureActionOnOneFormCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))

/-- Ricci-vector components in a pointwise tangent basis. -/
def ricciVectorCoord
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (curvatureVector : TangentSpace I x)
    (k : Idx) : Real :=
  Ric x (vec2 (basis k) curvatureVector)

theorem nabla2OneFormTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha) :
    Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha) := by
  intro i j k
  exact hsymm (basis i) (basis j) (basis k)

theorem oneFormRicciIdentityCoord_of_tensor
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis) := by
  intro i k j
  exact hcomm (basis i) (basis k) (basis j)

/-- Coordinate-basis form of the trace commutator, obtained from the three
component identities. -/
theorem oneFormRicciTraceComm_basisCoord_of_identities
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h_symm : Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha))
    (h_comm : OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis))
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
      (ricciVectorCoord (I := I) Ric basis curvatureVector)) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha i j k) =
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha k i j) +
          ricciVectorCoord (I := I) Ric basis curvatureVector k :=
  oneFormRicciTraceCommCoord_of_identities gInv
    (nabla2OneFormCoord (I := I) basis nabla2Alpha)
    (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
    (ricciVectorCoord (I := I) Ric basis curvatureVector)
    h_symm h_comm h_trace

theorem metricTraceInput_one_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    metricTraceInput (I := I) X Y (fun _ : Fin 1 => Z) = vec3 X Y Z := by
  funext q
  fin_cases q
  · simp [metricTraceInput, vec3, RicciFlower.Curvature.vec3]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ 0) = Y
    rw [Fin.cases_succ, Fin.cases_zero]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ (Fin.succ 0)) = Z
    rw [Fin.cases_succ, Fin.cases_succ]

/-- Trace-level Bochner commutator consumer from the untraced one-form Ricci
identity. This is only finite-sum algebra: the actual geometric proof of the
untraced commutator, trailing-slot symmetry, and curvature trace is supplied by
the three pointwise hypotheses. -/
theorem oneForm_ricci_trace_comm_of_third_comm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (hcurv : ∀ Y : TangentSpace I x,
      -∑ i : Idx, ∑ j : Idx,
        gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j)) =
          Ric x (vec2 Y curvatureVector)) :
    OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv curvatureVector
      nabla2Alpha := by
  intro Y
  unfold roughLap1FormAt roughLap0SAt metricTrace0S2InBasis
    traceNablaOneFormAt
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nabla2Alpha (metricTraceInput (I := I) (basis i) (basis j)
            (fun _ : Fin 1 => Y)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j * nabla2Alpha (vec3 (basis i) (basis j) Y) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [metricTraceInput_one_eq_vec3]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 (basis i) Y (basis j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsymm (basis i) (basis j) Y]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (nabla2Alpha (vec3 Y (basis i) (basis j)) -
              Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          have h := hcomm (basis i) Y (basis j)
          calc
            nabla2Alpha (vec3 (basis i) Y (basis j))
                = (nabla2Alpha (vec3 (basis i) Y (basis j)) -
                    nabla2Alpha (vec3 Y (basis i) (basis j))) +
                    nabla2Alpha (vec3 Y (basis i) (basis j)) := by ring
            _ = -Rm13 x alpha (vec3 (basis i) Y (basis j)) +
                  nabla2Alpha (vec3 Y (basis i) (basis j)) := by rw [h]
            _ = nabla2Alpha (vec3 Y (basis i) (basis j)) -
                  Rm13 x alpha (vec3 (basis i) Y (basis j)) := by ring_nf
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        (-∑ i : Idx, ∑ j : Idx,
          gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          simp_rw [mul_sub]
          simp_rw [Finset.sum_sub_distrib]
          ring
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        Ric x (vec2 Y curvatureVector) := by
          rw [hcurv Y]

/-- One-form Ricci identity interface at a point:
`roughAlpha = dLapAlpha + Ric(., curvatureVector)`. -/
def RicciIdentityOneFormAt
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector)

theorem ricci_identity_one_form
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x)
    (h : RicciIdentityOneFormAt (I := I) Ric roughAlpha dLapAlpha curvatureVector)
    (Y : TangentSpace I x) :
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector) :=
  h Y

/-- Freeze all covariant slots of a `(0,s)` tensor except slot `q`, producing
the one-form obtained by varying only that slot. -/
def oneFormAtSlot0S {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I)
    { toFun := fun W : TangentSpace I x => alpha (Function.update slots q W)
      map_add' := by
        intro A B
        exact alpha.map_update_add slots q A B
      map_smul' := by
        intro c A
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }

/-- Alias for `oneFormAtSlot0S`, matching the geometric wording "freeze all
but one tensor slot." -/
abbrev freezeSlot0SAt {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  oneFormAtSlot0S (I := I) alpha slots q

@[simp] theorem oneFormAtSlot0S_apply {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) (W : TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots q (fun _ : Fin 1 => W) =
      alpha (Function.update slots q W) := by
  simp [oneFormAtSlot0S]

/-- Slotwise curvature action on a covariant tensor, expressed using the
existing convention `Rm13 alpha X Y Z = alpha (R(X,Y)Z)`.  Covectors carry the
negative curvature sign. -/
def curvatureAction0SAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  -∑ q : Fin s,
    Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
      (vec3 X Y (slots q))

/-- Torsion correction term in the invariant `(0,s)` Ricci identity. -/
def torsionCorrection0SAt {x : M} {s : ℕ}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (T : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  nablaAlpha (Fin.cons T slots)

/-- Invariant pointwise Ricci identity for covariant tensors.  The first two
slots of `nabla2Alpha` are the derivative slots. -/
def Tensor0SRicciIdentityAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots

/-- Invariant pointwise Ricci identity for covariant tensors with the torsion
correction retained. -/
def Tensor0SRicciIdentityWithTorsionAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (torsion : TangentSpace I x → TangentSpace I x → TangentSpace I x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (torsion X Y) slots

@[simp] theorem oneFormAtSlot0S_fin1_eq {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (slots : Fin 1 → TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots 0 = alpha := by
  ext v
  have hv : (fun _ : Fin 1 => v 0) = v := by
    funext q
    fin_cases q
    rfl
  rw [← hv, oneFormAtSlot0S_apply]
  have hupdate :
      Function.update slots (0 : Fin 1) (v 0) = fun _ : Fin 1 => v 0 := by
    funext q
    fin_cases q
    simp
  simp [hupdate]

theorem tensor0S_ricciIdentity_one_of_oneForm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext q
    fin_cases q
    rfl
  have hcomm := h X Y (slots 0)
  rw [hslots]
  rw [metricTraceInput_one_eq_vec3, metricTraceInput_one_eq_vec3]
  simp [curvatureAction0SAt, hcomm]

theorem oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y Z
  have h0 := h X Y (fun _ : Fin 1 => Z)
  simpa [Tensor0SRicciIdentityAt, curvatureAction0SAt,
    metricTraceInput_one_eq_vec3] using h0

theorem tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha ↔
      OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  ⟨oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one (I := I)
      Rm13 alpha nabla2Alpha,
    tensor0S_ricciIdentity_one_of_oneForm (I := I) Rm13 alpha nabla2Alpha⟩

/-- A supplied `(0,s+1)` tensor field realizes the covariant derivative of a
bundled `(0,s)` tensor at one point. -/
def Nabla0SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (slots : Fin s → TangentSpace I x),
    nablaAlpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X alpha x slots

/-- Section-level realization of `nablaAlpha = ∇ alpha` for `(0,s)` tensors. -/
def Nabla0SSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)) : Prop :=
  ∀ x : M, Nabla0SRealizesAt (I := I) s cov alpha (fun y => nablaAlpha y) x

/-- A supplied `(0,s+2)` tensor realizes the true second covariant derivative of
a bundled `(0,s)` tensor at one point. -/
def Nabla20SRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (alpha : Tensor0SSection (I := I) (M := M) s)
    (nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
        (slots : Fin (s + 1) → TangentSpace I x),
      nabla2Alpha (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + 1) cov X nablaAlpha x slots

/-- Definition 14.5 for a realized first covariant derivative of a `(0,s)`
tensor section. -/
theorem Nabla0SSectionRealizes.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x

/-- Definition 14.5 for a realized first covariant derivative, evaluated on an
arbitrary tangent vector in the derivative slot and smooth moving tensor slots.
The proof extends the tangent vector to a smooth section and reuses
`eval_smooth_slots`. -/
theorem Nabla0SSectionRealizes.eval_point_vector_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    {x : M}
    (W : TangentSpace I x)
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nablaAlpha x (Fin.cons W (fun q : Fin s => V q x)) =
      extDerivFun (I := I)
        (fun y : M => alpha y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        alpha x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := Nabla0SSectionRealizes.eval_smooth_slots
    (I := I) h Wsec V x
  simpa [hWsec] using h0

/-- Definition 14.5 for a realized first covariant derivative with only `C¹`
moving slots. -/
theorem Nabla0SSectionRealizes.eval_C1_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    (h : Nabla0SSectionRealizes (I := I) s cov alpha nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x) :
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x)) =
      extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
        x (X x) -
        ∑ a : Fin s,
          alpha x
            (Function.update (fun b : Fin s => V b x) a
              ((cov (V a) x) (X x))) := by
  calc
    nablaAlpha x (Fin.cons (X x) (fun a : Fin s => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X alpha x (fun a : Fin s => V a x) := by
          exact h x X (fun a : Fin s => V a x)
    _ = extDerivFun (I := I) (fun p : M => alpha p (fun a : Fin s => V a p))
          x (X x) -
          ∑ a : Fin s,
            alpha x
              (Function.update (fun b : Fin s => V b x) a
                ((cov (V a) x) (X x))) := by
          exact nabla0SFun_eval_C1_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V alpha x hV_at

/-- Definition 14.5 for a realized second covariant derivative of a `(0,s)`
tensor section, applied to the outer derivative slot and smooth moving
remaining slots. -/
theorem Nabla20SRealizesAt.eval_smooth_slots
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : ℕ} {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {alpha : Tensor0SSection (I := I) (M := M) s}
    {nablaAlpha : Tensor0SSection (I := I) (M := M) (s + 1)}
    {x : M}
    {nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x}
    (h : Nabla20SRealizesAt (I := I) s cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x)) =
      extDerivFun (I := I) (fun p : M => nablaAlpha p
          (fun a : Fin (s + 1) => V a p)) x (X x) -
        ∑ a : Fin (s + 1),
          nablaAlpha x
            (Function.update (fun b : Fin (s + 1) => V b x) a
              ((cov (fun p : M => V a p) x) (X x))) := by
  calc
    nabla2Alpha (Fin.cons (X x) (fun a : Fin (s + 1) => V a x))
        = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (s + 1) cov X nablaAlpha x
            (fun a : Fin (s + 1) => V a x) := by
          exact h.2 X (fun a : Fin (s + 1) => V a x)
    _ = extDerivFun (I := I) (fun p : M => nablaAlpha p
            (fun a : Fin (s + 1) => V a p)) x (X x) -
          ∑ a : Fin (s + 1),
            nablaAlpha x
              (Function.update (fun b : Fin (s + 1) => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            cov X V nablaAlpha x

private theorem mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using
        (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real))
          (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

private theorem extDerivFun_finset_sum_at
    {ι : Type*} (t : Finset ι) (f : ι → M → Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x :=
        mdiffAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

private theorem extDerivFun_neg_at
    {f : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    extDerivFun (I := I) (fun y : M => -f y) x v =
      -extDerivFun (I := I) f x v := by
  have hfun : (fun y : M => -f y) = ((fun _ : M => (-1 : Real)) • f) := by
    ext y
    simp
  rw [hfun]
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => (-1 : Real)) (g := f)
    (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (-1 : Real)) (x := x))
    hf v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul] using hprod

private theorem extDerivFun_sub_at
    {f g : M → Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y - g y) x v =
      extDerivFun (I := I) f x v - extDerivFun (I := I) g x v := by
  have hneg := extDerivFun_neg_at (I := I) (f := g) (x := x) v hg
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := fun y : M => -g y)
    (x := x) hf hg.neg) v)
  simpa [Pi.add_apply, sub_eq_add_neg, hneg] using hadd

section PureUpdateAlgebra

private lemma update_update_ne_comm
    {ι V : Type*} [DecidableEq ι]
    (slots : ι → V) {p q : ι} (hpq : p ≠ q)
    (A B : V) :
    Function.update (Function.update slots q A) p B =
      Function.update (Function.update slots p B) q A := by
  funext r
  by_cases hrp : r = p
  · subst r
    simp [Function.update, hpq]
  · by_cases hrq : r = q
    · subst r
      simp [Function.update, hrp]
    · simp [Function.update, hrp, hrq]

private lemma double_sum_sub_eq_diag_sub_diag_of_offdiag_swap
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    (F G : ι → ι → A)
    (h : ∀ q p, q ≠ p → F q p = G p q) :
    (∑ q, ∑ p, F q p) - (∑ q, ∑ p, G q p) =
      (∑ q, F q q) - (∑ q, G q q) := by
  classical
  have hdecomp (H : ι → ι → A) :
      (∑ q, ∑ p, H q p) =
        (∑ q, H q q) + (∑ q, ∑ p, if p = q then 0 else H q p) := by
    calc
      (∑ q, ∑ p, H q p)
          =
          ∑ q, ∑ p,
            ((if p = q then H q p else 0) + (if p = q then 0 else H q p)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            refine Finset.sum_congr rfl ?_
            intro p hp
            by_cases hpq : p = q <;> simp [hpq]
      _ =
          ∑ q,
            ((∑ p, if p = q then H q p else 0) +
              (∑ p, if p = q then 0 else H q p)) := by
            simp [Finset.sum_add_distrib]
      _ =
          ∑ q, (H q q + (∑ p, if p = q then 0 else H q p)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hsingle :
                (∑ p : ι, if p = q then H q p else (0 : A)) = H q q := by
              simp
            rw [hsingle]
      _ =
          (∑ q, H q q) + (∑ q, ∑ p, if p = q then 0 else H q p) := by
            simp [Finset.sum_add_distrib]
  have hoff :
      (∑ q, ∑ p, if p = q then 0 else F q p) =
        (∑ q, ∑ p, if p = q then 0 else G q p) := by
    calc
      (∑ q, ∑ p, if p = q then 0 else F q p)
          = (∑ p, ∑ q, if p = q then 0 else F q p) := by
            rw [Finset.sum_comm]
      _ = (∑ p, ∑ q, if p = q then 0 else G p q) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            refine Finset.sum_congr rfl ?_
            intro q hq
            by_cases hpq : p = q
            · simp [hpq]
            · have hqp : q ≠ p := fun h' => hpq h'.symm
              simp [hpq, h q p hqp]
      _ = (∑ q, ∑ p, if p = q then 0 else G q p) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            refine Finset.sum_congr rfl ?_
            intro q hq
            by_cases hpq : p = q
            · subst q
              simp
            · have hqp : q ≠ p := fun h' => hpq h'.symm
              simp [hpq, hqp]
  calc
    (∑ q, ∑ p, F q p) - (∑ q, ∑ p, G q p)
        =
        ((∑ q, F q q) + (∑ q, ∑ p, if p = q then 0 else F q p)) -
          ((∑ q, G q q) + (∑ q, ∑ p, if p = q then 0 else G q p)) := by
          rw [hdecomp F, hdecomp G]
    _ = (∑ q, F q q) - (∑ q, G q q) := by
          rw [hoff]
          abel

private lemma double_update_sum_cancel_diag
    {ι V A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    (eval : (ι → V) → A)
    (slots X Y XY YX : ι → V) :
    - (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (Y q))
            p
            (if p = q then XY q else X p)))
      + (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (X q))
            p
            (if p = q then YX q else Y p)))
      =
    - (∑ q, eval (Function.update slots q (XY q)))
      + (∑ q, eval (Function.update slots q (YX q))) := by
  classical
  let F : ι → ι → A :=
    fun q p =>
      eval
        (Function.update
          (Function.update slots q (Y q))
          p
          (if p = q then XY q else X p))
  let G : ι → ι → A :=
    fun q p =>
      eval
        (Function.update
          (Function.update slots q (X q))
          p
          (if p = q then YX q else Y p))
  let SF : A := ∑ q, ∑ p, F q p
  let SG : A := ∑ q, ∑ p, G q p
  let DF0 : A := ∑ q, F q q
  let DG0 : A := ∑ q, G q q
  let DF : A := ∑ q, eval (Function.update slots q (XY q))
  let DG : A := ∑ q, eval (Function.update slots q (YX q))
  have hswap : ∀ q p, q ≠ p → F q p = G p q := by
    intro q p hqp
    dsimp [F, G]
    have hpq : p ≠ q := fun h' => hqp h'.symm
    rw [if_neg hpq, if_neg hqp]
    exact congrArg eval
      (update_update_ne_comm slots (p := p) (q := q) hpq (Y q) (X p))
  have hdiag0 : SF - SG = DF0 - DG0 := by
    dsimp [SF, SG, DF0, DG0]
    exact double_sum_sub_eq_diag_sub_diag_of_offdiag_swap F G hswap
  have hDF : DF0 = DF := by
    dsimp [DF0, DF, F]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp
  have hDG : DG0 = DG := by
    dsimp [DG0, DG, G]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp
  have hdiag : SF - SG = DF - DG := by
    rw [hdiag0, hDF, hDG]
  change -SF + SG = -DF + DG
  calc
    -SF + SG = -(SF - SG) := by abel
    _ = -(DF - DG) := by rw [hdiag]
    _ = -DF + DG := by abel

end PureUpdateAlgebra

private lemma update_finCons_zero
    {s : ℕ} {V : Type*}
    (head newHead : V) (tail : Fin s → V) :
    Function.update (Fin.cons head tail : Fin (s + 1) → V)
        (0 : Fin (s + 1)) newHead =
      (Fin.cons newHead tail : Fin (s + 1) → V) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [Function.update]
  · intro q
    have hne : q.succ ≠ (0 : Fin (s + 1)) := Fin.succ_ne_zero q
    simp [Function.update, hne]

private lemma update_finCons_succ
    {s : ℕ} {V : Type*}
    (head : V) (tail : Fin s → V) (q : Fin s) (newTail : V) :
    Function.update (Fin.cons head tail : Fin (s + 1) → V) q.succ newTail =
      (Fin.cons head (Function.update tail q newTail) : Fin (s + 1) → V) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · have hne : (0 : Fin (s + 1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
    simp [Function.update, hne]
  · intro r
    by_cases hrq : r = q
    · subst r
      simp
    · simp [hrq]

private lemma finCons_update_tail_eq_update_finCons_succ
    {s : ℕ} {V : Type*}
    (head : V) (tail : Fin s → V) (q : Fin s) (newTail : V) :
    (Fin.cons head (Function.update tail q newTail) : Fin (s + 1) → V) =
      Function.update (Fin.cons head tail : Fin (s + 1) → V) q.succ newTail :=
  (update_finCons_succ head tail q newTail).symm

private lemma sum_update_finCons
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head dHead : V) (tail dTail : Fin s → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        ((Fin.cons dHead dTail : Fin (s + 1) → V) a))) =
      F (Fin.cons dHead tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (dTail q))) := by
  rw [Fin.sum_univ_succ]
  have h0 :
      Function.update (Fin.cons head tail : Fin (s + 1) → V)
          (0 : Fin (s + 1)) dHead =
        (Fin.cons dHead tail : Fin (s + 1) → V) := by
    exact update_finCons_zero (s := s) (V := V) head dHead tail
  simp only [Fin.cons_zero]
  rw [h0]
  simp_rw [Fin.cons_succ]
  simp_rw [update_finCons_succ]

private lemma sum_update_finCons_raw
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head : V) (tail : Fin s → V) (d : Fin (s + 1) → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        (d a))) =
      F (Fin.cons (d 0) tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (d q.succ))) := by
  have hd :
      (Fin.cons (d 0) (fun q : Fin s => d q.succ) :
          Fin (s + 1) → V) = d := by
    funext a
    refine Fin.cases ?_ ?_ a
    · simp
    · intro q
      simp
  simpa [hd] using
    sum_update_finCons
      (F := F) (head := head) (dHead := d 0) (tail := tail)
      (dTail := fun q : Fin s => d q.succ)

private lemma tensor0S_update_curvature_diag
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s)
    (DXY DYX DB : TangentSpace I x) :
    -alpha (Function.update slots q DXY) +
        alpha (Function.update slots q DYX) +
        alpha (Function.update slots q DB) =
      -alpha (Function.update slots q (DXY - DYX - DB)) := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => alpha (Function.update slots q T)
      map_add' := by
        intro U V
        exact alpha.map_update_add slots q U V
      map_smul' := by
        intro c U
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }
  change -L DXY + L DYX + L DB = -L (DXY - DYX - DB)
  rw [map_sub, map_sub]
  abel

private lemma metricTraceInput_eq_finCons {s : ℕ} {x : M}
    (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    metricTraceInput (I := I) X Y tail =
      Fin.cons X (Fin.cons Y tail) := by
  rfl

private lemma curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {Rm13 : Tensor13Section (I := I) (M := M)}
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13) :
    curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
        (fun q : Fin s => Vsec q x) =
      -∑ q : Fin s,
        alpha
          (Function.update (fun r : Fin s => Vsec r x) q
            ((connectionRiemannCurvatureField (I := I) cov
              (fun p : M => Xsec p) (fun p : M => Ysec p)
              (fun p : M => Vsec q p)) x)) := by
  classical
  unfold curvatureAction0SAt
  congr 1
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hRm := hRm13 (fun p : M => Xsec p) (fun p : M => Ysec p)
    (fun p : M => Vsec q p) x
    (oneFormAtSlot0S (I := I) alpha (fun r : Fin s => Vsec r x) q)
  simpa [cotangentToDual_apply, oneFormAtSlot0S_apply] using hRm

private lemma first_slot_torsionCorrection_eq
    {s : ℕ} {x : M}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (A B C : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    nablaAlpha (Fin.cons C slots) - nablaAlpha (Fin.cons A slots) +
        nablaAlpha (Fin.cons B slots) =
      -torsionCorrection0SAt (I := I) nablaAlpha (A - B - C) slots := by
  let L : TangentSpace I x →ₗ[Real] Real :=
    { toFun := fun T => nablaAlpha (Fin.cons T slots)
      map_add' := by
        intro U V
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base] using nablaAlpha.map_update_add base 0 U V
      map_smul' := by
        intro c U
        let base : Fin (s + 1) → TangentSpace I x := Fin.cons 0 slots
        simpa [base, smul_eq_mul] using nablaAlpha.map_update_smul base 0 c U }
  change L C - L A + L B = -L (A - B - C)
  rw [map_sub, map_sub]
  abel

/-- Section-level expansion frontier for the invariant `(0,s)` Ricci identity.

All pointwise extension choices have already been made here.  The remaining
content is the finite-sum moving-slot calculation: expand both second
covariant derivatives by Definition 14.5, apply the scalar Lie-bracket
commutator, cancel off-diagonal slot updates, and identify the diagonal terms
with connection curvature. -/
private theorem tensor0S_commutator_expansion_from_realizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    let X : TangentSpace I x := Xsec x
    let Y : TangentSpace I x := Ysec x
    let slots : Fin s → TangentSpace I x := fun q => Vsec q x
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (cov.torsion x X Y) slots := by
  classical
  dsimp only
  let Xf : (p : M) → TangentSpace I p := fun p => Xsec p
  let Yf : (p : M) → TangentSpace I p := fun p => Ysec p
  let Vfield : Fin s → (p : M) → TangentSpace I p := fun q p => Vsec q p
  let slots : Fin s → TangentSpace I x := fun q => Vsec q x
  let WY :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Ysec Vsec
  let WX :
      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
    Fin.cons Xsec Vsec
  have hXY :
      nabla2Alpha (Fin.cons (Xsec x) (fun a : Fin (s + 1) => WY a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WY b x) a
                ((cov (fun p : M => WY a p) x) (Xsec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Xsec WY
    simpa using h
  have hYX :
      nabla2Alpha (Fin.cons (Ysec x) (fun a : Fin (s + 1) => WX a x)) =
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) -
          ∑ a : Fin (s + 1),
            nablaAlphaSec x
              (Function.update
                (fun b : Fin (s + 1) => WX b x) a
                ((cov (fun p : M => WX a p) x) (Ysec x))) := by
    have h := Nabla20SRealizesAt.eval_smooth_slots
      (I := I) hnabla2 Ysec WX
    simpa using h
  have hFY (p : M) :
      nablaAlphaSec p
          (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Ysec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Ysec Vsec p
    simpa using h
  have hFX (p : M) :
      nablaAlphaSec p
          (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) =
        extDerivFun (I := I)
            (fun y : M => alphaSec y (fun q : Fin s => Vsec q y))
            p (Xsec p) -
          ∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
    have h := Nabla0SSectionRealizes.eval_smooth_slots
      (I := I) hnabla2.1 Xsec Vsec p
    simpa using h
  let YV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Ysec p)
  let XV : Fin s → (p : M) → TangentSpace I p :=
    fun q p => (cov (fun y : M => Vsec q y) p) (Xsec p)
  have hYV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, YV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [YV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Ysec (Vsec q) x
  have hXV_C1 (q : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, XV q p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    simpa [XV] using
      CovariantDerivative.smoothSections_cov_contMDiffAt_one
        (𝕜 := ℝ) cov hcov Xsec (Vsec q) x
  let VYq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (YV q)
  let VXq : Fin s → Fin s → (p : M) → TangentSpace I p :=
    fun q => Function.update Vfield q (XV q)
  have hVYq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VYq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VYq, Vfield] using hYV_C1 q
    · simpa [VYq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hVXq_C1 (q a : Fin s) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, VXq q a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    by_cases ha : a = q
    · subst a
      simpa [VXq, Vfield] using hXV_C1 q
    · simpa [VXq, Vfield, ha] using
        ((Vsec a).contMDiff.contMDiffAt.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
  have hDX_corrY (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
          x (Xsec x) =
        nablaAlphaSec x
            (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VYq q b x) a
                ((cov (fun p : M => VYq q a p) x) (Xsec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Xsec (VYq q) x (hVYq_C1 q)
    rw [h]
    abel
  have hDY_corrX (q : Fin s) :
      extDerivFun (I := I)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
          x (Ysec x) =
        nablaAlphaSec x
            (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x)) +
          ∑ a : Fin s,
            alphaSec x
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x))) := by
    have h := Nabla0SSectionRealizes.eval_C1_slots
      (I := I) hnabla2.1 Ysec (VXq q) x (hVXq_C1 q)
    rw [h]
    abel
  have hcurvAction :
      curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) =
        -∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
    simpa [Xf, Yf] using
      curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature
        (I := I) (cov := cov) (Rm13 := Rm13)
        alpha Xsec Ysec Vsec hRm13
  have hX_mdiff : MDiffAt (T% Xf) x := by
    simpa [Xf] using
      (Xsec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have hY_mdiff : MDiffAt (T% Yf) x := by
    simpa [Yf] using
      (Ysec.contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have htorsion_apply :
      cov.torsion x (Xsec x) (Ysec x) =
        (cov Yf x) (Xsec x) - (cov Xf x) (Ysec x) -
          VectorField.mlieBracket I Xf Yf x := by
    simpa [Xf, Yf] using
      cov.torsion_apply hX_mdiff hY_mdiff
  have htorsionFirstSlot :
      nablaAlpha
          (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots) =
        -torsionCorrection0SAt (I := I) nablaAlpha
          (cov.torsion x (Xsec x) (Ysec x)) slots := by
    have h := first_slot_torsionCorrection_eq
      (I := I) nablaAlpha ((cov Yf x) (Xsec x))
      ((cov Xf x) (Ysec x)) (VectorField.mlieBracket I Xf Yf x) slots
    simpa [htorsion_apply] using h
  have hExpanded :
      nabla2Alpha
          (metricTraceInput (I := I) (Xsec x) (Ysec x)
            (fun q : Fin s => Vsec q x)) -
        nabla2Alpha
          (metricTraceInput (I := I) (Ysec x) (Xsec x)
            (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := by
    -- This is the remaining expansion/cancellation core:
    -- use `hXY`/`hYX`, `hFY`/`hFX`, `hDX_corrY`/`hDY_corrX`,
    -- `Nabla0SSectionRealizes.eval_point_vector_smooth_slots`, and
    -- `double_update_sum_cancel_diag`.
    rw [metricTraceInput_eq_finCons (I := I) (Xsec x) (Ysec x)
      (fun q : Fin s => Vsec q x)]
    rw [metricTraceInput_eq_finCons (I := I) (Ysec x) (Xsec x)
      (fun q : Fin s => Vsec q x)]
    have hWYx :
        (fun a : Fin (s + 1) => WY a x) =
          Fin.cons (Ysec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WY]
      · intro q
        simp [WY]
    have hWXx :
        (fun a : Fin (s + 1) => WX a x) =
          Fin.cons (Xsec x) (fun q : Fin s => Vsec q x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp [WX]
      · intro q
        simp [WX]
    have hcorrWY :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WY b x) a
              ((cov (fun p : M => WY a p) x) (Xsec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Yf x) (Xsec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Ysec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (XV q x))) := by
      rw [hWYx]
      simpa [WY, Xf, Yf, XV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Ysec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Ysec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Xsec x))
    have hcorrWX :
        (∑ a : Fin (s + 1),
          nablaAlphaSec x
            (Function.update (fun b : Fin (s + 1) => WX b x) a
              ((cov (fun p : M => WX a p) x) (Ysec x)))) =
          nablaAlphaSec x
            (Fin.cons ((cov Xf x) (Ysec x))
              (fun q : Fin s => Vsec q x)) +
            ∑ q : Fin s,
              nablaAlphaSec x
                (Fin.cons (Xsec x)
                  (Function.update (fun r : Fin s => Vsec r x) q
                    (YV q x))) := by
      rw [hWXx]
      simpa [WX, Xf, Yf, YV] using
        sum_update_finCons_raw
          (F := fun slots' : Fin (s + 1) → TangentSpace I x =>
            nablaAlphaSec x slots')
          (head := Xsec x)
          (tail := fun q : Fin s => Vsec q x)
          (d := fun a : Fin (s + 1) =>
            (cov (fun p : M =>
              ((Fin.cons Xsec Vsec :
                Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M → Type _)) a) p) x) (Ysec x))
    let baseScalar : M → Real :=
      fun p : M => alphaSec p (fun q : Fin s => Vsec q p)
    have hbaseSmooth :
        ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞) baseScalar x := by
      simpa [baseScalar] using
        Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec Vsec x
    have hbase2 :
        ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) baseScalar x :=
      hbaseSmooth.of_le
        (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hX2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Xf) x := by
      simpa [Xf] using
        (Xsec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hY2 :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
          (T% Yf) x := by
      simpa [Yf] using
        (Ysec.contMDiff.contMDiffAt.of_le
          (by
            exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    have hYbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p)) x := by
      exact
        (RicciFlower.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Ysec).mdifferentiableAt (by simp)
    have hXbase_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p)) x := by
      exact
        (RicciFlower.extDerivFun_apply_contMDiffAt
          (I := I) hbaseSmooth Xsec).mdifferentiableAt (by simp)
    have hCY_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VYq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VYq q) x (hVYq_C1 q)
    have hCX_mdiff (q : Fin s) :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M => alphaSec p (fun a : Fin s => VXq q a p)) x := by
      exact
        Tensor0SBundle.tensor0SField_eval_C1_slots_mdiffAt
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          alphaSec (VXq q) x (hVXq_C1 q)
    have hCY_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (by intro q hq; exact hCY_mdiff q)
    have hCX_sum_mdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun p : M =>
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) x :=
      by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          mdiffAt_finset_sum (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (by intro q hq; exact hCX_mdiff q)
    have hFY_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
      funext p
      have hWYp :
          (fun a : Fin (s + 1) => WY a p) =
            Fin.cons (Ysec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WY]
        · intro q
          simp [WY]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Ysec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VYq, Vfield, YV]
        · simp [VYq, Vfield, YV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WY a p)
            = nablaAlphaSec p
                (Fin.cons (Ysec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWYp]
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Ysec p))) := by
              simpa [baseScalar] using hFY p
        _ =
            extDerivFun (I := I) baseScalar p (Ysec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p) := by
              rw [hsum]
    have hFX_fun :
        (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)) =
          fun p : M =>
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
      funext p
      have hWXp :
          (fun a : Fin (s + 1) => WX a p) =
            Fin.cons (Xsec p) (fun q : Fin s => Vsec q p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp [WX]
        · intro q
          simp [WX]
      have hsum :
          (∑ q : Fin s,
            alphaSec p
              (Function.update (fun r : Fin s => Vsec r p) q
                ((cov (fun y : M => Vsec q y) p) (Xsec p)))) =
            ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        congr 1
        funext a
        by_cases ha : a = q
        · subst a
          simp [VXq, Vfield, XV]
        · simp [VXq, Vfield, XV, ha]
      calc
        nablaAlphaSec p (fun a : Fin (s + 1) => WX a p)
            = nablaAlphaSec p
                (Fin.cons (Xsec p) (fun q : Fin s => Vsec q p)) := by
              rw [hWXp]
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s,
                alphaSec p
                  (Function.update (fun r : Fin s => Vsec r p) q
                    ((cov (fun y : M => Vsec q y) p) (Xsec p))) := by
              simpa [baseScalar] using hFX p
        _ =
            extDerivFun (I := I) baseScalar p (Xsec p) -
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p) := by
              rw [hsum]
    have hFY_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WY a p))
            x (Xsec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
      rw [hFY_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Xsec x)
        hYbase_mdiff hCY_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p))
              x (Xsec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VYq q a p))
                x (Xsec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VYq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VYq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VYq q a p))
            (x := x) (v := Xsec x)
            (by intro q hq; exact hCY_mdiff q)
      rw [hsum]
    have hFX_deriv :
        extDerivFun (I := I)
            (fun p : M => nablaAlphaSec p (fun a : Fin (s + 1) => WX a p))
            x (Ysec x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) -
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
      rw [hFX_fun]
      rw [extDerivFun_sub_at (I := I) (x := x) (v := Ysec x)
        hXbase_mdiff hCX_sum_mdiff]
      have hsum :
          extDerivFun (I := I)
              (fun p : M =>
                ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p))
              x (Ysec x) =
            ∑ q : Fin s,
              extDerivFun (I := I)
                (fun p : M => alphaSec p (fun a : Fin s => VXq q a p))
                x (Ysec x) := by
        have hfun :
            (fun p : M =>
              ∑ q : Fin s, alphaSec p (fun a : Fin s => VXq q a p)) =
              Finset.univ.sum (fun q : Fin s => fun p : M =>
                alphaSec p (fun a : Fin s => VXq q a p)) := by
          funext p
          simp
        rw [hfun]
        exact
          extDerivFun_finset_sum_at (I := I) Finset.univ
            (fun q : Fin s => fun p : M =>
              alphaSec p (fun a : Fin s => VXq q a p))
            (x := x) (v := Ysec x)
            (by intro q hq; exact hCX_mdiff q)
      rw [hsum]
    haveI : CompleteSpace E := FiniteDimensional.complete Real E
    haveI : IsManifold I 3 M := by
      exact IsManifold.of_le (I := I) (M := M)
        (by exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hbracket :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
              x (Xsec x) -
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      simpa [Xf, Yf] using
        RicciFlower.extDerivFun_apply_mlieBracket
          (I := I) Xf Yf baseScalar x hX2 hY2 hbase2
    have hbracket_eval :
        extDerivFun (I := I) baseScalar x
            (VectorField.mlieBracket I Xf Yf x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      have h0 := Nabla0SSectionRealizes.eval_point_vector_smooth_slots
        (I := I) hnabla2.1
        (VectorField.mlieBracket I Xf Yf x) Vsec
      rw [hnablaAlpha, halpha] at h0
      linarith
    have hbaseComm :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) -
          extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
            x (Ysec x) =
          nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))) := by
      rw [← hbracket]
      exact hbracket_eval
    have hbaseComm_left :
        extDerivFun (I := I)
            (fun p : M => extDerivFun (I := I) baseScalar p (Ysec p))
            x (Xsec x) =
          (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) +
            ∑ q : Fin s,
              alpha
                (Function.update slots q
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x)))) +
            extDerivFun (I := I)
              (fun p : M => extDerivFun (I := I) baseScalar p (Xsec p))
              x (Ysec x) := by
      linarith
    rw [← hWYx, ← hWXx]
    rw [hXY, hYX]
    rw [hcorrWY, hcorrWX]
    rw [hFY_deriv, hFX_deriv]
    rw [hbaseComm_left]
    simp_rw [hDX_corrY, hDY_corrX]
    rw [hnablaAlpha, halpha]
    have hVYq_at (q : Fin s) :
        (fun a : Fin s => VYq q a x) =
          Function.update slots q (YV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VYq, Vfield, slots]
      · simp [VYq, Vfield, slots, ha]
    have hVXq_at (q : Fin s) :
        (fun a : Fin s => VXq q a x) =
          Function.update slots q (XV q x) := by
      funext a
      by_cases ha : a = q
      · subst a
        simp [VXq, Vfield, slots]
      · simp [VXq, Vfield, slots, ha]
    have hFinConsVY (q : Fin s) :
        (Fin.cons (Xsec x) (fun a : Fin s => VYq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Xsec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (YV q x) := by
      rw [hVYq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Xsec x) slots q (YV q x)
    have hFinConsVX (q : Fin s) :
        (Fin.cons (Ysec x) (fun a : Fin s => VXq q a x) :
            Fin (s + 1) → TangentSpace I x) =
          Function.update
            (Fin.cons (Ysec x) slots : Fin (s + 1) → TangentSpace I x)
            q.succ (XV q x) := by
      rw [hVXq_at q]
      exact finCons_update_tail_eq_update_finCons_succ
        (Ysec x) slots q (XV q x)
    have hDoubleY :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (YV q x)) a
              (if a = q then
                (cov (fun p : M => YV q p) x) (Xsec x)
              else
                XV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VYq q a p) x) (Xsec x)) =
            (if a = q then
              (cov (fun p : M => YV q p) x) (Xsec x)
            else
              XV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VYq, Vfield, YV, XV]
        · simp [VYq, Vfield, YV, XV, haq]
      rw [hVYq_at q, hderiv]
    have hDoubleX :
        (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VXq q b x) a
              ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        ∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (Function.update slots q (XV q x)) a
              (if a = q then
                (cov (fun p : M => XV q p) x) (Ysec x)
              else
                YV a x)) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hderiv :
          ((cov (fun p : M => VXq q a p) x) (Ysec x)) =
            (if a = q then
              (cov (fun p : M => XV q p) x) (Ysec x)
            else
              YV a x) := by
        by_cases haq : a = q
        · subst a
          simp [VXq, Vfield, YV, XV]
        · simp [VXq, Vfield, YV, XV, haq]
      rw [hVXq_at q, hderiv]
    have hDoubleCancel :
        - (∑ q : Fin s, ∑ a : Fin s,
          alpha
            (Function.update (fun b : Fin s => VYq q b x) a
              ((cov (fun p : M => VYq q a p) x) (Xsec x)))) +
          (∑ q : Fin s, ∑ a : Fin s,
            alpha
              (Function.update (fun b : Fin s => VXq q b x) a
                ((cov (fun p : M => VXq q a p) x) (Ysec x)))) =
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) := by
      rw [hDoubleY, hDoubleX]
      exact double_update_sum_cancel_diag
        (eval := fun slots' : Fin s → TangentSpace I x => alpha slots')
        (slots := slots)
        (X := fun q : Fin s => XV q x)
        (Y := fun q : Fin s => YV q x)
        (XY := fun q : Fin s => (cov (fun p : M => YV q p) x) (Xsec x))
        (YX := fun q : Fin s => (cov (fun p : M => XV q p) x) (Ysec x))
    have hDiagCurv :
        - (∑ q : Fin s,
          alpha
            (Function.update slots q
              ((cov (fun p : M => YV q p) x) (Xsec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun p : M => XV q p) x) (Ysec x)))) +
          (∑ q : Fin s,
            alpha
              (Function.update slots q
                ((cov (fun y : M => Vsec q y) x)
                  (VectorField.mlieBracket I Xf Yf x)))) =
        -∑ q : Fin s,
          alpha
            (Function.update slots q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)) := by
      let A : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => YV q p) x) (Xsec x)))
      let B : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun p : M => XV q p) x) (Ysec x)))
      let C : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((cov (fun y : M => Vsec q y) x)
            (VectorField.mlieBracket I Xf Yf x)))
      let D : Fin s → Real := fun q =>
        alpha (Function.update slots q
          ((connectionRiemannCurvatureField (I := I) cov Xf Yf
            (fun p : M => Vsec q p)) x))
      change - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
          (∑ q : Fin s, C q) = -∑ q : Fin s, D q
      calc
        - (∑ q : Fin s, A q) + (∑ q : Fin s, B q) +
            (∑ q : Fin s, C q)
            = ∑ q : Fin s, (-A q + B q + C q) := by
              simp [Finset.sum_neg_distrib, Finset.sum_add_distrib]
        _ = ∑ q : Fin s, -D q := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have hdiag :=
                tensor0S_update_curvature_diag
                  (I := I) alpha slots q
                  ((cov (fun p : M => YV q p) x) (Xsec x))
                  ((cov (fun p : M => XV q p) x) (Ysec x))
                  ((cov (fun y : M => Vsec q y) x)
                    (VectorField.mlieBracket I Xf Yf x))
              calc
                -A q + B q + C q =
                    -alpha
                      (Function.update slots q
                        (((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)))) := by
                  simpa [A, B, C] using hdiag
                _ = -D q := by
                  have hvec :
                      ((cov (fun p : M => YV q p) x) (Xsec x)) -
                          ((cov (fun p : M => XV q p) x) (Ysec x)) -
                          ((cov (fun y : M => Vsec q y) x)
                            (VectorField.mlieBracket I Xf Yf x)) =
                        (connectionRiemannCurvatureField (I := I) cov Xf Yf
                          (fun p : M => Vsec q p)) x := by
                    rfl
                  dsimp [D]
                  rw [hvec]
        _ = -∑ q : Fin s, D q := by
              simp [Finset.sum_neg_distrib]
    simp_rw [hFinConsVY, hFinConsVX]
    simp_rw [finCons_update_tail_eq_update_finCons_succ]
    repeat rw [Finset.sum_add_distrib]
    linarith [hDoubleCancel, hDiagCurv]

  calc
    nabla2Alpha
        (metricTraceInput (I := I) (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)) -
      nabla2Alpha
        (metricTraceInput (I := I) (Ysec x) (Xsec x)
          (fun q : Fin s => Vsec q x))
        =
        (-∑ q : Fin s,
          alpha
            (Function.update (fun r : Fin s => Vsec r x) q
              ((connectionRiemannCurvatureField (I := I) cov Xf Yf
                (fun p : M => Vsec q p)) x)))
        +
        (nablaAlpha
            (Fin.cons (VectorField.mlieBracket I Xf Yf x) slots) -
          nablaAlpha
            (Fin.cons ((cov Yf x) (Xsec x)) slots) +
          nablaAlpha
            (Fin.cons ((cov Xf x) (Ysec x)) slots)) := hExpanded
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x)
        +
        (-torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x)) := by
          rw [← hcurvAction]
          simpa [slots] using congrArg
            (fun z =>
              curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
                (fun q : Fin s => Vsec q x) + z)
            htorsionFirstSlot
    _ =
        curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
          (fun q : Fin s => Vsec q x) -
        torsionCorrection0SAt (I := I) nablaAlpha
          ((cov.torsion x) (Xsec x) (Ysec x))
          (fun q : Fin s => Vsec q x) := by
          ring

/-- General invariant Ricci identity for `(0,s)` tensors, with the torsion
correction retained.  This is the single remaining producer frontier for
Theorem 14.12 beyond the checked one-form case. -/
theorem tensor0S_ricciIdentity_with_torsion
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    Tensor0SRicciIdentityWithTorsionAt (I := I) Rm13 alpha nablaAlpha
      nabla2Alpha (fun X Y => cov.torsion x X Y) := by
  classical
  intro X Y slots
  obtain ⟨Xsec, hXx⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYx⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun q =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
        (slots q)).choose
  have hVx (q : Fin s) : Vsec q x = slots q :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x
      (slots q)).choose_spec
  have hslots : (fun q : Fin s => Vsec q x) = slots := by
    funext q
    exact hVx q
  have hmain :=
    tensor0S_commutator_expansion_from_realizes
      (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
      nabla2Alpha Xsec Ysec Vsec hRm13 halpha hnablaAlpha hnabla2
  simpa [Tensor0SRicciIdentityWithTorsionAt, hXx, hYx, hslots] using hmain

theorem tensor0S_ricciIdentity_of_torsionFree
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha)
    (htor : cov.torsion x = 0) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have h := tensor0S_ricciIdentity_with_torsion
    (I := I) cov hcov Rm13 alphaSec nablaAlphaSec alpha nablaAlpha
    nabla2Alpha hRm13 halpha hnablaAlpha hnabla2 X Y slots
  have hzero : cov.torsion x X Y = 0 := by
    simpa using congrArg (fun T => T X Y) htor
  have ht : nablaAlpha (Fin.cons (0 : TangentSpace I x) slots) = 0 := by
    exact nablaAlpha.map_coord_zero (0 : Fin (s + 1)) rfl
  simp [hzero, torsionCorrection0SAt, ht] at h
  simpa using h

/-- General covariant tensor Ricci-identity interface at one point.  The
left-hand tensor is the realized commutator of two covariant derivatives, and
the right-hand tensor is the slotwise curvature action. -/
def RicciIdentity0SAt {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  comm = curvatureAction

theorem ricci_identity_0s {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (h : RicciIdentity0SAt (I := I) comm curvatureAction) :
    comm = curvatureAction :=
  h

end Realized
end RicciFlower
