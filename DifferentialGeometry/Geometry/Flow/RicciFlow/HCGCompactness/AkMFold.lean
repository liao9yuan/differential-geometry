import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The field-level upper covariant-derivative tower for `A_k` (Claim 1 m-fold, route i)

`ric_bound` (MSM135 Lemma 3.11) Claim 1 `|∇^m A_k| ≤ C_m(1+|∇^{m+1}g_k|)` differentiates
the relation `∇g_k = A_k ∗ g_k` `m` times (component route, user-resolved). The natural
last-slot contraction `∗` (`contrTail`) has the proven single-step tower Leibniz
`covDerivStepCompU_contrTail_leibniz`: `A_k`'s contracted UPPER slot steps by
`covDerivStepCompU` (`+Γ`), `g_k`'s lower slot by `covDerivStepComp` (`−Γ`).

This file builds the FIELD-level iterated upper tower `iterCovCompU` — the
`covDerivStepCompU` analogue of `iterCovComp` (whose step's `ext` is `frameExtData`
of the whole running field, NOT a single-point function). The `+1` (the contracted
upper slot) is kept LAST in the rank so the recursion ranks `(r+a)+1` stay defeq.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- The field-level iterated **upper** covariant-derivative component tower: `a`
applications of `covDerivStepCompU` to a base array whose LAST slot is the contracted
upper index, with the running field's frame directional derivative as `ext` and fixed
Christoffel data.  The `covDerivStepCompU` analogue of `iterCovComp`; the upper slot is
kept last so ranks `(r+a)+1` stay definitionally equal across the recursion. -/
def iterCovCompU {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    (a : ℕ) → M → (Fin ((r + a) + 1) → Idx) → Real
  | 0 => base
  | (a + 1) => fun x =>
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU frame chr base a y) x)
        (chr x)
        (iterCovCompU frame chr base a x)

@[simp] theorem iterCovCompU_zero {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    iterCovCompU (I := I) frame chr base 0 = base := rfl

@[simp] theorem iterCovCompU_succ {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (a : ℕ) (x : M) :
    iterCovCompU (I := I) frame chr base (a + 1) x =
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU (I := I) frame chr base a y) x)
        (chr x)
        (iterCovCompU (I := I) frame chr base a x) := rfl

/-! ## The frameExtData product rule for the natural contraction (the field-level `hext`) -/

/-- **The frame directional derivative of a natural contraction is the Leibniz sum.**
This is the field-level `hext` that discharges the hypothesis of the tower single-step
`covDerivStepCompU_contrTail_leibniz`: the directional derivative of `contrTail (A ·) (B ·)`
splits by the product rule (`extDerivFun_finset_sum_mul_at`), with the directional
derivatives of the two factors becoming `frameExtData A`/`frameExtData B`.  Requires
component-wise manifold-differentiability of the two fields at `x`. -/
theorem frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (idx : Fin (p + q) → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x idx d =
      ∑ c : Idx,
        (frameExtData (I := I) frame A x
              (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) d *
            B x (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) +
          A x (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
            frameExtData (I := I) frame B x
              (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) d) := by
  classical
  unfold frameExtData
  rw [show (fun y : M => contrTail (A y) (B y) idx) =
      (fun y : M => ∑ c : Idx,
        A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
          B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c)) from by
    funext y; rw [contrTail_apply]]
  rw [extDerivFun_finset_sum_mul_at (I := I) Finset.univ
    (fun c y => A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c y => B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))
    (frame d x)
    (fun c _ => hA (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c _ => hB (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The field-level single-step contraction-Leibniz.**  One covariant-derivative step of
the contraction field `y ↦ contrTail (A y) (B y)` (with `ext = frameExtData` of that field)
splits into the upper step on `A` and the lower step on `B`.  This is
`covDerivStepCompU_contrTail_leibniz` (the tower single-step) with its `hext` discharged by
`frameExtData_contrTail`; it is the inductive engine of the m-fold binomial. -/
theorem covDerivStepComp_frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    covDerivStepComp (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
        (chr x) (contrTail (A x) (B x)) (Fin.cons d (Fin.append aPart bPart)) =
      contrTail (covDerivStepCompU (frameExtData (I := I) frame A x) (chr x) (A x)) (B x)
          (Fin.append (Fin.cons d aPart) bPart) +
        contrTail (A x) (covDerivStepComp (frameExtData (I := I) frame B x) (chr x) (B x))
          (Fin.append aPart (Fin.cons d bPart)) :=
  covDerivStepCompU_contrTail_leibniz
    (frameExtData (I := I) frame A x) (frameExtData (I := I) frame B x)
    (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
    (chr x) (A x) (B x)
    (frameExtData_contrTail (I := I) frame A B x hA hB)
    d aPart bPart

end DifferentialGeometry.PDE.RicciFlow
