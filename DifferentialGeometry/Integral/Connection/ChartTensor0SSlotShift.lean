import DifferentialGeometry.Integral.Connection.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Integral.Connection.Tensor0SPartialEval

/-!
# Slot-shift identity between the chart `(s + 1)` slot correction and the
chart `s` slot correction on the partial evaluation

For a smooth Riemannian manifold `(M, g)`, a chart center `α : M`, a base point
`b : M`, a `(0, s + 1)`-tensor section `T`, a tangent vector field `X`, and a
tangent vector `v : TangentSpace I b`, the per-slot Christoffel correction
`chartTensor0SSlotCorrection (s + 1) g α T X b k.succ` evaluated at the tuple
`Fin.cons (chartParallelExtend α b v b) m` equals the per-slot correction
`chartTensor0SSlotCorrection s g α (tensor0SPartialEval T (chartParallelExtend α b v)) X b k`
evaluated at `m`.

In words: shifting the slot index from `k.succ` to `k` while moving the
position-`0` argument into the tensor by partial evaluation (along the
chart-parallel extension of `v`) leaves the underlying scalar value unchanged.

The proof is a purely combinatorial reindexing: unfold both sides to their
underlying multilinear evaluations, use the currying evaluation identity
`TensorMultilinear.tensor0S_curry_apply_eval` on the right-hand side to pull
the partial-evaluation argument back into the tensor as a `Fin.cons` prepend,
then identify the two `Fin.cons` tuples slot-by-slot.

A second version, with literal vector `v` on the left-hand side, follows
unconditionally as soon as `b` lies in the trivialization base set of the
chart-`α` tangent-bundle trivialization, since the chart-parallel extension
collapses back to `v` there.

## Main results

* `chartTensor0SSlotCorrection_succ_eq_partialEval` — the unconditional
  slot-shift identity, with the `Fin.cons` head equal to the value of the
  chart-parallel extension at `b`.
* `chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem` — the
  conditional version with literal `v` on the left-hand side, under the
  hypothesis that `b` lies in the chart-`α` tangent-bundle trivialization
  base set.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Tensor0SBundle
open Tensor0SPartialEval

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Local slot-substitution CLM

We introduce a publicly-named slot-substitution CLM that mirrors the private
slot-CLM used internally by `chartTensor0SSlotCorrection`. The two are
definitionally equal (both are the same `if i = k then Φ else id` formula),
which lets the proof of the main identity manipulate slot indices without
referring to internal private symbols. -/

/-- The slot-`k` substitution CLM family: returns `Φ` at slot index `k`, and
the identity at every other slot index. -/
def localSlotCLM (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin s) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

/-- Slot value at the substituted index. -/
@[simp] lemma localSlotCLM_self (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    localSlotCLM (I := I) s k Φ k = Φ := by
  unfold localSlotCLM
  simp

/-- Slot value at a non-substituted index. -/
lemma localSlotCLM_other (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin s} (h : i ≠ k) :
    localSlotCLM (I := I) s k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold localSlotCLM
  simp [h]

/-- The `chartTensor0SSlotCorrection` value in terms of the public
`localSlotCLM`. By construction, the private `slotCLM` used inside
`chartTensor0SSlotCorrection`'s definition is the same `if i = k then Φ else id`
formula as `localSlotCLM`, so the two are definitionally equal. -/
lemma chartTensor0SSlotCorrection_eq_localSlotCLM_compose (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α T X b k =
      ContinuousMultilinearMap.compContinuousLinearMap
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (localSlotCLM (I := I) s k
          (chartLeviCivitaParallelCLM (I := I) g α b X)) := by
  -- Both sides reduce by the same `if i = k then Φ else id` formula on
  -- the slot index.
  rfl

/-- Pointwise application formula for the slot-`k` Christoffel correction
in terms of `localSlotCLM`. -/
lemma chartTensor0SSlotCorrection_apply_localSlotCLM (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s)
    (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      chartTensor0SSlotCorrection (I := I) s g α T X b k) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (fun i : Fin s =>
          localSlotCLM (I := I) s k
              (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  rw [chartTensor0SSlotCorrection_eq_localSlotCLM_compose
    (I := I) s g α T X b k]
  rfl

/-! ## Pointwise evaluation of the curried partial evaluation -/

/-- Evaluating the partial evaluation `tensor0SPartialEval T Y b` (a
`Tensor0SSpace s I b`) at a `Fin s`-tuple equals evaluating the original
`(0, s + 1)`-tensor `T b` at the `Fin.cons (Y b) _` tuple of length `s + 1`. -/
lemma tensor0SPartialEval_apply_tangent (s : ℕ)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (Y : Π b' : M, TangentSpace I b') (b : M)
    (vs : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      tensor0SPartialEval I M T Y b) vs =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from T b)
        (Fin.cons (Y b) vs) := by
  classical
  -- Rewrite the partial evaluation as `tensor0S_curry s b (T b) (Y b)`.
  change (show ContinuousMultilinearMap ℝ
      (fun _ : Fin s => TangentSpace I b) ℝ from
    tensor0S_curry (I := I) (M := M) s b (T b) (Y b)) vs =
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from T b)
      (Fin.cons (Y b) vs)
  -- `Tensor0SSpace.toModel` carrier is the identity; both sides reduce to
  -- the same evaluation modulo the defeq `TangentSpace I b = E`.
  exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := T b) (v0 := Y b) (vs := vs)

/-! ## Tuple-equality lemma for the slot-shift

Compare the LHS tuple
`fun i : Fin (s + 1) => localSlotCLM (s + 1) k.succ Φ i (Fin.cons w m i)`
with the RHS tuple
`Fin.cons w (fun j : Fin s => localSlotCLM s k Φ j (m j))`.

Both are evaluated on the `Fin (s + 1)`-indexed argument list of `T b`, with
the LHS coming from the chart slot correction at the *shifted* index `k.succ`
and the RHS from the chart slot correction at index `k` composed with the
`Fin.cons` partial-evaluation prepend. The two tuples coincide slot-by-slot:

* At `i = 0`: the LHS slot CLM is the identity (since `0 ≠ k.succ`), so the
  LHS evaluates to `Fin.cons w m 0 = w`, equal to the RHS head.
* At `i = j.succ`: by `Fin.succ_injective`, the LHS condition `j.succ = k.succ`
  is the same as the RHS condition `j = k`, so the LHS slot CLM equals the
  RHS slot CLM. Both are applied to `m j` (via `Fin.cons_succ` for the LHS).
-/

/-- Tuple-equality lemma: the two `Fin (s + 1)`-indexed tuples agree
pointwise. -/
private lemma slot_shift_tuple_eq (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (w : TangentSpace I b) (m : Fin s → TangentSpace I b) :
    (fun i : Fin (s + 1) =>
        localSlotCLM (I := I) (s + 1) k.succ Φ i
          ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) i)) =
      (Fin.cons w (fun j : Fin s =>
        localSlotCLM (I := I) s k Φ j (m j))
        : Fin (s + 1) → TangentSpace I b) := by
  classical
  funext i
  refine Fin.cases ?_ ?_ i
  · -- At `i = 0`. LHS: slot CLM is `id` (since `0 ≠ k.succ`), giving `Fin.cons w m 0 = w`.
    -- RHS: `Fin.cons w _ 0 = w`.
    have h_ne : (0 : Fin (s + 1)) ≠ k.succ := by
      intro h
      exact (Fin.succ_ne_zero k h.symm).elim
    -- Reduce both `Fin.cons` applications at index `0` to `w`.
    have hL_cons : (Fin.cons w m : Fin (s + 1) → TangentSpace I b) 0 = w :=
      Fin.cons_zero (α := fun _ : Fin (s + 1) => TangentSpace I b) w m
    have hR_cons : (Fin.cons w (fun j : Fin s =>
        localSlotCLM (I := I) s k Φ j (m j))
        : Fin (s + 1) → TangentSpace I b) 0 = w :=
      Fin.cons_zero (α := fun _ : Fin (s + 1) => TangentSpace I b) w _
    change localSlotCLM (I := I) (s + 1) k.succ Φ 0
        ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) 0) =
      (Fin.cons w _ : Fin (s + 1) → TangentSpace I b) 0
    rw [hL_cons, hR_cons]
    rw [localSlotCLM_other (I := I) (s + 1) k.succ Φ h_ne]
    rfl
  · intro j
    -- At `i = j.succ`. The LHS condition `j.succ = k.succ` is equivalent to
    -- `j = k` via `Fin.succ_injective`. The RHS uses `j = k` directly.
    have hL_cons : (Fin.cons w m : Fin (s + 1) → TangentSpace I b) j.succ = m j :=
      Fin.cons_succ (α := fun _ : Fin (s + 1) => TangentSpace I b) w m j
    have hR_cons : (Fin.cons w (fun j' : Fin s =>
        localSlotCLM (I := I) s k Φ j' (m j'))
        : Fin (s + 1) → TangentSpace I b) j.succ =
      localSlotCLM (I := I) s k Φ j (m j) :=
      Fin.cons_succ (α := fun _ : Fin (s + 1) => TangentSpace I b) w _ j
    change localSlotCLM (I := I) (s + 1) k.succ Φ j.succ
        ((Fin.cons w m : Fin (s + 1) → TangentSpace I b) j.succ) =
      (Fin.cons w _ : Fin (s + 1) → TangentSpace I b) j.succ
    rw [hL_cons, hR_cons]
    -- LHS slot CLM at index `j.succ` with substitution position `k.succ`
    -- equals the RHS slot CLM at index `j` with substitution position `k`.
    have hCLM_eq :
        localSlotCLM (I := I) (s + 1) k.succ Φ j.succ =
          localSlotCLM (I := I) s k Φ j := by
      unfold localSlotCLM
      by_cases hjk : j = k
      · subst hjk; simp
      · -- `j.succ ≠ k.succ` iff `j ≠ k`.
        have hsucc_ne : (j.succ : Fin (s + 1)) ≠ k.succ := by
          intro h
          exact hjk (Fin.succ_injective _ h)
        simp [hjk, hsucc_ne]
    rw [hCLM_eq]

/-! ## The main identity -/

/-- **Slot-shift identity (unconditional).** For a smooth Riemannian metric
`g`, a chart center `α`, a basepoint `b`, a `(0, s + 1)`-tensor section `T`,
a tangent vector field `X`, and a tangent vector `v ∈ TangentSpace I b`:

The slot-`k.succ` Christoffel correction of `T` evaluated at the tuple
`Fin.cons (chartParallelExtend α b v b) m` equals the slot-`k` Christoffel
correction of the partial evaluation
`tensor0SPartialEval T (chartParallelExtend α b v)` evaluated at `m`.

This is a purely combinatorial reindexing: the position-`0` argument is moved
from the evaluation tuple into the tensor itself via partial evaluation, and
the per-slot Christoffel correction simply re-indexes from `k.succ` to `k`. -/
theorem chartTensor0SSlotCorrection_succ_eq_partialEval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (X : Π b' : M, TangentSpace I b')
    (b : M) (v : TangentSpace I b)
    (k : Fin s) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k.succ)
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        chartTensor0SSlotCorrection (I := I) s g α
          (tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) X b k) m := by
  classical
  -- Abbreviate the slot CLM operator and the parallel-extension head.
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set w : TangentSpace I b := chartParallelExtend (I := I) α b v b with hw_def
  -- Unfold the LHS using the slot-correction evaluation formula (in
  -- `localSlotCLM` form).
  rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (s + 1) g α
    T X b k.succ (Fin.cons w m)]
  -- Unfold the RHS using the slot-correction evaluation formula at slot `k`.
  rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) s g α
    (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) X b k m]
  -- The RHS evaluation has the form `(tensor0SPartialEval T Y b) (...)`.
  -- Pull the partial evaluation back through the curry identity to reveal
  -- the underlying `T b` evaluated at `Fin.cons (Y b) _`.
  rw [tensor0SPartialEval_apply_tangent (s := s) (T := T)
    (Y := chartParallelExtend (I := I) α b v) (b := b)
    (vs := fun j : Fin s =>
      localSlotCLM (I := I) s k Φ j (m j))]
  -- Both sides now evaluate `T b` on a `Fin (s + 1)`-tuple. The tuples are
  -- equal by `slot_shift_tuple_eq`.
  congr 1
  -- The goal is exactly the conclusion of `slot_shift_tuple_eq` (with
  -- `Φ` set as `chartLeviCivitaParallelCLM g α b X`).
  exact slot_shift_tuple_eq (I := I) s k Φ w m

/-! ## Conditional version with literal `v`

When `b` lies in the trivialization base set of the chart-`α` tangent-bundle
trivialization, the chart-parallel extension collapses at `b` to its input
`v`, since `trivFromE α b ∘ trivToE α b = id` there. The slot-shift identity
then specialises to the form with the literal vector `v` appearing as the
`Fin.cons` head on the left-hand side. -/

/-- **Slot-shift identity (literal `v`, conditional).** Under the
trivialization-base-set hypothesis
`b ∈ (trivializationAt E (TangentSpace I) α).baseSet`, the slot-shift identity
holds with literal vector `v` as the `Fin.cons` head on the left-hand side. -/
theorem chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T : Π b' : M, Tensor0SSpace (s + 1) I b')
    (X : Π b' : M, TangentSpace I b')
    {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I b)
    (k : Fin s) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k.succ)
        (Fin.cons v m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        chartTensor0SSlotCorrection (I := I) s g α
          (tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) X b k) m := by
  classical
  -- Reduce to the unconditional form by collapsing
  -- `chartParallelExtend α b v b = v` on the base set.
  have hcollapse : chartParallelExtend (I := I) α b v b = v := by
    unfold chartParallelExtend
    exact trivFromE_trivToE (I := I) α hb v
  rw [show
      (Fin.cons v m : Fin (s + 1) → TangentSpace I b) =
        Fin.cons (chartParallelExtend (I := I) α b v b) m from by
      rw [hcollapse]]
  exact chartTensor0SSlotCorrection_succ_eq_partialEval (I := I)
    g s α T X b v k m

end Connection
end Integral
end DifferentialGeometry

end
