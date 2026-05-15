import DifferentialGeometry.Integral.Connection.Tensor0SIntrinsicChartRank0
import DifferentialGeometry.Integral.Connection.ChartTensor0SSlotShift
import DifferentialGeometry.Integral.Connection.Tensor0SIntrinsicChartCurryFactor
import DifferentialGeometry.Integral.Connection.ChartLeviCivitaParallelExtend
import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# Headline agreement of the chart-frame `(0, s + 1)`-tensor covariant derivative
with the abstract bundled one

Given a smooth Riemannian manifold `(M, g)`, a chart center `α : M`, a
`(0, s + 1)`-tensor section `T` and a tangent vector field `X` (both smooth),
this file proves the agreement
`chartTensor0SCovariantDerivative g α (s + 1) T X b
  = tensor0SCovariantDerivative I M (s + 1) (LeviCivita g) T b (X b)`
at every point `b` of the chart-α Levi-Civita good set.

The proof is by induction on `s`. The base case at `s = 0` (rank 1) reduces
to the rank-0 agreement `chartTensor0SCovariantDerivative_eq_abstract_zero`
applied to the partial evaluation of `T` along the chart-parallel extension.
The inductive step `s ↦ s + 1` (rank `s + 2`) uses the same partial-eval
decomposition with the inductive hypothesis at rank `s + 1`.

## Main results

* `chartTensor0SCovariantDerivative_eq_abstract_succ_aux` — the technical
  auxiliary form, with raw functions and pointwise differentiability
  hypotheses. Carries the induction.
* `chartTensor0SCovariantDerivative_eq_abstract_succ` — the headline,
  packaged for smooth `Cₛ^∞` sections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SNabla
open Tensor0SPartialEval

/-! ## Pointwise reductions for the right-hand side

For the inductive step we need to express the bundled
`tensor0SCovariantDerivative I M (s + 1) (LeviCivita g) T b (X b)` evaluated
at a `Fin.cons v m` tuple as the `Psi`-difference of two values evaluated at
`m`. The decomposition uses the curry-iso round trip and the
`homBundleCovariantDerivativeFun_apply` formula. -/

/-- Round-trip of the un-curry inverse applied to a `Fin.cons` tuple equals
the CLM-then-CMLM evaluation. This is a thin packaging of
`tensor0S_curry_apply_eval`. -/
private lemma tensor0S_curry_symm_apply_cons (s : ℕ) {b : M}
    (Φ : TangentSpace I b →L[ℝ] Tensor0SSpace s I b)
    (v : TangentSpace I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      (tensor0S_curry (I := I) (M := M) s b).symm Φ)
        (Fin.cons v m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from Φ v) m := by
  classical
  -- The model-space evaluation identity `tensor0S_curry_apply_eval`, applied
  -- to `(tensor0S_curry s b).symm Φ` and round-tripped through `tensor0S_curry`,
  -- yields the claim.
  set P : Tensor0SSpace (s + 1) I b :=
    (tensor0S_curry (I := I) (M := M) s b).symm Φ
  have hroundtrip :
      tensor0S_curry (I := I) (M := M) s b P = Φ :=
    (tensor0S_curry (I := I) (M := M) s b).apply_symm_apply Φ
  -- Use `tensor0S_curry_apply_eval` (model-space) at `(v, m)`.
  have hev := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := P) (v0 := v) (vs := m)
  -- Rewriting `tensor0S_curry s b P` to `Φ` in `hev` gives the claim.
  -- Both sides are scalars in `ℝ` (the `Tensor0SSpace.toModel` carriers are
  -- the identity), so the rewrite is direct.
  have : (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      tensor0S_curry (I := I) (M := M) s b P v) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from P)
        (Fin.cons v m) := hev.symm
  -- Substitute the round-trip.
  rw [hroundtrip] at this
  exact this.symm

/-! ## Levi-Civita on the chart-parallel extension agrees with the chart
parallel CLM

On the chart-Levi-Civita good set, the bundled Levi-Civita applied to a
chart-parallel-extended vector `chartParallelExtend α b v` at `b` along the
direction `X b` reduces to `chartLeviCivitaParallelCLM g α b X v`, by
applying the chart-overlap identity followed by the symmetric form of the
chart Levi-Civita parallel identity. -/

/-- **`LeviCivita` on a chart-parallel-extended vector.** For `b` in the
chart-α Levi-Civita good set, the bundled Levi-Civita derivative of
`chartParallelExtend α b v` at `b` along `X b` equals
`chartLeviCivitaParallelCLM g α b X v`. -/
private lemma LeviCivita_chartParallelExtend_eq_parallelCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    (LeviCivita (I := I) g).toFun
      (chartParallelExtend (I := I) α b v) b (X b) =
      chartLeviCivitaParallelCLM (I := I) g α b X v := by
  classical
  -- Step 1: chart-overlap formula for `LeviCivita`, which requires
  -- `MDiffAt (T% chartParallelExtend α b v) b`.
  have hY_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b'
          (chartParallelExtend (I := I) α b v b')) b :=
    chartParallelExtend_mdifferentiableAt (I := I) α hb v
  -- Apply the chart-overlap identity.
  rw [LeviCivita_chart_apply (I := I) g α hb hY_at (X b)]
  -- Step 2: identify the chart-Levi-Civita action on the parallel extension
  -- with the closed-form `chartLeviCivitaParallelCLM` value.
  rw [chartLeviCivita_chartParallelExtend_symm (I := I) g α hb v X]
  -- Goal: matches `chartLeviCivitaParallelCLM_apply` definitionally.
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X v]

/-! ## Differentiability of the partial-evaluation pointwise function

To apply the inductive hypothesis to the partial-eval section, we need the
`TensorSectionMDiffAt` predicate for it. This is exactly the `aux` lemma
`TensorSectionMDiffAt_partialEval` from the existing succ file. -/

/-! ## The auxiliary headline statement

We prove the agreement in its raw-function form first, by induction on `s`.
The smooth-section headline follows as a thin corollary. -/

/-- **Auxiliary induction theorem.** For a `(0, s + 1)`-tensor section `T`
with pointwise-differentiable total-space form at `b`, and a tangent vector
field `X` with pointwise-differentiable total-space form at `b`, the
chart-frame and bundled covariant derivatives at the chart-α Levi-Civita
good-set point `b` agree. -/
theorem chartTensor0SCovariantDerivative_eq_abstract_succ_aux
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (T : Π b' : M, Tensor0SSpace (s + 1) I b')
      (X : Π b' : M, TangentSpace I b')
      {b : M} (_hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
      (_hT_at : TensorSectionMDiffAt (I := I) (s + 1) T b)
      (_hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b' (X b')) b),
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b =
        Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g) T b (X b) := by
  intro s
  induction s with
  | zero =>
    -- Base case: `s = 0`, rank 1.
    intro T X b hb hT_at hX_at
    -- We prove the equality of `(0, 1)`-tensor fibre values by CMLM
    -- extensionality. Every `m : Fin 1 → TangentSpace I b` decomposes as
    -- `Fin.cons (m 0) Fin.tail` with `Fin.tail m = Fin.elim0` up to
    -- subsingleton.
    apply ContinuousMultilinearMap.ext
    intro m
    set v : TangentSpace I b := m 0 with hv_def
    -- Use `Fin.cons_self_tail` to rewrite `m` as `Fin.cons v (Fin.tail m)`.
    have hm_decomp : m = Fin.cons v (Fin.tail m) := by
      rw [hv_def]; exact (Fin.cons_self_tail m).symm
    have htail : (Fin.tail m : Fin 0 → TangentSpace I b) =
        (fun i : Fin 0 => Fin.elim0 i) := by
      funext i; exact i.elim0
    -- Set `m₀ : Fin 0 → TangentSpace I b` to the unique empty tuple.
    set m₀ : Fin 0 → TangentSpace I b := fun i => Fin.elim0 i with hm0_def
    have hm_eq : m = Fin.cons v m₀ := by
      rw [hm_decomp, htail]
    -- LHS evaluation via `chartTensor0SCovariantDerivative_succ_apply`.
    rw [hm_eq]
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) 0 g α T X b
        (Fin.cons v m₀)]
    -- RHS: unfold the bundled cov via `tensor0SCovariantDerivative_succ_eq`
    -- then `tensor0SCovariantDerivative_succ_apply`.
    rw [tensor0SCovariantDerivative_succ_eq I M (s := 0)
        (cov := LeviCivita (I := I) g)]
    rw [tensor0SCovariantDerivative_succ_apply I M
        (s := 0)
        (cov_TM := LeviCivita (I := I) g)
        (cov_s := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        T b (X b)]
    -- Evaluate the un-curry inverse at `Fin.cons v m₀`.
    rw [tensor0S_curry_symm_apply_cons (I := I) (M := M) 0
        (Φ := HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel 0 ℝ E)
          (fun x : M => Tensor0SSpace 0 I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
          (curriedSection I M T) b (X b))
        v m₀]
    -- Apply the Psi formula via `homBundleCovariantDerivativeFun_apply`,
    -- with `Y := chartParallelExtend α b v` (Y b = v on the base set) and
    -- `V_field := X` (the differentiation direction).
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
    have hYb_eq : chartParallelExtend (I := I) α b v b = v := by
      unfold chartParallelExtend
      exact trivFromE_trivToE (I := I) α hb_base v
    -- `MDiff` hypotheses for `homBundleCovariantDerivativeFun_apply`.
    have hτ_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 0 ℝ E))
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 0 ℝ E)
            (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace 0 I x)
            y (curriedSection I M T y)) b :=
      mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 0 T hT_at
    have hY_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y : M => TotalSpace.mk' E
            (E := fun x : M => TangentSpace I x) y
            (chartParallelExtend (I := I) α b v y)) b :=
      chartParallelExtend_mdifferentiableAt (I := I) α hb v
    -- Apply the Psi formula at `(X b, v)`, using `Y b = v`.
    have hPsi := HomConnection.homBundleCovariantDerivativeFun_apply
      (I := I) (M := M) (F := Tensor0SModel 0 ℝ E)
      (V := fun x : M => Tensor0SSpace 0 I x)
      (cov_TM := LeviCivita (I := I) g)
      (cov_V := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (τ := curriedSection I M T)
      (x := b) hτ_at
      (V_field := X) (Y := chartParallelExtend (I := I) α b v)
      hX_at hY_at
    -- `hPsi : homBundleCovariantDerivativeFun ... (X b) (chartParallelExtend α b v b) = Psi ...`.
    -- Convert `chartParallelExtend α b v b` to `v` using `hYb_eq`.
    rw [hYb_eq] at hPsi
    -- Rewrite the private `Psi` (the RHS of `hPsi`) to its explicit
    -- subtraction form. The reduction is definitional.
    have hPsi_explicit :
        (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel 0 ℝ E)
            (fun x : M => Tensor0SSpace 0 I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (curriedSection I M T) b (X b)) v =
        ((tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun y : M => (curriedSection I M T) y
              (chartParallelExtend (I := I) α b v y)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
              (X b)) :
          Tensor0SSpace 0 I b) := hPsi
    rw [hPsi_explicit]
    -- The pairing `τ y (Y y)` equals `tensor0SPartialEval T Y y`.
    have hpair_eq :
        (fun y : M => (curriedSection I M T) y
            (chartParallelExtend (I := I) α b v y)) =
          tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v) := by
      funext y
      rfl
    rw [hpair_eq]
    -- Distribute the CMLM evaluation across subtraction on the RHS.
    rw [show ((show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b)))) m₀ =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b)) m₀ -
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b))) m₀ from
      ContinuousMultilinearMap.sub_apply _ _ _]
    -- LHS: rewrite the chart-frame slot-correction sum at slot 0.
    have hslot_sum :
        (∑ k : Fin (0 + 1),
            chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b k) =
          chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b 0 := by
      simp
    rw [show ∑ k : Fin (0 + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b k)
              (Fin.cons v m₀) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from
          chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b 0)
            (Fin.cons v m₀) from by simp]
    -- Slot-0 evaluation in terms of the public `localSlotCLM`.
    rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (0 + 1) g α
        T X b 0 (Fin.cons v m₀)]
    -- Reduce `localSlotCLM ... 0 Φ i (Fin.cons v m₀ i)` to `Fin.cons (Φ v) m₀ i`.
    have hSlot0_tuple :
        (fun i : Fin (0 + 1) =>
            localSlotCLM (I := I) (0 + 1) (0 : Fin (0 + 1))
              (chartLeviCivitaParallelCLM (I := I) g α b X) i
              ((Fin.cons v m₀ : Fin (0 + 1) → TangentSpace I b) i)) =
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀
            : Fin (0 + 1) → TangentSpace I b) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.cons_zero, localSlotCLM]
      · intro k; exact k.elim0
    -- LHS now has the form `intrinsic_at_cons(v, m₀) - T b (Fin.cons (Φ v) m₀)`.
    -- RHS Psi splits into two CMLM-evaluated pieces. We identify the second
    -- piece with `T b (Fin.cons (Φ v) m₀)` via the chart-Levi-Civita parallel
    -- identity and the curry-eval rewrite, and the first piece with the
    -- intrinsic CLM via the rank-0 agreement and the rank-0 mfderiv bridge.
    have h_cov_TM_eq : (LeviCivita (I := I) g).toFun
        (chartParallelExtend (I := I) α b v) b (X b) =
        chartLeviCivitaParallelCLM (I := I) g α b X v :=
      LeviCivita_chartParallelExtend_eq_parallelCLM (I := I) g α hb v X
    have h_curry_eval_slot0 :
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀) =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b) ℝ from
            curriedSection I M T b
              (chartLeviCivitaParallelCLM (I := I) g α b X v))
            m₀ := by
      change (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          tensor0S_curry (I := I) (M := M) 0 b (T b)
            (chartLeviCivitaParallelCLM (I := I) g α b X v)) m₀
      exact (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := T b)
        (v0 := chartLeviCivitaParallelCLM (I := I) g α b X v) (vs := m₀)).symm
    -- LHS: intrinsic - slot_0. Rewrite the slot-0 piece via `hSlot0_tuple`
    -- and `h_curry_eval_slot0`; identify the cov_TM piece via `h_cov_TM_eq`.
    rw [hSlot0_tuple]
    rw [h_curry_eval_slot0]
    rw [show (LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
            (X b) = chartLeviCivitaParallelCLM (I := I) g α b X v from
      h_cov_TM_eq]
    -- Apply rank-0 agreement on the partial-eval section.
    have hRank0 :=
      chartTensor0SCovariantDerivative_eq_abstract_zero (I := I) g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X hb
    rw [← hRank0]
    rw [chartTensor0SCovariantDerivative_zero_apply (I := I) g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X b m₀]
    -- Bridge the rank-0 mfderiv to the rank-0 intrinsic CLM, then chain via
    -- the curry-factor identity to recover the rank-1 intrinsic at `Fin.cons v m₀`.
    have hPartialEval_at :
        TensorSectionMDiffAt (I := I) 0
          (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) b :=
      TensorSectionMDiffAt_partialEval (I := I) 0 α T hb hT_at v
    have hRank0_bridge := tensor0SIntrinsicChartCLM_zero_apply_empty_eq_mfderiv
      (I := I) α (tensor0SPartialEval I M T
        (chartParallelExtend (I := I) α b v)) hb hPartialEval_at (X b)
    rw [← hRank0_bridge]
    have hT_pull :
        DifferentiableAt ℝ
          (tensor0SChartE_section_repr (I := I) (0 + 1) α T ∘
            (extChartAt I α).symm) (extChartAt I α b) :=
      differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
        (I := I) (0 + 1) α T hb hT_at
    have hCurryFactor :=
      tensor0SIntrinsicChartCLM_factor_via_partialEval
        (I := I) 0 α T hb v hT_pull X m₀
    have hCons_eq :
        (Fin.cons (chartParallelExtend (I := I) α b v b) m₀
          : Fin (0 + 1) → TangentSpace I b) =
          Fin.cons v m₀ := by
      rw [hYb_eq]
    rw [hCons_eq] at hCurryFactor
    rw [hCurryFactor]
  | succ s ih =>
    -- Inductive step: `s ↦ s + 1`. Rank `(s + 1) + 1 = s + 2`.
    intro T X b hb hT_at hX_at
    -- Same CMLM-extensionality scheme.
    apply ContinuousMultilinearMap.ext
    intro m
    set v : TangentSpace I b := m 0 with hv_def
    have hm_decomp : m = Fin.cons v (Fin.tail m) := by
      rw [hv_def]; exact (Fin.cons_self_tail m).symm
    set mt : Fin (s + 1) → TangentSpace I b := Fin.tail m with hmt_def
    have hm_eq : m = Fin.cons v mt := hm_decomp
    rw [hm_eq]
    -- LHS via `chartTensor0SCovariantDerivative_succ_apply`.
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) (s + 1) g α T X b
        (Fin.cons v mt)]
    -- RHS via `tensor0SCovariantDerivative_succ_eq` then `_succ_apply`.
    rw [tensor0SCovariantDerivative_succ_eq I M (s := s + 1)
        (cov := LeviCivita (I := I) g)]
    rw [tensor0SCovariantDerivative_succ_apply I M
        (s := s + 1)
        (cov_TM := LeviCivita (I := I) g)
        (cov_s := tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g))
        T b (X b)]
    -- Round-trip through the un-curry inverse at `Fin.cons v mt`.
    rw [tensor0S_curry_symm_apply_cons (I := I) (M := M) (s + 1)
        (Φ := HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (curriedSection I M T) b (X b))
        v mt]
    -- Apply Psi via `homBundleCovariantDerivativeFun_apply` with
    -- `Y := chartParallelExtend α b v`, `V_field := X`.
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
    have hYb_eq : chartParallelExtend (I := I) α b v b = v := by
      unfold chartParallelExtend
      exact trivFromE_trivToE (I := I) α hb_base v
    have hτ_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s + 1) ℝ E))
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
            (E := fun x : M =>
              TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            y (curriedSection I M T y)) b :=
      mdifferentiableAt_curriedSection_of_section (I := I) (M := M) (s + 1)
        T hT_at
    have hY_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y : M => TotalSpace.mk' E
            (E := fun x : M => TangentSpace I x) y
            (chartParallelExtend (I := I) α b v y)) b :=
      chartParallelExtend_mdifferentiableAt (I := I) α hb v
    have hPsi := HomConnection.homBundleCovariantDerivativeFun_apply
      (I := I) (M := M) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun x : M => Tensor0SSpace (s + 1) I x)
      (cov_TM := LeviCivita (I := I) g)
      (cov_V := tensor0SCovariantDerivative I M (s + 1)
        (LeviCivita (I := I) g))
      (τ := curriedSection I M T)
      (x := b) hτ_at
      (V_field := X) (Y := chartParallelExtend (I := I) α b v)
      hX_at hY_at
    rw [hYb_eq] at hPsi
    -- Rewrite the private `Psi` (the RHS of `hPsi`) to its explicit
    -- subtraction form. The reduction is definitional.
    have hPsi_explicit :
        (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel (s + 1) ℝ E)
            (fun x : M => Tensor0SSpace (s + 1) I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (curriedSection I M T) b (X b)) v =
        ((tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun y : M => (curriedSection I M T) y
              (chartParallelExtend (I := I) α b v y)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
              (X b)) :
          Tensor0SSpace (s + 1) I b) := hPsi
    rw [hPsi_explicit]
    -- Pairing: `b' ↦ τ b' (Y b') = partialEval T Y b'`.
    have hpair_eq :
        (fun y : M => (curriedSection I M T) y
            (chartParallelExtend (I := I) α b v y)) =
          tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v) := by
      funext y
      rfl
    rw [hpair_eq]
    -- Distribute the CMLM evaluation across subtraction on the RHS.
    rw [show ((show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b)))) mt =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b)) mt -
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b))) mt from
      ContinuousMultilinearMap.sub_apply _ _ _]
    -- LHS slot-sum: distribute the CMLM evaluation across the finite sum.
    -- We split slot-0 from slots k+1 manually.
    -- Use `Fin.sum_univ_succ` on `∑ k : Fin (s + 2), …`.
    rw [show ∑ k : Fin (s + 1 + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b k)
              (Fin.cons v mt) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
          chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b 0)
            (Fin.cons v mt) +
          ∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b
                k.succ) (Fin.cons v mt) from
      Fin.sum_univ_succ _]
    -- Slot 0 evaluation in terms of the public `localSlotCLM`.
    rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (s + 1 + 1) g α
        T X b 0 (Fin.cons v mt)]
    -- Reduce the slot-0 substitution tuple to `Fin.cons (Φ v) mt`.
    have hSlot0_tuple :
        (fun i : Fin (s + 1 + 1) =>
            localSlotCLM (I := I) (s + 1 + 1) (0 : Fin (s + 1 + 1))
              (chartLeviCivitaParallelCLM (I := I) g α b X) i
              ((Fin.cons v mt : Fin (s + 1 + 1) → TangentSpace I b) i)) =
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt
            : Fin (s + 1 + 1) → TangentSpace I b) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.cons_zero, localSlotCLM]
      · intro k
        have hne : (k.succ : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero k
        simp [hne, localSlotCLM]
    rw [hSlot0_tuple]
    -- Slots `k.succ` reduce to slot-`k` corrections of the partial-eval at `mt`,
    -- via `chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem`.
    have hSlotSucc_sum :
        (∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b
                k.succ) (Fin.cons v mt)) =
          ∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1) g α
                (tensor0SPartialEval I M T
                  (chartParallelExtend (I := I) α b v)) X b k) mt := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem (I := I)
        g (s := s + 1) α T X (b := b) hb_base v k mt
    rw [hSlotSucc_sum]
    -- Now apply IH to the partial-eval section (rank s + 1).
    have hPartialEval_at :
        TensorSectionMDiffAt (I := I) (s + 1)
          (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) b :=
      TensorSectionMDiffAt_partialEval (I := I) (s + 1) α T hb hT_at v
    -- IH: chartTensor0SCovariantDerivative (s+1) (partialEval) X b =
    --     tensor0SCovariantDerivative I M (s+1) (LeviCivita g) (partialEval) b X b.
    have hIH := ih (tensor0SPartialEval I M T
        (chartParallelExtend (I := I) α b v))
      X hb hPartialEval_at hX_at
    -- Apply IH on the cov-side (RHS first piece): rewrite
    -- `tensor0SCovariantDerivative I M (s+1) (LeviCivita g) (partialEval) b X b`
    -- to `chartTensor0SCovariantDerivative (s+1) g α (partialEval) X b`.
    rw [← hIH]
    -- The chart-frame cov on partial-eval (rank s + 1), evaluated at `mt`,
    -- is `intrinsic_partialEval at mt - ∑ k, slot_k_partialEval at mt` (a
    -- CMLM evaluation that splits).
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) s g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X b mt]
    -- The cov_TM piece on RHS: `(LeviCivita g) Y b (X b) = Φ v` on the good set.
    have h_cov_TM_eq :
        (LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b (X b) =
          chartLeviCivitaParallelCLM (I := I) g α b X v :=
      LeviCivita_chartParallelExtend_eq_parallelCLM (I := I) g α hb v X
    -- Apply the curry-factor identity for the intrinsic piece.
    have hT_pull :
        DifferentiableAt ℝ
          (tensor0SChartE_section_repr (I := I) (s + 1 + 1) α T ∘
            (extChartAt I α).symm) (extChartAt I α b) :=
      differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
        (I := I) (s + 1 + 1) α T hb hT_at
    have hCurryFactor :=
      tensor0SIntrinsicChartCLM_factor_via_partialEval
        (I := I) (s + 1) α T hb v hT_pull X mt
    -- Reduce `Fin.cons (chartParallelExtend ... b) mt` to `Fin.cons v mt`.
    have hCons_eq :
        (Fin.cons (chartParallelExtend (I := I) α b v b) mt
          : Fin (s + 1 + 1) → TangentSpace I b) =
          Fin.cons v mt := by
      rw [hYb_eq]
    rw [hCons_eq] at hCurryFactor
    -- The slot-0 term `T b (Fin.cons (Φ v) mt)` must match the second Psi
    -- piece, written as `(curriedSection T b (cov_TM Y b X)) mt`.
    have h_curry_eval_slot0 :
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt) =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
            curriedSection I M T b
              (chartLeviCivitaParallelCLM (I := I) g α b X v))
            mt := by
      change (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          tensor0S_curry (I := I) (M := M) (s + 1) b (T b)
            (chartLeviCivitaParallelCLM (I := I) g α b X v)) mt
      exact (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := T b)
        (v0 := chartLeviCivitaParallelCLM (I := I) g α b X v) (vs := mt)).symm
    rw [h_curry_eval_slot0]
    rw [h_cov_TM_eq]
    rw [hCurryFactor]
    -- The two arithmetic expressions coincide by `abel`.
    abel

/-! ## Headline theorem (smooth-section form)

The smooth-section form is the direct corollary, extracting pointwise
differentiability from the `Cₛ^∞` smoothness data. -/

/-- **Headline agreement.** For a smooth Riemannian manifold `(M, g)`, a
chart center `α : M`, a smooth `(0, s + 1)`-tensor section `T`, a smooth
tangent vector field `X`, and any point `b` on the chart-α Levi-Civita good
set, the chart-frame and bundled covariant derivatives at `b` agree. -/
theorem chartTensor0SCovariantDerivative_eq_abstract_succ
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)) :=
        tensor0SBundle_topology (s + 1)
      letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x) :=
        tensor0SBundle_fiber (s + 1)
      Cₛ^∞⟮I; Tensor0SModel (s + 1) ℝ E,
        fun b => Tensor0SSpace (s + 1) I b⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α T.toFun X.toFun b =
      Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g) T.toFun b (X.toFun b) := by
  classical
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x) :=
    tensor0SBundle_fiber (s + 1)
  -- Extract pointwise differentiability from the `Cₛ^∞` smoothness data.
  have hT_at : TensorSectionMDiffAt (I := I) (s + 1) T.toFun b := by
    unfold TensorSectionMDiffAt
    exact T.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b' (X.toFun b')) b :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact chartTensor0SCovariantDerivative_eq_abstract_succ_aux
    (I := I) (M := M) g α s T.toFun X.toFun hb hT_at hX_at

end Connection
end Integral
end DifferentialGeometry

end
