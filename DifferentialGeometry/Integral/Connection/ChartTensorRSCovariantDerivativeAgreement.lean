import DifferentialGeometry.Integral.Connection.ChartTensorRSCurryFactor
import DifferentialGeometry.Integral.Connection.ChartTensor0SLeviCivitaParallelExtend
import DifferentialGeometry.Integral.Connection.Tensor0SCovariantDerivativeAgreementHeadline
import DifferentialGeometry.Integral.Connection.TensorRSNabla

/-!
# Agreement of the chart-frame `(r, s)`-tensor covariant derivative with the
abstract bundled one

Given a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model
`I`, a chart-centre `α : M`, a smooth `(r, s)`-tensor section `T`, and a
smooth tangent vector field `X`, this file proves that the chart-frame
`(r, s)`-tensor covariant derivative at a point `b` of the chart-α
Levi-Civita good set agrees with the bundled `(r, s)`-tensor covariant
derivative built from the Levi-Civita connection.

The proof reduces to the agreement of the `(0, r)` and `(0, s)`-tensor
covariant derivatives (Layer B), the curry-factorisation of the
`(r, s)`-intrinsic chart Fréchet derivative through the `(0, s)`-tensor
partial evaluation (D.3.a), and the chart-frame identity for the chart
parallel extension on `(0, r)`-tensor bundles (D.2). The slot-substitution
on the input side cancels against the chart-parallel-extension contribution
of the `(0, r)`-bundle covariant derivative; the slot-substitution on the
output side is identified slot-by-slot with the `(0, s)`-bundle Christoffel
correction of the partial evaluation.

## Main results

* `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet` — the headline agreement,
  for smooth `Cₛ^∞` sections, at a chart-α Levi-Civita good-set point `b`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
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

/-! ## Auxiliary differentiability bridge -/

/-- Manifold-differentiability of the partial evaluation
`tensorPartialEval r s T (chartTensor0SParallelExtend r α b α_input)` at the
basepoint `b`, given pointwise differentiability of `T` and good-set
membership. -/
private lemma tensorSectionMDiffAt_tensorPartialEval
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (α_input : Tensor0SSpace r I b)
    (hT_at :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (T y)) b) :
    TensorSectionMDiffAt (I := I) s
      (tensorPartialEval (I := I) (M := M) r s T
        (chartTensor0SParallelExtend (I := I) r α b α_input)) b := by
  classical
  unfold TensorSectionMDiffAt
  letI _h_top_s : TopologicalSpace
      (TotalSpace (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)) :=
    tensor0SBundle_topology s
  have hW_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
        (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) y
          (chartTensor0SParallelExtend (I := I) r α b α_input y)) b :=
    chartTensor0SParallelExtend_mdifferentiableAt (I := I) r α hb α_input
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => Tensor0SSpace r I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => T y)
    (v := fun y : M => chartTensor0SParallelExtend (I := I) r α b α_input y)
    hT_at hW_at

/-! ## Self-evaluation of the chart-parallel extension at the basepoint -/

/-- On the chart-α trivialisation base set at `b`, the chart-parallel extension
of `α_input` evaluated at `b` itself equals `α_input`. -/
private lemma chartTensor0SParallelExtend_at_self
    (r : ℕ) (α : M) {b : M}
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (α_input : Tensor0SSpace r I b) :
    chartTensor0SParallelExtend (I := I) r α b α_input b = α_input := by
  classical
  have hb_base_tensor : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb_base
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
    ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b α_input) =
    α_input
  exact (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symmL_continuousLinearMapAt
    (R := ℝ) hb_base_tensor α_input

/-! ## Input-slot identity -/

/-- The `(0, r)`-slot-`k` Christoffel correction of the chart-parallel
extension of `α_input` at `b`, viewed as an element of `Tensor0SSpace r I b`,
equals (up to underlying-CMLM evaluation) the value
`tensorSlotSubstCLM r b (tangentSlotCLM r k Φ) α_input`. -/
private lemma chartTensor0SSlotCorrection_chartTensor0SParallelExtend_eq
    (r : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (α_input : Tensor0SSpace r I b) (k : Fin r) :
    chartTensor0SSlotCorrection (I := I) r g α
        (chartTensor0SParallelExtend (I := I) r α b α_input) X b k =
      tensorSlotSubstCLM (I := I) r b
        (fun i : Fin r => if i = k
            then chartLeviCivitaParallelCLM (I := I) g α b X
            else ContinuousLinearMap.id ℝ (TangentSpace I b)) α_input := by
  classical
  -- Both elements are `Tensor0SSpace r I b`. Use `tensor0SSpace_ext` to
  -- reduce to evaluation at every tuple `m`.
  apply tensor0SSpace_ext
  intro m
  -- LHS evaluation via `chartTensor0SSlotCorrection_apply`.
  rw [chartTensor0SSlotCorrection_apply (I := I) r g α
    (chartTensor0SParallelExtend (I := I) r α b α_input) X b k m]
  -- Now LHS = `(parallel_extend ... b) (fun i => slotCLM r k Φ i (m i))`.
  -- Substitute `parallel_extend ... b = α_input`.
  rw [chartTensor0SParallelExtend_at_self (I := I) r α (b := b) hb_base α_input]
  -- RHS via `tensorSlotSubstCLM_apply`.
  rw [tensorSlotSubstCLM_apply (I := I) r b
      (fun i : Fin r => if i = k
          then chartLeviCivitaParallelCLM (I := I) g α b X
          else ContinuousLinearMap.id ℝ (TangentSpace I b))
      α_input m]
  -- Both sides are now
  -- `α_input (fun i => (if i = k then Φ else id) i (m i))`.
  rfl

/-- The composition `T b ∘ (chartTensor0SSlotCorrection r g α w X b k)`,
where `w` is the chart-parallel extension of `α_input`, equals
`chartTensorRSInputSlotCorrection r s g α T X b k` applied to `α_input`. -/
private lemma tensorRSInputSlotCorrection_eq_compose_chartTensor0SSlotCorrection
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (α_input : Tensor0SSpace r I b) (k : Fin r) :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (chartTensor0SSlotCorrection (I := I) r g α
          (chartTensor0SParallelExtend (I := I) r α b α_input) X b k) =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) α_input := by
  classical
  -- Step 1: rewrite the slot correction value to `tensorSlotSubstCLM`.
  rw [chartTensor0SSlotCorrection_chartTensor0SParallelExtend_eq
    (I := I) r g α X (b := b) hb_base α_input k]
  -- Step 2: unfold `chartTensorRSInputSlotCorrection` and apply.
  unfold chartTensorRSInputSlotCorrection
  -- `(T b).comp (tensorSlotSubstCLM ...) α_input = T b (tensorSlotSubstCLM ... α_input)`.
  rfl

/-! ## Output-slot identity -/

/-- On the chart-α trivialisation base set, the `(0, s)`-slot-`l` Christoffel
correction of the partial evaluation, evaluated at a tuple `m`, equals the
value at `m` of the `(r, s)`-output-slot-`l` correction of `T` at `b` applied
to `α_input`. -/
private lemma chartTensor0SSlotCorrection_partialEval_eq_chartTensorRSOutputSlotCorrection
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (α_input : Tensor0SSpace r I b) (l : Fin s)
    (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      chartTensor0SSlotCorrection (I := I) s g α
        (tensorPartialEval (I := I) (M := M) r s T
          (chartTensor0SParallelExtend (I := I) r α b α_input)) X b l) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
          α_input) m := by
  classical
  -- LHS evaluation.
  rw [chartTensor0SSlotCorrection_apply (I := I) s g α
    (tensorPartialEval (I := I) (M := M) r s T
      (chartTensor0SParallelExtend (I := I) r α b α_input)) X b l m]
  -- LHS = `(tensorPartialEval ... b) (fun i => slotCLM s l Φ i (m i))`.
  -- `tensorPartialEval r s T w b = T b (w b)` (definitional).
  -- Substitute `w b = α_input`.
  have hPE_at_b :
      chartTensor0SParallelExtend (I := I) r α b α_input b = α_input :=
    chartTensor0SParallelExtend_at_self (I := I) r α (b := b) hb_base α_input
  change (show ContinuousMultilinearMap ℝ
      (fun _ : Fin s => TangentSpace I b) ℝ from
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
      (chartTensor0SParallelExtend (I := I) r α b α_input b))
    (fun i : Fin s => _) = _
  rw [hPE_at_b]
  -- RHS evaluation via `chartTensorRSOutputSlotCorrection_apply`.
  rw [chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T X b l
    α_input m]
  -- Both sides now have the form
  --   `(T b α_input) (fun i => (if i = l then Φ else id) i (m i))`.
  rfl

/-! ## Headline agreement -/

/-- The chart-frame `(r, s)`-tensor covariant derivative
`chartTensorRSCovariantDerivative r s g α T X` agrees, at any point `b` of the
chart-`α` Levi-Civita good set `chartLeviCivitaGoodSet α`, with the bundled
`(r, s)`-tensor covariant derivative `tensorRSCovariantDerivative` of the
Levi-Civita connection `LeviCivita g`.

Here `g` is a smooth Riemannian metric, `α : M` is the chart centre, `T` is a
smooth `Cₛ^∞` `(r, s)`-tensor section, and `X` is a smooth `Cₛ^∞` tangent
vector field. The good-set membership `hb : b ∈ chartLeviCivitaGoodSet α` is a
genuine validity-domain hypothesis: it places `b` in the chart-`α`
trivialisation base set and the interior of the chart target, where the
chart-frame construction is defined and differentiable. -/
theorem chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensorRSCovariantDerivative (I := I) r s g α T.toFun X.toFun b =
      TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) T.toFun b (X.toFun b) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  -- Pointwise differentiability of `T` and `X` at `b`.
  have hT_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun b' : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun x : M => TensorRSSpace r s I x) b' (T.toFun b')) b :=
    T.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b' (X.toFun b')) b :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- Chart-pullback differentiability of `T` (needed for D.3.a curry-factor).
  have hT_pull :
      DifferentiableAt ℝ
        (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘ (extChartAt I α).symm)
        (extChartAt I α b) := by
    set e := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α with he_def
    have hb_base_rs : b ∈ e.baseSet := by
      change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).baseSet)
      refine ⟨?_, ?_⟩
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
    have hα_repr_diff : MDifferentiableAt I 𝓘(ℝ, TensorRSModel r s ℝ E)
        (fun b' : M => (e ⟨b', T.toFun b'⟩).2) b :=
      (Trivialization.mdifferentiableAt_section_iff (IB := I)
        (e := e) T.toFun hb_base_rs).mp hT_at
    have hα_repr_eq : ∀ {b' : M}, b' ∈ e.baseSet →
        (e ⟨b', T.toFun b'⟩).2 =
          tensorRSChartE_section_repr (I := I) r s α T.toFun b' := by
      intro b' hb'
      unfold tensorRSChartE_section_repr
      have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := b') hb'
      have happ := congrFun hcoe (T.toFun b')
      exact happ.symm
    have hbase_open : IsOpen e.baseSet := e.open_baseSet
    have hbase_nhds : e.baseSet ∈ 𝓝 b := hbase_open.mem_nhds hb_base_rs
    have h_funeq :
        tensorRSChartE_section_repr (I := I) r s α T.toFun =ᶠ[𝓝 b]
        (fun b' : M => (e ⟨b', T.toFun b'⟩).2) := by
      filter_upwards [hbase_nhds] with b' hb' using (hα_repr_eq hb').symm
    have hrepr_α_diff : MDifferentiableAt I 𝓘(ℝ, TensorRSModel r s ℝ E)
        (tensorRSChartE_section_repr (I := I) r s α T.toFun) b :=
      hα_repr_diff.congr_of_eventuallyEq h_funeq
    have hb_src : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
    have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
    have hpb := mdifferentiableAt_iff_source_of_mem_source (I := I)
      (E' := TensorRSModel r s ℝ E) (I' := 𝓘(ℝ, TensorRSModel r s ℝ E)) (x := α)
      (f := tensorRSChartE_section_repr (I := I) r s α T.toFun) hb_src
    have hwithin := hpb.mp hrepr_α_diff
    have htgt_subset : (extChartAt I α).target ⊆ range I :=
      extChartAt_target_subset_range α
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hrange_nhds : range I ∈ 𝓝 (extChartAt I α b) :=
      Filter.mem_of_superset (hint_open.mem_nhds hb_int)
        (interior_subset.trans htgt_subset)
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at hwithin
    exact hwithin.differentiableAt hrange_nhds
  -- Good-set membership lemmas.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  -- Reduce to equality at every `α_input ∈ Tensor0SSpace r I b`.
  apply ContinuousLinearMap.ext
  intro α_input
  -- Use `w := chartTensor0SParallelExtend r α b α_input` for the (0, r) input.
  set w : Π b' : M, Tensor0SSpace r I b' :=
    chartTensor0SParallelExtend (I := I) r α b α_input with hw_def
  -- Differentiability of `w` at `b`.
  have hw_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
        (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) y (w y)) b :=
    chartTensor0SParallelExtend_mdifferentiableAt (I := I) r α hb α_input
  -- `w b = α_input` (on base set).
  have hwb_eq : w b = α_input :=
    chartTensor0SParallelExtend_at_self (I := I) r α (b := b) hb_base α_input
  -- Differentiability of the partial-eval section at `b`.
  have hPartialEval_at : TensorSectionMDiffAt (I := I) s
      (tensorPartialEval (I := I) (M := M) r s T.toFun w) b :=
    tensorSectionMDiffAt_tensorPartialEval (I := I) r s α T.toFun hb α_input
      hT_at
  -- RHS Psi formula via function-level apply.
  have hRHS_psi :=
    TensorRSNabla.tensorRSCovariantDerivative_apply_of_mdifferentiableAt
      (I := I) (M := M) r s (LeviCivita (I := I) g) T.toFun w X.toFun
      (x := b) hT_at hw_at hX_at
  rw [hwb_eq] at hRHS_psi
  rw [hRHS_psi]
  -- Identify the pairing `b' ↦ T b' (w b')` as `tensorPartialEval r s T w b'`.
  have hpartialEval_def :
      (fun y : M =>
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T.toFun y)
          (w y)) =
        tensorPartialEval (I := I) (M := M) r s T.toFun w := by
    funext y; rfl
  rw [hpartialEval_def]
  -- Layer B (0, s) agreement for `partialEval` at `b`.
  have hLayerB_first :
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (tensorPartialEval (I := I) (M := M) r s T.toFun w) b (X.toFun b) =
      chartTensor0SCovariantDerivative (I := I) s g α
        (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b := by
    rcases s with _ | n
    · exact (chartTensor0SCovariantDerivative_eq_abstract_zero (I := I) g α
            (tensorPartialEval (I := I) (M := M) r 0 T.toFun w) X.toFun hb).symm
    · exact (chartTensor0SCovariantDerivative_eq_abstract_succ_aux
            (I := I) (M := M) g α n
            (tensorPartialEval (I := I) (M := M) r (n + 1) T.toFun w)
            X.toFun hb hPartialEval_at hX_at).symm
  rw [hLayerB_first]
  -- Layer B (0, r) agreement for `w` at `b`.
  have hLayerB_second :
      Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g) w b
        (X.toFun b) =
      chartTensor0SCovariantDerivative (I := I) r g α w X.toFun b := by
    rcases r with _ | n
    · exact (chartTensor0SCovariantDerivative_eq_abstract_zero (I := I) g α
            w X.toFun hb).symm
    · have hw_at_n : TensorSectionMDiffAt (I := I) (n + 1) w b := by
        unfold TensorSectionMDiffAt
        exact hw_at
      exact (chartTensor0SCovariantDerivative_eq_abstract_succ_aux
            (I := I) (M := M) g α n w X.toFun hb hw_at_n hX_at).symm
  rw [hLayerB_second]
  -- D.2: chart-frame cov on chart-parallel extension equals `- ∑_k slot_corr`.
  rw [chartTensor0SCovariantDerivative_chartTensor0SParallelExtend
      (I := I) g r α hb α_input X.toFun]
  -- `T b (- ∑_k ...) = - ∑_k T b (slot_corr_k)`.
  have h_T_neg_sum :
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T.toFun b)
        (-(∑ k : Fin r,
          chartTensor0SSlotCorrection (I := I) r g α w X.toFun b k)) =
      - ∑ k : Fin r,
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T.toFun b)
          (chartTensor0SSlotCorrection (I := I) r g α w X.toFun b k) := by
    rw [map_neg]
    rw [map_sum (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      T.toFun b)]
  rw [h_T_neg_sum]
  -- Input-slot identity.
  have h_input_id : ∀ k : Fin r,
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T.toFun b)
        (chartTensor0SSlotCorrection (I := I) r g α w X.toFun b k) =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
        α_input := fun k =>
    tensorRSInputSlotCorrection_eq_compose_chartTensor0SSlotCorrection
      (I := I) r s g α T.toFun X.toFun (b := b) hb_base α_input k
  have h_input_sum :
      (∑ k : Fin r,
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T.toFun b)
          (chartTensor0SSlotCorrection (I := I) r g α w X.toFun b k)) =
      ∑ k : Fin r,
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
          α_input :=
    Finset.sum_congr rfl (fun k _ => h_input_id k)
  rw [h_input_sum]
  -- Now LHS = `chartTensorRSCovariantDerivative ... α_input` (by CLM-ext);
  -- RHS = `chart0S_cov_(0,s)(partialEval) - (- ∑_k input_slot_k α_input)`.
  -- Reduce both sides to a CMLM by evaluating at `m`.
  apply tensor0SSpace_ext
  intro m
  rw [chartTensorRSCovariantDerivative_apply (I := I) r s g α T.toFun X.toFun b
      α_input m]
  -- The RHS subtraction `... - -(∑ k input_slot α_input)` rewrites to addition.
  -- Then evaluate at `m`.
  have hCMLM_subtract :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        chartTensor0SCovariantDerivative (I := I) s g α
          (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b
        - - ∑ k : Fin r,
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
            α_input) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        chartTensor0SCovariantDerivative (I := I) s g α
          (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b) m
      + ∑ k : Fin r,
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
            α_input) m := by
    rw [sub_neg_eq_add]
    rw [show (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) s g α
            (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b
          + ∑ k : Fin r,
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
              α_input) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) s g α
            (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b) m
        + (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from
          ∑ k : Fin r,
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T.toFun X.toFun b k)
              α_input) m from rfl]
    rw [ContinuousMultilinearMap.sum_apply]
  rw [hCMLM_subtract]
  -- Decompose chart-frame (0, s)-cov on partial-eval.
  have h_chart0S_decomp :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        chartTensor0SCovariantDerivative (I := I) s g α
          (tensorPartialEval (I := I) (M := M) r s T.toFun w) X.toFun b) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        tensorRSIntrinsicChartCLM (I := I) r s α T.toFun b (X.toFun b) α_input) m
      - ∑ l : Fin s,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T.toFun X.toFun b l)
              α_input) m := by
    rcases s with _ | n
    · -- s = 0: empty output-slot sum; intrinsic via D.3.a + rank-0 mfderiv bridge.
      simp only [Finset.sum_empty, Finset.univ_eq_empty, sub_zero]
      -- Reduce `m` to the empty tuple.
      have hm_empty : m = fun i : Fin 0 => Fin.elim0 i := by
        funext i; exact i.elim0
      rw [hm_empty]
      rw [chartTensor0SCovariantDerivative_zero_apply (I := I) g α
          (tensorPartialEval (I := I) (M := M) r 0 T.toFun w) X.toFun b
          (fun i : Fin 0 => Fin.elim0 i)]
      have hCurryFactor :=
        tensorRSIntrinsicChartCLM_factor_via_tensorPartialEval
          (I := I) r 0 α T.toFun (b := b) hb α_input hT_pull X.toFun
      have hRank0_bridge :=
        tensor0SIntrinsicChartCLM_zero_apply_empty_eq_mfderiv
          (I := I) α (tensorPartialEval (I := I) (M := M) r 0 T.toFun w)
          hb hPartialEval_at (X.toFun b)
      rw [← hRank0_bridge]
      rw [hCurryFactor]
    · -- s = n + 1: succ apply, then output-slot identity & D.3.a.
      rw [chartTensor0SCovariantDerivative_succ_apply (I := I) n g α
          (tensorPartialEval (I := I) (M := M) r (n + 1) T.toFun w) X.toFun b m]
      have hCurryFactor :=
        tensorRSIntrinsicChartCLM_factor_via_tensorPartialEval
          (I := I) r (n + 1) α T.toFun (b := b) hb α_input hT_pull X.toFun
      have hCurryFactor_at_m :
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
            tensor0SIntrinsicChartCLM (I := I) (n + 1) α
              (tensorPartialEval (I := I) (M := M) r (n + 1) T.toFun w) b
              (X.toFun b)) m =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
            tensorRSIntrinsicChartCLM (I := I) r (n + 1) α T.toFun b (X.toFun b)
              α_input) m := by
        rw [← hCurryFactor]
      rw [hCurryFactor_at_m]
      have h_slot_l_id : ∀ l : Fin (n + 1),
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
            chartTensor0SSlotCorrection (I := I) (n + 1) g α
              (tensorPartialEval (I := I) (M := M) r (n + 1) T.toFun w)
              X.toFun b l) m =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (n + 1) I b from
              chartTensorRSOutputSlotCorrection (I := I) r (n + 1) g α T.toFun
                X.toFun b l) α_input) m := fun l =>
        chartTensor0SSlotCorrection_partialEval_eq_chartTensorRSOutputSlotCorrection
          (I := I) (M := M) r (n + 1) g α T.toFun X.toFun (b := b) hb_base
          α_input l m
      have h_slot_sum :
          (∑ l : Fin (n + 1),
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
                chartTensor0SSlotCorrection (I := I) (n + 1) g α
                  (tensorPartialEval (I := I) (M := M) r (n + 1) T.toFun w)
                  X.toFun b l) m) =
          ∑ l : Fin (n + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (n + 1) => TangentSpace I b) ℝ from
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (n + 1) I b from
                chartTensorRSOutputSlotCorrection (I := I) r (n + 1) g α T.toFun
                  X.toFun b l) α_input) m :=
        Finset.sum_congr rfl (fun l _ => h_slot_l_id l)
      rw [h_slot_sum]
  rw [h_chart0S_decomp]
  -- Final reorganisation: both sides match modulo `abel`.
  abel

end Connection
end Integral
end DifferentialGeometry

end
