import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionChartSourceContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorRSModelEvalBasis
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProjBridge
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative

/-!
# Chart-source smoothness of the trivialised slot-substitution CLM

For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, and a slot index
`k : Fin r`, this file ships chart-source smoothness of the trivialised
image of

```
b ↦ tensorSlotSubstCLM r b
      (tangentSlotCLM r k
        (chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)))
```

viewed as a section of the hom-bundle of `Tensor0SSpace r → Tensor0SSpace r`
on `M`.

## Headline

`tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource`
— the trivialised image is `C^∞`-smooth on `(chartAt H α).source` as a
`TensorRSModel r r ℝ E`-valued function.

The proof composes two ingredients:

* The **bridge identity**
  `triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel` from
  `TrivProjBridge.lean`, which rewrites the trivialised image on chart
  source as the inverse chart-`(α, b)`-twist of the model-fibre value.
* The **chart-source smoothness of the trivialised parallel CLM** at the
  chart-basis vector field, supplied by B.1
  (`chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource`).

We reduce the CLM-valued smoothness to per-`(Idx, Jdx)` scalar smoothness
via `contMDiffOn_into_tensorRSModel_of_eval_basis`, then identify each
scalar entry with a Kronecker product of indicators times a matrix entry
of the trivialised parallel CLM (which is smooth by B.1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [CompactSpace M]

/-- A finite-dimensional inner-product space is complete. We package this as
a local instance so the chart-Levi-Civita parallel CLM infrastructure
(which requires `[CompleteSpace E]`) is usable here. -/
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Auxiliary smoothness of the trivialised parallel-CLM at a basis vector

For a chart-basis input `chartBasisVecFiber α j`, B.1 gives chart-source
smoothness of `b ↦ inCoordinates (...) (Φ_b) : E →L[ℝ] E`. Specialising to
the scalar matrix entry against the model basis yields a smooth scalar. -/

/-- For a chart-basis input `chartBasisVecFiber α j`, the matrix entry
`(chartModelBasis E).repr (Φ_b_triv (chartModelBasis E j_in)) i_out` is
chart-source `C^∞`-smooth in `b`. Here `Φ_b = chartLeviCivitaParallelCLM
g α b (chartBasisVecFiber α j)` and `Φ_b_triv := chartJ α b ∘ Φ_b ∘
chartJinv α b` is its `E →L[ℝ] E` trivialisation. -/
private lemma chartLeviCivitaParallelCLM_chartBasisVec_matrixEntry_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (i_out j_in : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          ((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2
              ((chartModelBasis E) j_in))) i_out)
      ((chartAt H α).source) := by
  classical
  -- Start from B.1's chart-source smooth trivialised image as `E →L E`.
  have hΦ_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M =>
          (trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2)
        ((chartAt H α).source) :=
    chartLeviCivitaParallelCLM_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g α j
  -- Apply CLM at the model basis vector (j_in).
  have hbasis_smooth : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun (_ : M) => (chartModelBasis E) j_in)
      ((chartAt H α).source) := contMDiffOn_const
  have hΦv_smooth : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M =>
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j)⟩).2)
            ((chartModelBasis E) j_in))
      ((chartAt H α).source) :=
    hΦ_smooth.clm_apply hbasis_smooth
  -- The model-basis repr at i_out is a continuous linear functional, hence
  -- smooth in its argument.
  have hcoord_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun v : E => ((chartModelBasis E).repr v) i_out) := by
    have h1 : Continuous fun v : E => ((chartModelBasis E).repr v) i_out :=
      ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) i_out).comp
        (chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
    -- Build it as a CLM and use that all CLMs are `ContMDiff ∞`.
    let L : E →L[ℝ] ℝ :=
      ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) i_out).comp
        (chartModelBasis E).repr.toLinearMap).toContinuousLinearMap
    exact L.contMDiff
  have hfinal : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        ((chartModelBasis E).repr
          ((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α j)⟩).2
              ((chartModelBasis E) j_in))) i_out)
      ((chartAt H α).source) :=
    hcoord_smooth.comp_contMDiffOn hΦv_smooth
  exact hfinal

/-! ## Inner round-trip on chart source

For `b` in the chart source (= tangent trivialisation base set at `α`), the
roundtrip `chartJ α b (chartJinv α b v) = v` and likewise the other way. -/

private lemma chartJ_chartJinv_on_chartSource
    (α : M) {b : M} (hb : b ∈ (chartAt H α).source) (v : E) :
    chartJ (I := I) (M := M) α b
        (chartJinv (I := I) (M := M) α b v) = v := by
  classical
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  exact chartJ_chartJinv (I := I) (M := M) α hbase v

private lemma chartJinv_chartJ_self_on_chartSource
    (α : M) {b : M} (hb : b ∈ (chartAt H α).source) (v : E) :
    chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b v) = v := by
  classical
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  exact chartJinv_chartJ_self (I := I) (M := M) α hbase v

/-! ## Expansion of `(eval0SCLE r).symm (Pi.single Idx 1)` on a basis tuple

The key characterising property: `((eval0SCLE r).symm (Pi.single Idx 1))`
evaluated at `chartModelBasis E ∘ φ` is the indicator `[φ = Idx]`. -/

private lemma eval0SCLE_symm_pi_single_at_basis_tuple
    (r : ℕ) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (φ : Fin r → Fin (Module.finrank ℝ E)) :
    ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ)))
        (fun k : Fin r => (chartModelBasis E) (φ k)) =
      Pi.single (M := fun _ => ℝ) Idx (1 : ℝ) φ := by
  classical
  -- `eval0SCLE.symm` applied then `eval0SCLE`-evaluated at φ gives the original.
  have h := (eval0SCLE (E := E) r).apply_symm_apply
    (Pi.single Idx (1 : ℝ))
  have h' := congr_fun h φ
  -- `eval0SCLE r Ψ φ = Ψ (chartModelBasis ∘ φ)`.
  simpa [eval0SCLE_apply] using h'

/-! ## Closed-form expansion of the trivialised slot-substitution CLM

The trivialised image of `tensorSlotSubstCLM r b (tangentSlotCLM r k Φ_b)`
on chart source has matrix-entry expression at `(Idx, Jdx)`:

* `M_{Idx k, Jdx k}` if `Idx i = Jdx i` for all `i ≠ k`,
* `0` otherwise.

Here `M` is the matrix of `Φ_b_triv := chartJ ∘ Φ_b ∘ chartJinv` in the
model basis. This follows from the bridge identity
`triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel`, multilinearity of
the basis "delta multilinear form" `((eval0SCLE r).symm (Pi.single Idx 1))`,
and the round-trip identity `chartJ ∘ chartJinv = id` on chart source. -/

/-- Closed-form expansion of `((triv_RR α) ⟨b, T_b⟩).2 ((eval0SCLE r).symm (Pi.single Idx 1)) (chartModelBasis ∘ Jdx)`
for `T_b = tensorSlotSubstCLM r b (tangentSlotCLM r k Φ_b)` and `Φ_b =
chartLeviCivitaParallelCLM g α b X`.

The expansion: 0 if some non-`k` index disagrees, otherwise the model-basis
matrix entry of the trivialised parallel CLM. -/
private lemma slotSubst_trivProj_entry_closedForm
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M) (k : Fin r)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLE_TensorRSModel (E := E) r r
      ((trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b
        ((tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b X))) : TensorRSSpace r r I b))
      (Idx, Jdx) =
      (if ∀ i : Fin r, i ≠ k → Idx i = Jdx i then
        (((chartModelBasis E).repr
          (((trivializationAt (E →L[ℝ] E)
            (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
            ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
            ((chartModelBasis E) (Jdx k)))) (Idx k))
      else 0) := by
  classical
  -- Step 1: apply the bridge identity.
  have hbridge := triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r r α (b := b) hb
    (T := ((tensorSlotSubstCLM (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X))) : TensorRSSpace r r I b))
  rw [hbridge]
  -- Step 2: unfold `evalAtBasisCLE_TensorRSModel`.
  rw [evalAtBasisCLE_TensorRSModel_apply]
  -- Step 3: unfold `chartRSTwistInv_apply` and `TensorRSSpace.toModel`.
  -- `(chartRSTwistInv α b r r M) ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) = (M (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compCLM chartJ)).compCLM chartJinv`.
  rw [chartRSTwistInv_apply]
  -- Step 4: evaluate the outer `compCLM chartJinv` at the basis tuple `chartModelBasis ∘ Jdx`.
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The argument is now (M (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compCLM chartJ)) (λ i, chartJinv α b (chartModelBasis E (Jdx i))).
  -- M = TensorRSSpace.toModel of our CLM. At the data level it's just the CLM itself.
  -- We don't `set` here, to avoid Lean creating opaque `have this := ...; this` blobs.
  -- Apply `tensorSlotSubstCLM_apply` directly via `change` to drop the `TensorRSSpace.toModel` shell.
  -- Define the inner tuple Ri : Fin r → E (defined in the final goal after compCLM).
  -- Define ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) = (eval0SCLE r).symm (Pi.single Idx 1) (kept inline below).
  -- At the data level: TensorRSSpace.toModel T_clm ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) = T_clm ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) as a CMM application.
  -- Step 5: turn the LHS to use `tensorSlotSubstCLM_apply` via a `change` to a definitionally
  -- equal form (TensorRSSpace.toModel is the `arrowCongr` of identity-at-data CLEs).
  -- Apply tensorSlotSubstCLM_apply.
  have hslot_apply :
      ∀ (m : Fin r → TangentSpace I b),
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin r => TangentSpace I b) ℝ from
          (tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b X)))
            (show Tensor0SSpace r I b from
              (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
                (fun _ : Fin r => chartJ (I := I) (M := M) α b)))) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin r => TangentSpace I b) ℝ from
          (show Tensor0SSpace r I b from
            (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b))))
          (fun i =>
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b X) i) (m i)) := by
    intro m
    exact tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X))
      _ m
  -- Convert LHS to use `tensorSlotSubstCLM_apply`. At the data level, the LHS reads
  --   (TensorRSSpace.toModel (tensorSlotSubstCLM r b (...))) (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compCLM chartJ) (λ i, chartJinv α b (chartModelBasis (Jdx i)))
  -- which equals
  --   (tensorSlotSubstCLM r b (...)) ((((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compCLM chartJ) : Tensor0SSpace r I b) (λ i, ...)
  -- as a CMM application. This is `rfl` because TensorRSSpace.toModel is the `arrowCongr` of
  -- identity-as-function CLEs.
  change (show ContinuousMultilinearMap ℝ
        (fun _ : Fin r => TangentSpace I b) ℝ from
      (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b X)))
        (show Tensor0SSpace r I b from
          (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))))
      (fun i : Fin r =>
        chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx i))) = _
  rw [hslot_apply]
  -- LHS is now:
  --   (((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))).compCLM chartJ) (λ i, (tangentSlotCLM r k Φ_b i) (chartJinv α b (chartModelBasis E (Jdx i))))
  -- Unfold the outer compCLM:
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Now LHS is:
  --   ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) (λ i, chartJ α b ((tangentSlotCLM r k Φ_b i) (chartJinv α b (chartModelBasis E (Jdx i)))))
  -- Define the inner tuple Ri : Fin r → E via `set`. We abstract the inner fun-form.
  -- `set Ri := fun i => ...` may fail to abstract if the goal has β-redex differences;
  -- we follow up with an explicit `change` to ensure the goal carries `Ri`.
  set Ri : Fin r → E :=
    (fun i : Fin r =>
      chartJ (I := I) (M := M) α b
        ((tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X) i)
          (chartJinv (I := I) (M := M) α b
            ((chartModelBasis E) (Jdx i)))))
    with hRi_def
  change ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = _
  -- Reduce: for i ≠ k, Ri i = chartModelBasis E (Jdx i); for i = k, Ri k = Φ_b_triv (chartModelBasis E (Jdx k)).
  -- We need a closed expression for ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = ∑ a M_{a, Jdx k} * ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) (slot-k = chartModelBasis E a, others = chartModelBasis E (Jdx i)).
  -- Strategy: by-cases on whether ∀ i ≠ k, Idx i = Jdx i.
  by_cases hagree : ∀ i : Fin r, i ≠ k → Idx i = Jdx i
  · -- Agree case: show ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = M_{Idx k, Jdx k}.
    rw [if_pos hagree]
    -- For i ≠ k, R i = chartModelBasis E (Jdx i) = chartModelBasis E (Idx i).
    have hRi_other : ∀ i, i ≠ k →
        Ri i = (chartModelBasis E) (Idx i) := by
      intro i hi
      have hother := tangentSlotCLM_other (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X) (i := i) hi
      simp only [Ri, hother, ContinuousLinearMap.id_apply]
      -- Now Ri i = chartJ α b (chartJinv α b (chartModelBasis E (Jdx i)))
      rw [chartJ_chartJinv_on_chartSource (I := I) (M := M) α hb]
      rw [hagree i hi]
    -- For i = k, Ri k = Φ_b_triv (chartModelBasis E (Jdx k)).
    have hRi_at_k :
        Ri k = ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
          ((chartModelBasis E) (Jdx k)) := by
      have hself := tangentSlotCLM_self (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)
      simp only [Ri, hself]
      -- Now Ri k = chartJ α b (Φ_b (chartJinv α b (chartModelBasis E (Jdx k)))).
      -- The trivialised parallel CLM at chartBasis-vector input is:
      --   inCoordinates α b α b Φ_b = trivToE ∘ Φ_b ∘ trivFromE.
      -- = chartJ ∘ Φ_b ∘ chartJinv (since trivToE = chartJ, trivFromE = chartJinv).
      -- We need:
      --   trivializationAt (E →L E) ... ⟨b, Φ_b⟩.2 = chartJ ∘ Φ_b ∘ chartJinv (as CLMs)
      -- which is `inCoordinates E (TangentSpace I) E (TangentSpace I) α b α b Φ_b`,
      -- applied to a model vector.
      rfl
    -- Now compute ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri using multilinearity.
    -- Strategy: write Ri k = ∑_a M_{a, Jdx k} • chartModelBasis E a, then expand ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) via multilinearity.
    -- Define M := matrix of Φ_b_triv in chartModelBasis.
    set M_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun a c => ((chartModelBasis E).repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) c))) a
      with hM_mat_def
    -- Decompose Ri k as the sum of M_{a, Jdx k} • chartModelBasis E a.
    have hRi_k_decomp :
        Ri k = ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a := by
      rw [hRi_at_k]
      -- The standard basis decomposition: any v ∈ E equals ∑ a (chartModelBasis E).repr v a • chartModelBasis E a.
      simp only [hM_mat_def]
      exact ((chartModelBasis E).sum_repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) (Jdx k)))).symm
    -- Multilinearity: ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) (λ i, Ri i) — substitute Ri k = ∑ a M_{a, Jdx k} • chartModelBasis E a.
    -- Use map_sum_finset on the k-th slot.
    -- Define the "slot-replaced" tuple: for input a : Fin (finrank E),
    --   tuple_a i := if i = k then chartModelBasis E a else Ri i = chartModelBasis E (Idx i).
    have hsigma_eq :
        ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) := by
      -- Use map_update_sum-style multilinearity on slot k.
      have hupdate :
          Ri = Function.update Ri k (Ri k) := by
        funext i; simp
      -- Easier: rewrite Ri k as the sum, then use map_sum on slot k via update.
      -- Step 1: turn Ri into Function.update Ri k (∑ a M_{a, Jdx k} • chartModelBasis E a).
      have hRi_update : Ri = Function.update Ri k
          (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a) := by
        rw [← hRi_k_decomp]
        funext i; by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hRi_update]
      -- σ (update Ri k (∑ a x_a • e_a)) = ∑ a x_a • σ (update Ri k e_a).
      -- Use the underlying `MultilinearMap.map_update_sum` (the CMM coerces to MM via `coe_coe`).
      have hsum := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_sum
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
        (g := fun a : Fin (Module.finrank ℝ E) => M_mat a (Jdx k) • (chartModelBasis E) a)
        (m := Ri)
      -- `f.toMultilinearMap (args) = f (args)` via `ContinuousMultilinearMap.coe_coe`.
      have hsum' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k
              (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a)) =
          ∑ a : Fin (Module.finrank ℝ E),
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) := hsum
      rw [hsum']
      refine Finset.sum_congr rfl ?_
      intro a _
      have hsmul := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_smul
          (m := Ri) (i := k) (c := M_mat a (Jdx k)) (x := (chartModelBasis E) a)
      have hsmul' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) =
          M_mat a (Jdx k) •
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k ((chartModelBasis E) a)) := hsmul
      rw [hsmul']
      have hupd_eq :
          Function.update Ri k ((chartModelBasis E) a) =
            fun i => if i = k then (chartModelBasis E) a
                     else (chartModelBasis E) (Idx i) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi, hRi_other i hi]
      rw [hupd_eq]
      rw [smul_eq_mul]
    rw [hsigma_eq]
    -- Now `((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))` applied to (λ i, if i = k then chartModelBasis E a else chartModelBasis E (Idx i))
    -- equals (Pi.single Idx 1) at the function (λ i, if i = k then a else Idx i).
    -- Rewrite via `eval0SCLE_symm_pi_single_at_basis_tuple`.
    have hphi_form :
        ∀ a : Fin (Module.finrank ℝ E),
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) =
            Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
              (fun i => if i = k then a else Idx i) := by
      intro a
      -- The tuple `(if i = k then a else Idx i)` equals `Function.update Idx k a` written as a function.
      -- We can express the tuple as `chartModelBasis E ∘ (fun i => if i = k then a else Idx i)`.
      have hfeq :
          (fun i : Fin r => if i = k then (chartModelBasis E) a
                            else (chartModelBasis E) (Idx i)) =
          (fun i : Fin r => (chartModelBasis E)
            ((fun i' => if i' = k then a else Idx i') i)) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hfeq]
      have := eval0SCLE_symm_pi_single_at_basis_tuple (E := E) r Idx
        (fun i' => if i' = k then a else Idx i')
      change (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
        (fun k_0 : Fin r => (chartModelBasis E) (
          (fun i' => if i' = k then a else Idx i') k_0)) = _
      exact this
    -- Apply hphi_form.
    have hsum_simp :
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Idx i)) =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [hphi_form a]
    rw [hsum_simp]
    -- Now Pi.single Idx 1 (fun i => if i = k then a else Idx i) = if Idx = (fun i => if i = k then a else Idx i) then 1 else 0
    -- = if Idx k = a then 1 else 0 (since other slots agree by construction).
    have hpi_simp :
        ∀ a : Fin (Module.finrank ℝ E),
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) =
          (if Idx k = a then (1 : ℝ) else 0) := by
      intro a
      classical
      by_cases ha : Idx k = a
      · -- Idx = (fun i => if i = k then a else Idx i).
        have hidx_eq : Idx = (fun i : Fin r => if i = k then a else Idx i) := by
          funext i
          by_cases hi : i = k
          · subst hi; simp [ha]
          · simp [hi]
        rw [← hidx_eq]
        rw [Pi.single_eq_same]
        simp [ha]
      · -- Idx ≠ (fun i => if i = k then a else Idx i) (disagree at i = k).
        have hne : (fun i : Fin r => if i = k then a else Idx i) ≠ Idx := by
          intro heq
          have hk := congr_fun heq k
          simp at hk
          exact ha hk.symm
        rw [Pi.single_eq_of_ne hne]
        simp [ha]
    have hsum_simp2 :
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          Pi.single (M := fun _ => ℝ) Idx (1 : ℝ)
            (fun i => if i = k then a else Idx i) =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          (if Idx k = a then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [hpi_simp a]
    rw [hsum_simp2]
    -- The sum collapses to M_{Idx k, Jdx k}.
    have hcollapse :
        (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
            (if Idx k = a then (1 : ℝ) else 0)) =
          M_mat (Idx k) (Jdx k) := by
      rw [Finset.sum_eq_single (Idx k)]
      · simp
      · intro a _ ha
        have : Idx k ≠ a := fun h => ha h.symm
        simp [this]
      · intro hne
        exfalso; exact hne (Finset.mem_univ _)
    rw [hcollapse]
  · -- Disagree case: show ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = 0.
    rw [if_neg hagree]
    -- There exists some i₀ ≠ k with Idx i₀ ≠ Jdx i₀.
    have hagree' : ∃ i : Fin r, i ≠ k ∧ Idx i ≠ Jdx i := by
      classical
      by_contra hall
      apply hagree
      intro i hi
      by_contra hne
      exact hall ⟨i, hi, hne⟩
    obtain ⟨i₀, hi₀_ne_k, hi₀_disagree⟩ := hagree'
    -- For i ≠ k, Ri i = chartModelBasis E (Jdx i).
    have hRi_other : ∀ i, i ≠ k →
        Ri i = (chartModelBasis E) (Jdx i) := by
      intro i hi
      have hother := tangentSlotCLM_other (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X) (i := i) hi
      simp only [Ri, hother, ContinuousLinearMap.id_apply]
      rw [chartJ_chartJinv_on_chartSource (I := I) (M := M) α hb]
    -- Recall: ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) = (eval0SCLE r).symm (Pi.single Idx 1).
    -- We must show ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = 0 when Idx and Jdx differ at some i₀ ≠ k.
    -- Strategy: rewrite Ri at slot k as a sum ∑ a M_{a, Jdx k} • chartModelBasis E a.
    -- Then ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri = ∑ a M_{a, Jdx k} · ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) (slot k = chartModelBasis E a, others = chartModelBasis E (Jdx i)).
    -- Each ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))-term equals Pi.single Idx 1 (fun i => if i = k then a else Jdx i).
    -- Since Jdx i₀ ≠ Idx i₀ (and i₀ ≠ k), the tuple (fun i => if i = k then a else Jdx i)
    -- disagrees with Idx at i₀ (regardless of a), so Pi.single Idx 1 = 0.
    set M_mat : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun a c => ((chartModelBasis E).repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) c))) a
      with hM_mat_def
    have hRi_at_k :
        Ri k = ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2)
          ((chartModelBasis E) (Jdx k)) := by
      have hself := tangentSlotCLM_self (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)
      simp only [Ri, hself]
      rfl
    have hRi_k_decomp :
        Ri k = ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a := by
      rw [hRi_at_k]
      simp only [hM_mat_def]
      exact ((chartModelBasis E).sum_repr
        ((trivializationAt (E →L[ℝ] E)
          (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
          ⟨b, chartLeviCivitaParallelCLM (I := I) g α b X⟩).2
          ((chartModelBasis E) (Jdx k)))).symm
    have hRi_update : Ri = Function.update Ri k
        (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a) := by
      rw [← hRi_k_decomp]
      funext i; by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    have hsigma_eq :
        ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) Ri =
        ∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i)) := by
      rw [hRi_update]
      have hsum := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_sum
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
        (g := fun a : Fin (Module.finrank ℝ E) => M_mat a (Jdx k) • (chartModelBasis E) a)
        (m := Ri)
      have hsum' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k
              (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) • (chartModelBasis E) a)) =
          ∑ a : Fin (Module.finrank ℝ E),
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) := hsum
      rw [hsum']
      refine Finset.sum_congr rfl ?_
      intro a _
      have hsmul := ((eval0SCLE (E := E) r).symm
        (Pi.single Idx (1 : ℝ))).toMultilinearMap.map_update_smul
          (m := Ri) (i := k) (c := M_mat a (Jdx k)) (x := (chartModelBasis E) a)
      have hsmul' :
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (Function.update Ri k (M_mat a (Jdx k) • (chartModelBasis E) a)) =
          M_mat a (Jdx k) •
            ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
              (Function.update Ri k ((chartModelBasis E) a)) := hsmul
      rw [hsmul']
      have hupd_eq :
          Function.update Ri k ((chartModelBasis E) a) =
            fun i => if i = k then (chartModelBasis E) a
                     else (chartModelBasis E) (Jdx i) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi, hRi_other i hi]
      rw [hupd_eq]
      rw [smul_eq_mul]
    rw [hsigma_eq]
    -- Now every term ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) (...) = 0 since Jdx i₀ ≠ Idx i₀ at i₀ ≠ k.
    have hphi_zero :
        ∀ a : Fin (Module.finrank ℝ E),
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i)) = 0 := by
      intro a
      have hfeq :
          (fun i : Fin r => if i = k then (chartModelBasis E) a
                            else (chartModelBasis E) (Jdx i)) =
          (fun i : Fin r => (chartModelBasis E)
            ((fun i' => if i' = k then a else Jdx i') i)) := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      rw [hfeq]
      have hwell := eval0SCLE_symm_pi_single_at_basis_tuple (E := E) r Idx
        (fun i' => if i' = k then a else Jdx i')
      change (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
        (fun k_0 : Fin r => (chartModelBasis E) (
          (fun i' => if i' = k then a else Jdx i') k_0)) = 0
      rw [hwell]
      -- Pi.single Idx 1 (fun i' => if i' = k then a else Jdx i') = 0 since they differ at i₀.
      have hne : (fun i : Fin r => if i = k then a else Jdx i) ≠ Idx := by
        intro heq
        have hi₀_val := congr_fun heq i₀
        simp [hi₀_ne_k] at hi₀_val
        exact hi₀_disagree hi₀_val.symm
      rw [Pi.single_eq_of_ne hne]
    rw [show (∑ a : Fin (Module.finrank ℝ E), M_mat a (Jdx k) *
          ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)))
            (fun i => if i = k then (chartModelBasis E) a
                      else (chartModelBasis E) (Jdx i))) = 0 from ?_]
    rw [Finset.sum_eq_zero]
    intro a _
    rw [hphi_zero a]
    simp

/-! ## Headline -/

/-- **Chart-source smoothness of the hom-trivialised slot-substitution CLM
for the chart-Levi-Civita parallel CLM at a chart-basis vector field.**

For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, and a slot index
`k : Fin r`, the function

```
b ↦ (trivializationAt (TensorRSModel r r ℝ E)
      (fun y : M => TensorRSSpace r r I y) α
      ⟨b, tensorSlotSubstCLM r b (tangentSlotCLM r k
            (chartLeviCivitaParallelCLM g α b
              (chartBasisVecFiber α j)))⟩).2
```

is `ContMDiffOn I 𝓘(ℝ, TensorRSModel r r ℝ E) ∞` on `(chartAt H α).source`. -/
theorem tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) (k : Fin r) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r r ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j)))) : TensorRSSpace r r I b)⟩).2)
      ((chartAt H α).source) := by
  classical
  -- Reduce to per-entry smoothness via `contMDiffOn_into_tensorRSModel_of_eval_basis`.
  -- The target type `TensorRSModel r r ℝ E` is by definition
  -- `Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E =
  --  ContinuousMultilinearMap ℝ (fun _ => E) ℝ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ => E) ℝ`.
  -- Rewrite to the unfolded `→L`-of-CMM form using `change`.
  change ContMDiffOn I
    𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) ∞
    (fun b : M =>
      (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α
        ⟨b, TensorRSSpace.ofCLM (𝕜 := ℝ) (I := I)
          (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α j))))⟩).2)
    ((chartAt H α).source)
  rw [contMDiffOn_into_tensorRSModel_of_eval_basis (E := E) (r := r) (s := r) (I := I)]
  intro Idx Jdx
  -- For each `(Idx, Jdx)`, the entry is the matrix entry on agree-case
  -- (smooth via B.1 + projection) or zero (smooth).
  -- Apply the closed-form expansion.
  have hentry_eq :
      ∀ b ∈ (chartAt H α).source,
        evalAtBasisCLE_TensorRSModel (E := E) r r
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, TensorRSSpace.ofCLM (𝕜 := ℝ) (I := I)
              (tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))⟩).2)
          (Idx, Jdx) =
        (if ∀ i : Fin r, i ≠ k → Idx i = Jdx i then
          (((chartModelBasis E).repr
            (((trivializationAt (E →L[ℝ] E)
              (fun b' : M => TangentSpace I b' →L[ℝ] TangentSpace I b') α
              ⟨b, chartLeviCivitaParallelCLM (I := I) g α b
                (chartBasisVecFiber (I := I) α j)⟩).2)
              ((chartModelBasis E) (Jdx k)))) (Idx k))
        else 0) := by
    intro b hb
    -- The trivializationAt expression `((triv_RR α) ⟨b, T_b⟩).2 = (triv_RR α).continuousLinearMapAt ℝ b T_b`
    -- on the base set. Use `coe_linearMapAt_of_mem` to bridge.
    have hbaseHom : b ∈ (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).baseSet := by
      change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).baseSet
      refine ⟨?_, ?_⟩
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact hb
      · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
        exact hb
    -- Apply the closed-form expansion.
    have hkey := slotSubst_trivProj_entry_closedForm
      (I := I) (M := M) g r α k
      (X := (chartBasisVecFiber (I := I) α j)) (b := b) hb Idx Jdx
    -- Bridge: `.continuousLinearMapAt ℝ b T = ((triv ⟨b, T⟩)).2`. This is
    -- `Bundle.Trivialization.continuousLinearMapAt_apply` which on the base set
    -- gives `linearMapAt = (triv ⟨b, T⟩).2`, and `linearMapAt = continuousLinearMapAt`
    -- as functions.
    have hbridge_clmat :
        ∀ T : TensorRSSpace r r I b,
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b T =
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α) ⟨b, T⟩).2 := by
      intro T
      -- `continuousLinearMapAt = linearMapAt` as functions.
      have hclmat :
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b T =
          (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).linearMapAt ℝ b T := rfl
      rw [hclmat]
      -- `linearMapAt` on base set equals `(triv ⟨b, T⟩).2` via `coe_linearMapAt_of_mem`.
      have hcoe := (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α).coe_linearMapAt_of_mem
        (R := ℝ) (b := b) hbaseHom
      exact congrFun hcoe T
    -- Apply the bridge to hkey.
    rw [hbridge_clmat] at hkey
    -- The remaining typeclass-level annotation: `TensorRSSpace.ofCLM (...)` should be
    -- definitionally equal to `((...) : TensorRSSpace r r I b)`. Close with the bridged hkey.
    exact hkey
  -- Now smoothness via congruence with the closed form.
  refine ContMDiffOn.congr ?_ hentry_eq
  -- The closed form is smooth on chart source.
  by_cases hagree : ∀ i : Fin r, i ≠ k → Idx i = Jdx i
  · -- The agree-case branch: the entry equals the matrix entry, which is smooth via B.1.
    have hagree_smooth :=
      chartLeviCivitaParallelCLM_chartBasisVec_matrixEntry_contMDiffOn_chartSource
        (I := I) (M := M) g α j (Idx k) (Jdx k)
    refine hagree_smooth.congr ?_
    intro b _
    rw [if_pos hagree]
  · -- The disagree branch: the entry is 0 (constant), hence smooth.
    have hzero_smooth : ContMDiffOn I 𝓘(ℝ) ∞ (fun (_ : M) => (0 : ℝ))
        ((chartAt H α).source) := contMDiffOn_const
    refine hzero_smooth.congr ?_
    intro b _
    rw [if_neg hagree]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource

end Sanity
