import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotSubstCLMTrivImageContMDiff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionChartSourceContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProjBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorRSModelEvalBasis
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative

/-!
# Chart-source smoothness of the trivialised slot-correction sections

For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, and an `(r, s)`-tensor
section `T : Π b : M, TensorRSSpace r s I b` that is smooth as a bundle
section, this file ships chart-source smoothness of the trivialised image of
the chart-frame Christoffel slot-correction CLMs

```
b ↦ chartTensorRSInputSlotCorrection r s g α T (chartBasisVecFiber α j) b k
b ↦ chartTensorRSOutputSlotCorrection r s g α T (chartBasisVecFiber α j) b l
```

at chart `α`.

## Headlines

* `chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource`
* `chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource`

## Proof structure

The input slot correction equals `(T b).comp (SubstCLM_b)` where
`SubstCLM_b := tensorSlotSubstCLM r b (tangentSlotCLM r k Φ_b)` and
`Φ_b := chartLeviCivitaParallelCLM g α b (chartBasisVecFiber α j)`. The
output slot correction has the symmetric shape `(SubstCLM_b).comp (T b)`
(with the substitution acting on the output slot instead).

The bridge identity (proved as `triv_compRR_eq_trivT_compL_trivS` below) says
that the trivialisation projection of a Hom-bundle composition equals the
composition of the individual trivialisation projections on the chart-`α`
base set. This factors the trivialised image of the slot correction into a
CLM-composition of two ContMDiffOn-smooth factors, which combine via
`ContMDiffOn.clm_comp`.

The two factors are:

* The trivialised image of the smooth tensor section `T b`. This is smooth
  on the chart-`α` base set because of bundle smoothness of `T`
  (`Trivialization.contMDiffOn_section_baseSet_iff`).
* The trivialised image of `SubstCLM_b` for the chart-basis input vector.
  This is exactly the headline shipped by `SlotSubstCLMTrivImageContMDiff`
  (S1).
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

/-! ## Auxiliary bridge: trivialisation projection of a composition

For two smooth CLM-valued bundle sections of compatible types, the
trivialisation projection of their pointwise composition equals the
composition of the individual projections on the chart-`α` base set. This is
the structural fact that the Hom-bundle pretrivialisation formula commutes
with composition once the inner chart-`(α, b)`-twist round-trips back to the
identity. -/

/-- The trivialisation-projection of `(T b).comp S_b` on chart source, where
`T b ∈ TensorRSSpace r s I b` and `S_b ∈ TensorRSSpace r r I b`. The result
equals the composition (in `Tensor0SModel r ℝ E →L Tensor0SModel s ℝ E`) of
their individual projections. -/
private lemma triv_compInput_eq_trivT_compL_trivS
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (Tb : TensorRSSpace r s I b) (Sb : TensorRSSpace r r I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α
        ⟨b, ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            : TensorRSSpace r s I b)⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, Tb⟩).2).comp
        ((trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, Sb⟩).2) := by
  classical
  -- Reduce each `(triv ⟨b, ·⟩).2` to `triv.continuousLinearMapAt ℝ b ·`,
  -- then apply the bridge identity
  -- `triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel` to expose the
  -- chart-`(α, b)`-twist structure on both sides.
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  have hbase_rs : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · exact hb_base
    · exact hb_base
  have hbase_rr : b ∈ (trivializationAt (TensorRSModel r r ℝ E)
      (fun y : M => TensorRSSpace r r I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  -- Re-express each `(triv ⟨b, T⟩).2` via `continuousLinearMapAt`.
  have hLHS_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              : TensorRSSpace r s I b)⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              : TensorRSSpace r s I b)) := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
                : TensorRSSpace r s I b)) =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
              (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
                : TensorRSSpace r s I b)) := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hT_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, Tb⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b Tb := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hS_coe :
      (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α ⟨b, Sb⟩).2 =
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b Sb := by
    have hcoeRR := (trivializationAt (TensorRSModel r r ℝ E)
        (fun y : M => TensorRSSpace r r I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rr
    have h1 :
        (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).continuousLinearMapAt ℝ b Sb =
        (trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α).linearMapAt ℝ b Sb := rfl
    rw [h1]
    exact (congrFun hcoeRR _).symm
  -- Rewrite both sides via `continuousLinearMapAt`.
  rw [hLHS_coe, hT_coe, hS_coe]
  -- Now apply the bridge identity from `TrivProjBridge`.
  have hbridge_LHS :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb
      (T := (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            : TensorRSSpace r s I b)))
  have hbridge_T :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb (T := Tb)
  have hbridge_S :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r r α (b := b) hb (T := Sb)
  rw [hbridge_LHS, hbridge_T, hbridge_S]
  -- Both sides are now in terms of `chartRSTwistInv`. Reduce to the
  -- multilinear-slot composition statement and check equality on an
  -- arbitrary input.
  refine ContinuousLinearMap.ext ?_
  intro α'
  -- Unfold the LHS: chartRSTwistInv applied to `toModel ((Tb).comp Sb)`.
  rw [chartRSTwistInv_apply]
  -- Unfold the RHS comp-apply.
  rw [ContinuousLinearMap.comp_apply, chartRSTwistInv_apply, chartRSTwistInv_apply]
  -- At this point both sides are `ContinuousMultilinearMap` values
  -- after a `compContinuousLinearMap` post-composition with `chartJinv`.
  -- The LHS:
  --   (TensorRSSpace.toModel ((Tb).comp Sb) (α'.compCLM chartJ)).compCLM chartJinv
  -- The RHS:
  --   (TensorRSSpace.toModel Tb
  --     (((TensorRSSpace.toModel Sb (α'.compCLM chartJ)).compCLM chartJinv).compCLM chartJ))
  --     .compCLM chartJinv
  -- Apply both sides at an arbitrary tuple `w : Fin s → E`.
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- After the outer `compCLM chartJinv` evaluation, both sides reduce to
  --   inner_LHS (fun i => chartJinv (w i))
  --   inner_RHS (fun i => chartJinv (w i))
  -- so it suffices to prove `inner_LHS = inner_RHS` as ContMultilinearMaps.
  -- We do that by extensionality at an arbitrary `v : Fin s → E`.
  -- Use `change` to expose `TensorRSSpace.toModel T_? = T_?` at the
  -- function level (toModel is arrowCongr of identity-as-function CLEs).
  -- LHS inner-CMM at `(fun i => chartJinv (w i))` is the CMM
  --   (TensorRSSpace.toModel ((Tb).comp Sb))(α'.compCLM chartJ)
  -- applied to `(fun i => chartJinv (w i))`. At the function level this is
  --   ((Tb).comp Sb)(α'.compCLM chartJ) at `(fun i => chartJinv (w i))`
  --   = Tb (Sb (α'.compCLM chartJ)) at `(fun i => chartJinv (w i))`.
  -- RHS inner-CMM at `(fun i => chartJinv (w i))` is the CMM
  --   (TensorRSSpace.toModel Tb)((toModel Sb (α'.compCLM chartJ)).compCLM chartJinv .compCLM chartJ)
  -- applied to `(fun i => chartJinv (w i))`. At the function level:
  --   Tb (((Sb (α'.compCLM chartJ)).compCLM chartJinv).compCLM chartJ)
  --     at `(fun i => chartJinv (w i))`.
  -- We need to show these are equal. Apply `Tb` after showing the inner
  -- argument is equal (as a CMM).
  -- We use `change` to expose the data-level Sb / Tb / toModel reductions.
  change
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))))
      (fun i => chartJinv (I := I) (M := M) α b (w i)) = _
  -- Now LHS is `Tb (Sb (α'.compCLM chartJ))` at `(fun i => chartJinv (w i))`.
  -- RHS has `Sb`-arg wrapped by the chartJinv-then-chartJ round-trip.
  -- Reduce the RHS via the round-trip identity.
  -- Build the round-trip identity as an inner CMM equality.
  have hinner_round_trip :
      ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
              (fun _ : Fin r => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)) =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) := by
    refine ContinuousMultilinearMap.ext ?_
    intro u
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext kk
    exact chartJinv_chartJ_self (I := I) (M := M) α hb_base (u kk)
  -- Apply Tb-extensionality. We use a `change` on the RHS to expose the structure.
  change _ =
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
        ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from Sb)
              (α'.compContinuousLinearMap
                (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
                (fun _ : Fin r => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
      (fun i => chartJinv (I := I) (M := M) α b (w i))
  rw [hinner_round_trip]

/-- Output-slot counterpart of `triv_compInput_eq_trivT_compL_trivS`. -/
private lemma triv_compOutput_eq_trivS_compL_trivT
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (Tb : TensorRSSpace r s I b) (Sb : TensorRSSpace s s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α
        ⟨b, ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            : TensorRSSpace r s I b)⟩).2 =
      ((trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α
          ⟨b, Sb⟩).2).comp
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, Tb⟩).2) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  have hbase_rs : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  have hbase_ss : b ∈ (trivializationAt (TensorRSModel s s ℝ E)
      (fun y : M => TensorRSSpace s s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    exact ⟨hb_base, hb_base⟩
  have hLHS_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              : TensorRSSpace r s I b)⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              : TensorRSSpace r s I b)) := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
                : TensorRSSpace r s I b)) =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
              (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
                  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
                : TensorRSSpace r s I b)) := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hT_coe :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, Tb⟩).2 =
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb := by
    have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_rs
    have h1 :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Tb =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b Tb := rfl
    rw [h1]
    exact (congrFun hcoeRS _).symm
  have hS_coe :
      (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α ⟨b, Sb⟩).2 =
        (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α).continuousLinearMapAt ℝ b Sb := by
    have hcoeRR := (trivializationAt (TensorRSModel s s ℝ E)
        (fun y : M => TensorRSSpace s s I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_ss
    have h1 :
        (trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α).continuousLinearMapAt ℝ b Sb =
        (trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α).linearMapAt ℝ b Sb := rfl
    rw [h1]
    exact (congrFun hcoeRR _).symm
  rw [hLHS_coe, hT_coe, hS_coe]
  have hbridge_LHS :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb
      (T := (((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb).comp
              (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            : TensorRSSpace r s I b)))
  have hbridge_T :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) r s α (b := b) hb (T := Tb)
  have hbridge_S :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
      (I := I) (M := M) s s α (b := b) hb (T := Sb)
  rw [hbridge_LHS, hbridge_T, hbridge_S]
  -- Reduce to multilinear-slot equality.
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [chartRSTwistInv_apply]
  rw [ContinuousLinearMap.comp_apply, chartRSTwistInv_apply, chartRSTwistInv_apply]
  -- LHS: ((Sb.comp Tb)(α'.compCLM chartJ)).compCLM chartJinv
  --   = (Sb(Tb(α'.compCLM chartJ))).compCLM chartJinv
  -- RHS: (Sb((Tb(α'.compCLM chartJ)).compCLM chartJinv .compCLM chartJ)).compCLM chartJinv
  -- The round-trip chartJ ∘ chartJinv = id on chart source reduces RHS inner to
  --   Sb(Tb(α'.compCLM chartJ)), matching LHS.
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- After the outer `compCLM chartJinv`-evaluation at `w`, both sides reduce
  -- to (inner-CMM) (fun i => chartJinv (w i)). So it suffices to prove
  -- inner-CMM equality. We do that by evaluating at an arbitrary `v`.
  -- Use `change` to expose the data-level Sb / Tb / toModel reductions for the
  -- LHS, then for the RHS, then apply the round-trip identity.
  change
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb)
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))))
      (fun i => chartJinv (I := I) (M := M) α b (w i)) = _
  -- Now LHS is `Sb (Tb (α'.compCLM chartJ))` at `(fun i => chartJinv (w i))`.
  -- The RHS has `Sb` applied to `(Tb(α'.compCLM chartJ)).compCLM chartJinv .compCLM chartJ`.
  -- Round-trip identity reduces this to `Tb(α'.compCLM chartJ)`.
  have hround :
      ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
              (fun _ : Fin s => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
            (fun _ : Fin s => chartJ (I := I) (M := M) α b)) =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) := by
    refine ContinuousMultilinearMap.ext ?_
    intro u
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext kk
    exact chartJinv_chartJ_self (I := I) (M := M) α hb_base (u kk)
  -- Use `change` to expose the data-level Sb / Tb / toModel reductions on RHS.
  change _ =
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
      (show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from Sb)
        ((((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Tb)
              (α'.compContinuousLinearMap
                (fun _ : Fin r => chartJ (I := I) (M := M) α b))).compContinuousLinearMap
                (fun _ : Fin s => chartJinv (I := I) (M := M) α b)).compContinuousLinearMap
              (fun _ : Fin s => chartJ (I := I) (M := M) α b)))
      (fun i => chartJinv (I := I) (M := M) α b (w i))
  rw [hround]

/-! ## The input-slot trivialised image is chart-source `ContMDiffOn`

We combine S1 (chart-source smoothness of the trivialised SubstCLM at the
chart-basis input) and the bundle-section smoothness of `T` (via
`Trivialization.contMDiffOn_section_baseSet_iff`) through the bridge
identity `triv_compInput_eq_trivT_compL_trivS`.
-/

/-- **Headline (input slot).**
For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, an input slot
`k : Fin r`, and a bundle-smooth tensor section `T`, the trivialised image
of the chart-`α` Christoffel input-slot correction CLM

```
b ↦ chartTensorRSInputSlotCorrection r s g α T (chartBasisVecFiber α j) b k
```

is `ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞` on `(chartAt H α).source`. -/
theorem chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (T b)))
    (j : Fin (Module.finrank ℝ E)) (k : Fin r) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b k⟩).2)
      ((chartAt H α).source) := by
  classical
  -- Step 1: chart-source baseSet equality.
  have hbase_rs : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet = (chartAt H α).source := by
    change (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).baseSet = _
    have h_r : (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    have h_s : (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    rw [h_r, h_s, Set.inter_self]
    exact DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  -- Step 2: smoothness of `(triv ⟨b, T b⟩).2` on chart source via bundle smoothness.
  have hT_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, T b⟩).2)
      ((chartAt H α).source) := by
    have hsmooth_total :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) x (T x)) := hT
    have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)).mp hsmooth_total.contMDiffOn
    rw [hbase_rs] at hrewrite
    exact hrewrite
  -- Step 3: smoothness of `(triv_RR ⟨b, SubstCLM_b⟩).2` from S1.
  have hSubst_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r r ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r r ℝ E)
          (fun y : M => TensorRSSpace r r I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace r r I b)⟩).2)
      ((chartAt H α).source) :=
    tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r α j k
  -- Step 4: pointwise bridge identity.
  -- On chart source, the trivialised image of the slot correction equals the
  -- CLM-composition of the two trivialised images.
  have hbridge : ∀ b ∈ (chartAt H α).source,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b k⟩).2 =
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2).comp
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace r r I b)⟩).2) := by
    intro b hb
    -- Unfold `chartTensorRSInputSlotCorrection` to `(T b).comp (SubstCLM_b)`.
    have hunfold :
        chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => T b')
          (chartBasisVecFiber (I := I) α j) b k =
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace r I b from
            ((tensorSlotSubstCLM (I := I) r b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace r r I b))
          : TensorRSSpace r s I b) := by
      unfold chartTensorRSInputSlotCorrection
      rfl
    rw [hunfold]
    exact triv_compInput_eq_trivT_compL_trivS
      (I := I) (M := M) r s α (b := b) hb (Tb := T b)
      (Sb := ((tensorSlotSubstCLM (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))))
        : TensorRSSpace r r I b))
  -- Step 5: clm_comp + congruence.
  -- The model fibre type `TensorRSModel r s ℝ E` definitionally unfolds to a
  -- `→L[ℝ]`-space; `ContMDiffOn.clm_comp` operates on such CLM-valued maps.
  -- We use `ContMDiffOn.clm_comp` directly: hT_proj produces a CLM-valued map
  -- and so does hSubst_proj, and their composition is also CLM-valued.
  have hcomp : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2).comp
          ((trivializationAt (TensorRSModel r r ℝ E)
            (fun y : M => TensorRSSpace r r I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) r b
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace r r I b)⟩).2))
      ((chartAt H α).source) := hT_proj.clm_comp hSubst_proj
  -- Final: congruence.
  refine hcomp.congr ?_
  intro b hb
  exact hbridge b hb

/-! ## The output-slot trivialised image is chart-source `ContMDiffOn`

Symmetric to the input-slot case, using `triv_compOutput_eq_trivS_compL_trivT`.
The substituted CLM here is `tensorSlotSubstCLM s b (tangentSlotCLM s l Φ_b)`,
viewed as an `s s`-tensor section, composed *on the left* with `T b`.
-/

/-- **Headline (output slot).**
For a closed Riemannian manifold `(M, g)`, a chart base point `α : M`, a
chart-basis direction `j : Fin (Module.finrank ℝ E)`, an output slot
`l : Fin s`, and a bundle-smooth tensor section `T`, the trivialised image
of the chart-`α` Christoffel output-slot correction CLM

```
b ↦ chartTensorRSOutputSlotCorrection r s g α T (chartBasisVecFiber α j) b l
```

is `ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞` on `(chartAt H α).source`. -/
theorem chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (T b)))
    (j : Fin (Module.finrank ℝ E)) (l : Fin s) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b l⟩).2)
      ((chartAt H α).source) := by
  classical
  -- Step 1: chart-source baseSet equality (same as input-side proof).
  have hbase_rs : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet = (chartAt H α).source := by
    change (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
        (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).baseSet = _
    have h_r : (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    have h_s : (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet =
          (trivializationAt E (TangentSpace I) α).baseSet := rfl
    rw [h_r, h_s, Set.inter_self]
    exact DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  -- Step 2: smoothness of `(triv_RS ⟨b, T b⟩).2` on chart source.
  have hT_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, T b⟩).2)
      ((chartAt H α).source) := by
    have hsmooth_total :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) x (T x)) := hT
    have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)).mp hsmooth_total.contMDiffOn
    rw [hbase_rs] at hrewrite
    exact hrewrite
  -- Step 3: smoothness of `(triv_SS ⟨b, SubstCLM_b⟩).2` from S1 (with r↦s).
  have hSubst_proj : ContMDiffOn I 𝓘(ℝ, TensorRSModel s s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel s s ℝ E)
          (fun y : M => TensorRSSpace s s I y) α
          ⟨b, ((tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace s s I b)⟩).2)
      ((chartAt H α).source) :=
    tensorSlotSubstCLM_chartLeviCivita_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g s α j l
  -- Step 4: pointwise bridge identity.
  -- On chart source: trivialised image of the output correction = CLM-comp
  -- of S1's trivialised image (on the left) with `T b`'s trivialised image
  -- (on the right).
  have hbridge : ∀ b ∈ (chartAt H α).source,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T b')
                (chartBasisVecFiber (I := I) α j) b l⟩).2 =
        ((trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) s b
                (tangentSlotCLM (I := I) s l
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace s s I b)⟩).2).comp
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2) := by
    intro b hb
    have hunfold :
        chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => T b')
          (chartBasisVecFiber (I := I) α j) b l =
        ((show Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b from
            ((tensorSlotSubstCLM (I := I) s b
              (tangentSlotCLM (I := I) s l
                (chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α j))))
              : TensorRSSpace s s I b)).comp
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          : TensorRSSpace r s I b) := by
      unfold chartTensorRSOutputSlotCorrection
      rfl
    rw [hunfold]
    exact triv_compOutput_eq_trivS_compL_trivT
      (I := I) (M := M) r s α (b := b) hb (Tb := T b)
      (Sb := ((tensorSlotSubstCLM (I := I) s b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b
            (chartBasisVecFiber (I := I) α j))))
        : TensorRSSpace s s I b))
  -- Step 5: clm_comp + congruence.
  have hcomp : ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        ((trivializationAt (TensorRSModel s s ℝ E)
            (fun y : M => TensorRSSpace s s I y) α
            ⟨b, ((tensorSlotSubstCLM (I := I) s b
                (tangentSlotCLM (I := I) s l
                  (chartLeviCivitaParallelCLM (I := I) g α b
                    (chartBasisVecFiber (I := I) α j))))
                : TensorRSSpace s s I b)⟩).2).comp
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, T b⟩).2))
      ((chartAt H α).source) := hSubst_proj.clm_comp hT_proj
  refine hcomp.congr ?_
  intro b hb
  exact hbridge b hb

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource

end Sanity
