import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Chart-component formula for the upper/lower Christoffel slot corrections

For a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model `I`,
a chart center `α : M`, a smooth tangent vector field `B`, an `(r, s)`-tensor
section `T`, and a base point `b` in the chart `α` source, this file expresses
the `(Idx, Jdx)`-chart-frame component of

* `chartTensorRSInputSlotCorrection r s g α T B b k`
  (the `k`-th upper-slot Christoffel correction), and
* `chartTensorRSOutputSlotCorrection r s g α T B b l`
  (the `l`-th lower-slot Christoffel correction),

projected by the chart-α trivialisation, in closed form as a multilinear value
built from:

* `chartLeviCivitaParallelCLM g α b B`, the chart-`α` Levi-Civita parallel CLM,
  which itself unfolds (via `chartLeviCivitaParallelCLM_apply` and
  `christoffelCorrection_apply`) to a polynomial in chart-Christoffel data
  `chartChristoffel g α i j k` and B's chart components
  `(chartModelBasis E).repr (trivToE α b (B b))`,
* T's chart-frame action `(T b) ω' (chartJinv α b ∘ chartModelBasis ∘ Jdx)`
  applied to a `(0, r)`-CMM input `ω'` and a tuple of chart-frame vectors,
  which evaluated on the chart-frame basis yields T's chart components.

The formulae make no expansion choices: the closed-form RHS exposes the
slot-CLM `chartLeviCivitaParallelCLM g α b B` and the chart-Jacobians
`chartJ α b` / `chartJinv α b` so that any further expansion (into
Christoffel symbols, B's components, T's components) is a direct
substitution of the corresponding `_apply` lemmas of the building blocks.

## Main results

* `chartTensorRSInputSlotCorrection_chartComp_formula` — the closed-form
  chart-component formula for the upper-slot Christoffel correction.
* `chartTensorRSOutputSlotCorrection_chartComp_formula` — the closed-form
  chart-component formula for the lower-slot Christoffel correction.

The right-hand sides are polynomials in chart-Christoffel data, B's chart
components, and T's chart components in the sense described above.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Chart-frame component formula: input slot

The input slot correction `chartTensorRSInputSlotCorrection r s g α T B b k`
is, by definition, `(T b).comp (tensorSlotSubstCLM r b Φ)` where `Φ` is the
`k`-th tangent-slot substitution by `chartLeviCivitaParallelCLM g α b B`.

After projection through the chart-α trivialisation, the
`(Idx, Jdx)`-chart-frame component is:

```
((T b)  ((dualCovariantCMM r Idx).compCLM (chartJ α b ∘ Φ_•)))
  (fun j => chartJinv α b (chartModelBasis E (Jdx j)))
```

Concretely, `Φ_i = chartLeviCivitaParallelCLM g α b B` if `i = k`, and the
identity otherwise. The right-hand side is therefore a value of `T b` on:

* a `(0, r)`-CMM input whose covariant slots are precomposed with the
  chart-Jacobian and either `chartLeviCivitaParallelCLM` (slot `k`) or the
  identity (other slots),
* a tuple of chart-frame vectors `chartJinv α b ∘ chartModelBasis ∘ Jdx`,
  i.e. exactly the chart-`α` coordinate basis vectors at `b`.

The combined expression is a polynomial in:

* chart-Christoffel symbols `chartChristoffel g α i j k`
  (via the explicit expansion of `chartLeviCivitaParallelCLM` in
  `chartLeviCivitaParallelCLM_apply` + `christoffelCorrection_apply`),
* B's chart components `(chartModelBasis E).repr (trivToE α b (B b))`
  (same expansion),
* T's chart components (evaluation of `T b` on tuples of chart-frame
  vectors `chartJinv α b ∘ chartModelBasis ∘ Idx'`, i.e. the chart-frame
  matrix of `T b`).
-/

/-- **Closed-form chart-frame component of the upper-slot Christoffel
correction.** For a smooth Riemannian manifold `(M, g)`, a chart center `α`,
a tangent vector field `B`, an `(r, s)`-tensor section `T`, a base point `b`
in the chart `α` source, an input-slot index `k : Fin r`, and a pair of
chart-frame multi-indices `Idx : Fin r → Fin n` and `Jdx : Fin s → Fin n`,
the `(Idx, Jdx)`-chart-frame component of the `triv-α`-projected upper-slot
Christoffel correction at `b` equals the explicit closed-form value

```
((T b)  ((dualCovariantCMM r Idx).compContinuousLinearMap
            (fun i : Fin r => (chartJ α b).comp
              (tangentSlotCLM r k (chartLeviCivitaParallelCLM g α b B) i))))
  (fun j : Fin s => chartJinv α b (chartModelBasis E (Jdx j)))
```

This is a polynomial in chart-Christoffel data, B's chart components, and
T's chart components in the sense described in the file-level docstring. -/
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun i : Fin r =>
              (chartJ (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) := by
  classical
  -- Bridge: `triv.cLMA(b)` on the slot correction is `chartRSTwistInv ∘ toModel`.
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)]
  -- Unfold the component projection.
  rw [tensorChartComponentProjection_apply]
  -- Unfold `chartRSTwistInv_apply`.
  rw [chartRSTwistInv_apply]
  -- Expose CMM `compContinuousLinearMap` evaluation.
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The slot correction, viewed as a CLM and evaluated at the precomposed
  -- input, factors as `(T b)` applied to a `tensorSlotSubstCLM` value.
  -- `TensorRSSpace.toModel` is identity at the function level, so we get the
  -- raw `chartTensorRSInputSlotCorrection` action.
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
            ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  -- Unfold the input-slot correction's action on its input CMM.
  rw [chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
    ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))]
  -- The intermediate `tensorSlotSubstCLM` value: rewrite `tensorSlotSubstCLM ...`
  -- via `tensorSlotSubstCLM_apply`. After applying `T b` and evaluating, the
  -- proof reduces to a CMM equality between
  --   `tensorSlotSubstCLM r b Phi w_in`
  -- and the precomposed form
  --   `(dualCovariantCMM r Idx).compCLM (fun i => (chartJ α b).comp (Phi i))`.
  -- We lift this CMM equality through `T b` and through the final evaluation.
  -- Name the slot-CLM family `Phi` and the precomposed input CMM `w_in` to
  -- keep the rewrite below compact.
  -- Step: prove the CMM equality first, then transport.
  have hsubst :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin r => TangentSpace I b) ℝ from
        tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))) =
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) := by
    refine ContinuousMultilinearMap.ext ?_
    intro w
    rw [tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b B))
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b)) w]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  -- Lift to a `Tensor0SSpace`-fibre equality (definitionally the same).
  have hsubst_fiber :
      (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))
        : Tensor0SSpace r I b) =
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) :=
    hsubst
  rw [hsubst_fiber]

/-! ## Chart-frame component formula: output slot

The output slot correction `chartTensorRSOutputSlotCorrection r s g α T B b l`
is, by definition, `(tensorSlotSubstCLM s b Ψ).comp (T b)` where `Ψ` is the
`l`-th tangent-slot substitution by `chartLeviCivitaParallelCLM g α b B`.

After projection through the chart-α trivialisation, the
`(Idx, Jdx)`-chart-frame component is:

```
((T b) ((dualCovariantCMM r Idx).compCLM (fun _ => chartJ α b)))
  (fun j => Ψ_j (chartJinv α b (chartModelBasis E (Jdx j))))
```

Concretely, `Ψ_j = chartLeviCivitaParallelCLM g α b B` if `j = l`, and the
identity otherwise. The right-hand side is a value of `T b` on:

* a `(0, r)`-CMM input precomposed by the chart-Jacobian (no slot
  substitution on the input side),
* a tuple of vectors where each chart-frame vector is then mapped through
  the slot-CLM `Ψ_j`.
-/

/-- **Closed-form chart-frame component of the lower-slot Christoffel
correction.** For a smooth Riemannian manifold `(M, g)`, a chart center `α`,
a tangent vector field `B`, an `(r, s)`-tensor section `T`, a base point `b`
in the chart `α` source, an output-slot index `l : Fin s`, and a pair of
chart-frame multi-indices `Idx : Fin r → Fin n` and `Jdx : Fin s → Fin n`,
the `(Idx, Jdx)`-chart-frame component of the `triv-α`-projected lower-slot
Christoffel correction at `b` equals the explicit closed-form value

```
((T b)  ((dualCovariantCMM r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ α b)))
  (fun j : Fin s =>
    tangentSlotCLM s l (chartLeviCivitaParallelCLM g α b B) j
      (chartJinv α b (chartModelBasis E (Jdx j))))
```

This is a polynomial in chart-Christoffel data, B's chart components, and
T's chart components in the sense described in the file-level docstring. -/
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) := by
  classical
  -- Bridge: `triv.cLMA(b)` on the slot correction is `chartRSTwistInv ∘ toModel`.
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)]
  -- Unfold the component projection.
  rw [tensorChartComponentProjection_apply]
  -- Unfold `chartRSTwistInv_apply`.
  rw [chartRSTwistInv_apply]
  -- Expose CMM `compContinuousLinearMap` evaluation.
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The slot correction, viewed as a CLM and evaluated at the precomposed
  -- input, factors as `tensorSlotSubstCLM s b Ψ` applied to `T b ω`.
  -- `TensorRSSpace.toModel` is identity at the function level, so we get the
  -- raw `chartTensorRSOutputSlotCorrection` action.
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
            ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  -- Unfold the output-slot correction's action on its input CMM. The RHS of
  -- `chartTensorRSOutputSlotCorrection_apply` already evaluates the
  -- `tensorSlotSubstCLM`-substituted tuple in place; the resulting form is
  -- exactly our headline RHS.
  exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
    ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))

/-! ## Sanity-check examples -/

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin 1)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) 1 2 g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCovariantCMM (E := E) 1 Idx).compContinuousLinearMap
            (fun i : Fin 1 =>
              (chartJ (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) 1 k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin 2 =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) :=
  chartTensorRSInputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb k Idx Jdx

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) 1 2 g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCovariantCMM (E := E) 1 Idx).compContinuousLinearMap
            (fun _ : Fin 1 => chartJ (I := I) (M := M) α b)))
        (fun j : Fin 2 =>
          tangentSlotCLM (I := I) 2 l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) :=
  chartTensorRSOutputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb l Idx Jdx

end Connection
end Integral
end DifferentialGeometry
