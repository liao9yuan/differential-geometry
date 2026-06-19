import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckRicciArm

/-!
# The Lie-derivative-metric (DeTurck vector-field) arm of the Ricci–DeTurck right-hand side

The Ricci–DeTurck right-hand side at a metric `g` is `deTurckRicciRHS g_bg g = −2 Ric(g) + 𝓛_{W(g)} g`,
where `W(g) = deTurckVF g g_bg` is the DeTurck vector field (the metric `g`-trace of the connection
difference `∇^{LC}(g) − ∇^{LC}(g_bg)`).  The Ricci arm `−2 Ric(g)` is graded by
`deTurckRicciArm_appCc_graded` (`RicciDeTurckRicciArm`).  This file records the **parallel** order-graded
`appCc` decomposition of the second summand — the **Lie arm** `𝓛_{W(g)} g`.

## The order-graded `appCc` decomposition (the Lie arm)

For two realized endpoint metrics `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`, the Lie-arm
difference `𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁'` is, at every base point and on every tangent pair, the
`unitModel` read-off of an order-graded operator-field action on the iterated covariant gradients
`Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the perturbation difference:
```
(𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁')(v 0, v 1)
  = unitModel g₀ 2 (appCc g₀ 2 2 L₀ W₀ + appCc g₀ 3 2 L₁ W₁ + appCc g₀ 4 2 L₂ W₂) x v.
```
The Lie arm is genuinely **second order** in the perturbation difference: `𝓛_W g` reads one derivative of
`W` and `W = deTurckVF g g_bg` reads one derivative of `g`, so the principal symbol contributes a `∂²(T −
T')` (the order-`2` slot `L₂`); unlike the Ricci arm, the convective term `W^k ∂_k g` of `𝓛_W g` also
linearizes to a genuine `∂¹(T − T')` slot, so `L₁` is in general nonzero.

`deTurckLieArm_appCc_eval` is the eval-matching node (the genuine Lie-arm linearization, the irreducible
differential-geometric content — the mean-value/Leibniz expansion of the chart Lie-derivative-metric
symbol `½g⁻¹∂` along the realize-tie metric path, read off in the `g₀`-covariant `appCc` form);
`deTurckLieArm_appCc_graded` rides the order-`0` `C⁰` and order-`a` `L²` coefficient controls on top of it
by the fixed-field compactness bound, exactly mirroring the Ricci arm.  Its `(eval)` predicate genuinely
constrains `(L₀, L₁, L₂)` to *reproduce the actual Lie-arm difference value*, so it is non-vacuous: the
zero triple fails it whenever the realized Lie arm is nonzero.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The order-graded `appCc` eval-matching (Lie arm) -/

/-- **The Ricci–DeTurck Lie-arm order-graded `appCc` eval-matching (the genuine Lie-derivative-metric
linearization).**

There exist endpoint-dependent operator coefficient fields
```
L₀ : SmoothCcTensor g₀ 2 2,   L₁ : SmoothCcTensor g₀ 3 2,   L₂ : SmoothCcTensor g₀ 4 2,
```
reproducing the difference of the two realized Lie-derivative-metric arms
`𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁'` (with `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`, `W(g) =
deTurckVF g g_bg`) as the `unitModel`/`appCc` order-graded read-off on the iterated covariant gradients
`Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the perturbation difference `S = T − T'`:
```
(𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁')(v 0, v 1)
  = unitModel g₀ 2 (appCc g₀ 2 2 L₀ W₀ + appCc g₀ 3 2 L₁ W₁ + appCc g₀ 4 2 L₂ W₂) x v.
```

This is the eval-matching half of the grading node `deTurckLieArm_appCc_graded` (the parallel of the
Ricci arm's `deTurckRicciArm_appCc_eval`); its order-`0` `C⁰` and order-`a` `L²` coefficient controls are
proved on top of it by the fixed-field compactness bound.

**The genuine differential-geometric content.**  Writing the chart Lie-derivative-metric symbol
`(𝓛_W g)_{ij} = W^k ∂_k g_{ij} + g_{kj} ∂_i W^k + g_{ik} ∂_j W^k` and `W = deTurckVF g g_bg = g⁻¹·(∇g −
∇g_bg)` (a rational, det-`≠ 0` by `δ < 1`, smooth function of the order-`≤ 1` metric jets), the
mean-value (FTC) expansion of the Lie-arm difference along the realize-tie convex metric path `g_s` is a
finite sum of products of fixed `g₀`-built rational coefficient fields against the order-`≤ 2` covariant
gradients of the perturbation difference `S = T − T'`: the principal `g⁻¹∂²` symbol contributes the
order-`2` slot `L₂` (the genuine `∂²S` of `∂W`), the convective `W^k ∂_k g` and the cross `∂g·∂W` terms
contribute the order-`1` slot `L₁`, and the order-`0` curvature/inverse-Gram-difference multipliers
contribute `L₀`.  Producing the exact endpoint operator fields `(L₀, L₁, L₂)` and the eval-matching
identity is the deep mean-value/Leibniz content of the Lie-arm linearization — the analogue of the Ricci
arm's posited `integratedLinearizedRicci_appCc_eq` (the chart-derivative → intrinsic `appCc` form together
with the operator-field path integration producing the coefficient fields).  It is stated here as the
genuine existential grading node, to be discharged by recursing into the chart-Lie-symbol mean-value
bridges.

**Non-vacuity.**  The `(eval)` predicate genuinely constrains `(L₀, L₁, L₂)` to *reproduce the actual
Lie-arm difference value*, so it is non-vacuous: the zero triple fails it whenever the realized Lie arm is
nonzero (the realization is `ℝ`-linear in `S` and its jets, so it vanishes as `S → 0`, but does NOT vanish
for a genuinely second-order, non-flat perturbation).  Consumers transitively depend on its `sorryAx`. -/
theorem deTurckLieArm_appCc_eval
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        lieDerivMetricClm (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
              (deTurckVF (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
            lieDerivMetricClm (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
              (deTurckVF (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 L₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 L₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 L₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  sorry

/-- **The Ricci–DeTurck Lie-arm order-graded `appCc` decomposition with order-`0` `C⁰` and order-`a`
`L²` coefficient control (genuine grading node — parallel of `deTurckRicciArm_appCc_graded`).**

There exist a constant `Λ ≥ 0` and endpoint-dependent operator coefficient fields
```
L₀ : SmoothCcTensor g₀ 2 2,   L₁ : SmoothCcTensor g₀ 3 2,   L₂ : SmoothCcTensor g₀ 4 2,
```
such that, with `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`:

* **(eval)** the Lie-arm difference `𝓛_{W(g₁)} g₁ − 𝓛_{W(g₁')} g₁'` is the `unitModel`/`appCc`
  order-graded read-off on `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')`;
* **(C⁰ norm)** `rfns(L₀ x) ≤ Λ²`, `rfns(L₁ x) ≤ Λ²`, `rfns(L₂ x) ≤ Λ²` at every base point;
* **(order-`a` `L²` norm)** `rfns((∇₀^a L₀) x) ≤ Λ²`, `rfns((∇₀^a L₁) x) ≤ Λ²`, `rfns((∇₀^a L₂) x) ≤ Λ²`.

Both controls ride on top of the eval-matching `deTurckLieArm_appCc_eval`: the coefficient fields are
fixed smooth compactly-supported tensors with uniform fibre-norm sups on the closed manifold (and so are
their fixed order-`a` covariant gradients) by `exists_bound_riemannianFiberNormSq_smoothCcTensor`.  The
order `a` is supplied as an argument and `Λ` is chosen after it (a single `Λ` cannot bound every covariant
order at once, since a fixed smooth field's covariant-gradient norms grow with the order).  The `(eval)`
predicate genuinely constrains `(L₀, L₁, L₂)` to *reproduce the Lie-arm value*, so it is non-vacuous: it
fails for the zero triple whenever the realized Lie arm is nonzero.

This matches the existential shape of the Ricci-arm grading `deTurckRicciArm_appCc_graded` (same
realize-tie hypotheses, same `unitModel`/`appCc`/`Wₘ` shape), so the `−2·Ric + 𝓛` leaf-identity glue sums
the two graded triples cleanly into the Ricci–DeTurck right-hand-side difference grading. -/
theorem deTurckLieArm_appCc_graded
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Λ : ℝ), 0 ≤ Λ ∧
      ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
        (∀ (x : M) (v : Fin 2 → TangentSpace I x),
          lieDerivMetricClm (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
                (deTurckVF (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
                  (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
              lieDerivMetricClm (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
                (deTurckVF (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
                  (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 L₁
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 L₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ Λ ^ 2) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 2 2 a L₀).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 3 2 a L₁).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 4 2 a L₂).toSection x) ≤ Λ ^ 2) := by
  obtain ⟨L₀, L₁, L₂, heval⟩ :=
    deTurckLieArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 L₀
  obtain ⟨K₁, hK₁_nn, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 2 L₁
  obtain ⟨K₂, hK₂_nn, hK₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 2 L₂
  obtain ⟨J₀, hJ₀_nn, hJ₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + a)
      (iteratedCovGrad (I := I) g₀ 2 2 a L₀)
  obtain ⟨J₁, hJ₁_nn, hJ₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (2 + a)
      (iteratedCovGrad (I := I) g₀ 3 2 a L₁)
  obtain ⟨J₂, hJ₂_nn, hJ₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + a)
      (iteratedCovGrad (I := I) g₀ 4 2 a L₂)
  set Kmax : ℝ := max (max (max K₀ K₁) K₂) (max (max J₀ J₁) J₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax :=
    le_trans hK₀_nn (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine ⟨Real.sqrt Kmax, Real.sqrt_nonneg _, L₀, L₁, L₂, heval, fun x => ?_, fun x => ?_⟩
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hK₀ x) ?_, le_trans (hK₁ x) ?_, le_trans (hK₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hJ₀ x) ?_, le_trans (hJ₁ x) ?_, le_trans (hJ₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
