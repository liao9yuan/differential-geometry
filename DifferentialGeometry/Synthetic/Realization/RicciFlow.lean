import DifferentialGeometry.Synthetic.Realization.KoszulCov
import DifferentialGeometry.Synthetic.Realization.LeviCivita
import DifferentialGeometry.Synthetic.Realization.TimeTrace
import DifferentialGeometry.Synthetic.Realization.NablaComm
import DifferentialGeometry.Synthetic.Realization.NablaContractSynthetic
import DifferentialGeometry.Synthetic.Realization.TimeNabla
import DifferentialGeometry.Synthetic.Assembly

/-!
# P29.4: Final Assembly of `concreteRicciFlowBundle`

This file is the **capstone** of the Realization campaign. It packages every
concrete construction built in `Synthetic/Realization/` into a single term
`concreteRicciFlowBundle`, an instance of the Synthetic-layer record

```
RicciFlowBundle ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, TangentSpace I⟯ ℝ (SmoothTimeAlgebra I M)
```

With this term in hand, every downstream Synthetic theorem about Ricci flow
(Hamilton's evolution equations, monotonicity formulas, etc.) instantly
specializes to a concrete Mathlib smooth manifold, with the Ricci flow PDE as
the *only* remaining mathematical hypothesis.

## Inputs

Besides the ambient manifold `I`, `M`:

* `g_fam : ℝ → ContMDiffRiemannianMetric I ω E (TangentSpace I)` — the
  time-dependent Riemannian metric.
* `h_met` — pointwise smoothness in `t` of `(g_fam t).inner v w`.
* `h_ricci_flow : IsRicciFlow …` — the Ricci flow PDE (`∂_t g = -2 Rc`).

The Levi-Civita connection family is **not** a user input: it is constructed
internally from `g_fam` via `concreteKoszulCov`, which produces the Koszul
covariant derivative of each `g_fam t`. The Mathlib-level smoothness, metric
compatibility, and torsion-freeness of `concreteKoszulCov` are all verified in
`KoszulCov.lean`, so `IsLeviCivita` is automatic.

All other fields (time derivative, derivation embedding, abstract trace,
spatial/temporal commutation, trace/nabla commutation, time product rule) are
derived from the infrastructure proved earlier in the Realization layer.

## Downstream demo

The `example` at the bottom of this file shows that the Levi-Civita property
stored on the concrete bundle can be read off via the bundle's own
`levi_civita` field — without supplying any extra hypotheses.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle SyntheticTensor CovariantDerivative
open TensorContractRealization NablaContractSynthetic KoszulCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **The concrete `RicciFlowBundle`.** Packages every piece of Realization
infrastructure into a single `RicciFlowBundle`, so that the whole Synthetic
Ricci flow theory specialises to Mathlib's concrete smooth-manifold setting.

The only genuinely mathematical inputs are:

* the metric family `g_fam`,
* the metric smoothness witness `h_met`,
* the Ricci flow PDE `h_ricci_flow` (evolution only: `∂_t g = -2 Rc`).

The covariant derivative family is built internally as
`fun t => concreteKoszulCov I M (g_fam t)`, and its Levi-Civita property
follows automatically from `concreteKoszulCov_metric_compat` and
`concreteKoszulCov_torsion_free`. The required smoothness instance
`ContMDiffCovariantDerivative (concreteKoszulCov I M (g_fam t)) ∞` is declared
as a global instance in `KoszulCov.lean` and auto-resolves here.

Everything else — the derivation embedding, the abstract trace, the time
derivative, the spatial/temporal commutation, the trace and tensor-contract
commutation with `∇`, the `∂_t/∇` product rule, the characteristic-≠-2 witness —
comes from the theorems proved earlier in the Realization layer. -/
noncomputable def concreteRicciFlowBundle
    (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_met : ∀ (vs : Fin 2 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (αs : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
        (concreteTimeDerivativeData I M).isSmoothFam
          (fun τ => ((concreteMetricDuality I M (g_fam τ)).g_tensor :
            TensorData C^∞⟮I, M; ℝ⟯
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ 0 2) vs αs))
    (h_ricci_flow : IsRicciFlow
        (concreteDerivationEmbedding I M)
        (concreteTimeDerivativeData I M)
        (concreteAbstractTrace I M)
        (fun t => concreteMetricDuality I M (g_fam t))
        h_met
        (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))) :
    RicciFlowBundle ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ℝ
      (SmoothTimeAlgebra I M) where
  toTimeEvolvingFamilyManifoldData :=
    { emb := concreteDerivationEmbedding I M
      atr := concreteAbstractTrace I M
      td := concreteTimeDerivativeData I M
      g_fam := fun t => concreteMetricDuality I M (g_fam t)
      h_met := h_met
      conn_fam := fun t => concreteConn I M (concreteKoszulCov I M (g_fam t))
      ha_fam := fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t))
      hal_fam := fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t))
      hsl_fam := fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t))
      hl_fam := fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t))
      spatial_temporal_comm := concrete_spatial_temporal_comm_general I M
      time_tr_comm := concrete_time_tr_comm I M
      nabla_tr_comm := fun t X L => by
        -- `concrete_nabla_tr_comm` gives the identity using `concreteTr I M` and
        -- `vectorFieldActionSmooth I M X`. Via the simp lemma `concreteAbstractTrace_tr`
        -- this matches the Synthetic `NablaTrComm` shape; the remaining pieces
        -- (`(emb.embed X)` vs `vectorFieldActionSmooth I M X`) agree definitionally.
        have h := concrete_nabla_tr_comm I M (concreteKoszulCov I M (g_fam t)) X L
        simp only [concreteAbstractTrace_tr]
        exact h
      nabla_contract_comm := fun t =>
        concrete_NablaTensorContractComm I M (concreteKoszulCov I M (g_fam t))
      levi_civita := fun t =>
        concreteIsLeviCivita I M (concreteKoszulCov I M (g_fam t)) (g_fam t)
          (concreteKoszulCov_metric_compat I M (g_fam t))
          (concreteKoszulCov_torsion_free I M (g_fam t)) }
  ricci_flow := h_ricci_flow
  nabla_time_product_rule :=
    concrete_nabla_time_product_rule I M
      (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))

/-- **Downstream demo.** The concrete `RicciFlowBundle` carries a Levi-Civita
connection at every time, supplied automatically by the Koszul construction
without any Levi-Civita input from the user. This showcases that every theorem
proved in the Synthetic Ricci flow library specialises, with no extra work, to
the Mathlib smooth-manifold setting. -/
example
    (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (h_met : ∀ (vs : Fin 2 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (αs : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
        (concreteTimeDerivativeData I M).isSmoothFam
          (fun τ => ((concreteMetricDuality I M (g_fam τ)).g_tensor :
            TensorData C^∞⟮I, M; ℝ⟯
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ 0 2) vs αs))
    (h_ricci_flow : IsRicciFlow
        (concreteDerivationEmbedding I M)
        (concreteTimeDerivativeData I M)
        (concreteAbstractTrace I M)
        (fun t => concreteMetricDuality I M (g_fam t))
        h_met
        (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
        (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t))))
    (t : ℝ) :
    IsLeviCivita
      (concreteRicciFlowBundle I M g_fam h_met h_ricci_flow).emb
      ((concreteRicciFlowBundle I M g_fam h_met h_ricci_flow).conn_fam t)
      ((concreteRicciFlowBundle I M g_fam h_met h_ricci_flow).g_fam t) :=
  (concreteRicciFlowBundle I M g_fam h_met h_ricci_flow).levi_civita t

end
