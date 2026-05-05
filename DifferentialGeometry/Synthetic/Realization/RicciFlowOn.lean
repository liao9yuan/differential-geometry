import DifferentialGeometry.Synthetic.Realization.RicciFlow

/-!
# Subset-time capstone: `concreteRicciFlowBundleOn`

This file is the **subset-time analog** of `RicciFlow.lean`'s
`concreteRicciFlowBundle`. It assembles the full Synthetic `RicciFlowBundle`
on a jointly-smooth time-derivative model restricted to a set `s ⊆ ℝ`
with unique differentiability `hs : UniqueDiffOn ℝ s`.

## Inputs (in addition to `I`, `M`, `s`, `hs`)

* `g_fam : ℝ → ContMDiffRiemannianMetric I ω E (TangentSpace I)` — the
  time-dependent Riemannian metric.
* `h_met` — pointwise smoothness in `t` (subset-time variant).
* `h_ricci_flow` — the Ricci flow PDE, formulated against the subset-time
  `concreteTimeDerivativeDataOn`.
* `h_st` — the subset-time spatial/temporal commutation witness. Unlike the
  global case which uses `concrete_spatial_temporal_comm_general`, the
  subset-time Schwarz argument (via `IsSymmSndFDerivWithinAt` on
  `s ×ˢ Set.range I`) is deferred; the user supplies it directly.

The Levi-Civita connection family, abstract trace, derivation embedding, and
spatial commutation lemmas are all time-independent and reused from the
global infrastructure. The subset-time pieces specific to this file are
`concrete_time_tr_commOn` and `concrete_nabla_time_product_ruleOn`.
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

/-- **The subset-time concrete `RicciFlowBundle`.** Packages every piece of
Realization infrastructure (with the subset-time `concreteTimeDerivativeDataOn`
as the time-algebra layer) into a single `RicciFlowBundle`.

Like the global `concreteRicciFlowBundle`, the only genuinely mathematical
inputs are the metric family, the metric smoothness witness, and the Ricci
flow PDE — except the subset-time spatial/temporal commutation is an
explicit user input (`h_st`) rather than derived from a Schwarz lemma.

Everything else (derivation embedding, abstract trace, Koszul connection,
Levi-Civita, trace commutation, contraction commutation) is time-independent
and reused unchanged from the global layer. -/
noncomputable def concreteRicciFlowBundleOn
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) :
    letI : TimeRegularFam (concreteTimeDerivativeDataOn I M s hs) :=
      concreteTimeRegularFamOn I M s hs
    letI : TimeRegularFam2 (concreteTimeDerivativeDataOn I M s hs) :=
      concreteTimeRegularFam2On I M s hs
    ∀ (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
      (h_met : ∀ (vs : Fin 2 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
          (αs : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
          (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
            (fun τ => ((concreteMetricDuality I M (g_fam τ)).g_tensor :
              TensorData C^∞⟮I, M; ℝ⟯
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ 0 2) vs αs))
      (h_st : SpatialTemporalComm (concreteDerivationEmbedding I M)
        (concreteTimeDerivativeDataOn I M s hs))
      (h_ricci_flow : IsRicciFlow
          (concreteDerivationEmbedding I M)
          (concreteTimeDerivativeDataOn I M s hs)
          (concreteAbstractTrace I M)
          (fun t => concreteMetricDuality I M (g_fam t))
          h_met
          (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))),
    RicciFlowBundle ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ℝ
      (SmoothTimeAlgebraOn I M s) := by
  letI : TimeRegularFam (concreteTimeDerivativeDataOn I M s hs) :=
    concreteTimeRegularFamOn I M s hs
  letI : TimeRegularFam2 (concreteTimeDerivativeDataOn I M s hs) :=
    concreteTimeRegularFam2On I M s hs
  intro g_fam h_met h_st h_ricci_flow
  exact
    { toTimeEvolvingFamilyManifoldData :=
        { emb := concreteDerivationEmbedding I M
          atr := concreteAbstractTrace I M
          td := concreteTimeDerivativeDataOn I M s hs
          g_fam := fun t => concreteMetricDuality I M (g_fam t)
          h_met := h_met
          conn_fam := fun t => concreteConn I M (concreteKoszulCov I M (g_fam t))
          ha_fam := fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t))
          hal_fam := fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t))
          hsl_fam := fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t))
          hl_fam := fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t))
          spatial_temporal_comm := h_st
          time_tr_comm := concrete_time_tr_commOn I M s hs
          nabla_tr_comm := fun t X L => by
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
        concrete_nabla_time_product_ruleOn I M s hs h_st
          (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
          (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t))) }

end
