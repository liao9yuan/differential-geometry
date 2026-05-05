import DifferentialGeometry.Synthetic.Realization.RicciFlow

/-!
# Phase D: `SmoothRicciFlowSolution` — user-facing wrapper

A compact wrapper that reduces the inputs to the concrete Ricci flow bundle to
the three mathematically essential ingredients:
  * `g_fam` — the Riemannian metric family,
  * `g_joint_smooth` — joint `(τ, x)` smoothness in the natural section-pairing
    form `τ ↦ g(τ)(X, Y)`,
  * `ricci_pde` — the Ricci flow equation `∂_t g = -2·Ric`.

`.toBundle` then produces the full `RicciFlowBundle`, from which every
downstream Synthetic theorem about Ricci flow specialises automatically.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle SyntheticTensor CovariantDerivative
open TensorContractRealization NablaContractSynthetic KoszulCov

/-- Helper: convert the natural "joint smoothness of `τ ↦ g(τ)(X, Y)` for all
smooth sections `X, Y`" form to the tensor-form smoothness hypothesis `h_met`
consumed by `IsRicciFlow`. The conversion uses that
`g_tensor vs αs = g ((vs 0)) ((vs 1))` when `vs = ![vs 0, vs 1]` and `αs = ![]`,
which holds for any `Fin 2`/`Fin 0` input. -/
noncomputable def SmoothRicciFlowSolution.g_joint_smooth_to_h_met
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (concreteTimeDerivativeData I M).isSmoothFam
        (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y)) :
    ∀ (vs : Fin 2 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (αs : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
      (concreteTimeDerivativeData I M).isSmoothFam
        (fun τ => ((concreteMetricDuality I M (g_fam τ)).g_tensor :
          TensorData C^∞⟮I, M; ℝ⟯
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ 0 2) vs αs) := by
  intro vs αs
  have h_vs : vs = ![vs 0, vs 1] := by ext i; fin_cases i <;> rfl
  have h_αs : αs = ![] := by ext i; exact i.elim0
  rw [h_vs, h_αs]
  -- `g_tensor ![vs 0, vs 1] ![] = met.g (vs 0) (vs 1)` by definition of `MetricDuality.g`.
  exact g_joint_smooth (vs 0) (vs 1)

/-- A `SmoothRicciFlowSolution` packages the three mathematically essential
ingredients for a Ricci flow on a concrete Mathlib smooth manifold:

* `g_fam` — the time-dependent Riemannian metric family,
* `g_joint_smooth` — the metric's scalar slices are jointly smooth in `(τ, x)`,
  stated in the natural section-pairing form,
* `ricci_pde` — the Ricci flow PDE `∂_t g = −2·Ric` (Levi-Civita is automatic
  from the Koszul construction in `concreteRicciFlowBundle`).

From a `SmoothRicciFlowSolution`, `.toBundle` produces the full
`RicciFlowBundle`, specialising every Synthetic Ricci flow theorem to the
concrete manifold setting. -/
structure SmoothRicciFlowSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] where
  /-- Time-dependent Riemannian metric family. -/
  g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)
  /-- The metric's scalar slices are jointly smooth in `(τ, x)`: for any pair of
  smooth tangent sections `X, Y`, the scalar family `τ ↦ g(τ)(X, Y)` is a
  regular (jointly smooth) time family. -/
  g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    (concreteTimeDerivativeData I M).isSmoothFam
      (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y)
  /-- The Ricci flow PDE: `∂_t g = −2·Ric`. Levi-Civita is automatic from the
  Koszul construction inside `concreteRicciFlowBundle`. -/
  ricci_pde : IsRicciFlow
    (concreteDerivationEmbedding I M)
    (concreteTimeDerivativeData I M)
    (concreteAbstractTrace I M)
    (fun t => concreteMetricDuality I M (g_fam t))
    (SmoothRicciFlowSolution.g_joint_smooth_to_h_met I M g_fam g_joint_smooth)
    (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))

/-- **Produce a full `RicciFlowBundle` from a `SmoothRicciFlowSolution`.**

This is the single function that turns a user's three inputs (metric family,
joint smoothness, PDE) into the full Synthetic `RicciFlowBundle`, from which
every downstream theorem specialises without further work. -/
noncomputable def SmoothRicciFlowSolution.toBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (sol : SmoothRicciFlowSolution I M) :
    RicciFlowBundle ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ℝ
      (SmoothTimeAlgebra I M) :=
  concreteRicciFlowBundle I M sol.g_fam
    (SmoothRicciFlowSolution.g_joint_smooth_to_h_met I M sol.g_fam sol.g_joint_smooth)
    sol.ricci_pde

/-- **End-to-end demo.** From a `SmoothRicciFlowSolution`, the Levi-Civita
property is immediately available at any time — the user never supplies it. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (sol : SmoothRicciFlowSolution I M) (t : ℝ) :
    IsLeviCivita
      (concreteDerivationEmbedding I M)
      (concreteConn I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteMetricDuality I M (sol.g_fam t)) :=
  sol.toBundle.levi_civita t

/-- **Second demo.** The Ricci flow evolution equation `∂_t g = −2·Ric` holds
at every time, read off directly from the solution. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (sol : SmoothRicciFlowSolution I M) (t : ℝ) :
    metric_var_form
      (concreteTimeDerivativeData I M)
      (fun τ => concreteMetricDuality I M (sol.g_fam τ))
      (SmoothRicciFlowSolution.g_joint_smooth_to_h_met I M sol.g_fam sol.g_joint_smooth)
      t =
    (-2 : C^∞⟮I, M; ℝ⟯) • ricciForm_tensor
      (concreteDerivationEmbedding I M)
      (concreteConn I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteConn_add_right I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteConn_add_left I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteConn_smul_left I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteConn_leibniz I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteAbstractTrace I M) :=
  sol.ricci_pde t

end
