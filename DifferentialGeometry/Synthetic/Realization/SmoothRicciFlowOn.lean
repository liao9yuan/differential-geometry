import DifferentialGeometry.Synthetic.Realization.RicciFlowOn
import DifferentialGeometry.Synthetic.Realization.SmoothRicciFlow
import DifferentialGeometry.Synthetic.Realization.SpatialTemporalCommOn

/-!
# Subset-time user-facing wrapper: `SmoothRicciFlowSolutionOn`

This file is the **subset-time analog** of `SmoothRicciFlow.lean`'s
`SmoothRicciFlowSolution`. It reduces the inputs to the subset-time
concrete Ricci flow bundle to four mathematically essential ingredients:

  * `g_fam` — the Riemannian metric family,
  * `g_joint_smooth` — joint `(τ, x)` smoothness on `s ×ˢ M`,
  * `h_st` — the subset-time `SpatialTemporalComm` witness,
  * `ricci_pde` — the Ricci flow equation `∂_t g = -2·Ric` against the
    subset-time time-derivative data.

`.toBundle` then produces the full subset-time `RicciFlowBundle`, from
which every downstream Synthetic theorem about Ricci flow specializes
automatically to the subset-time setting.

The convenience constructor `SmoothRicciFlowSolutionOn.ofClosure` removes
the `h_st` input entirely when the subset `s` additionally satisfies
`s ⊆ closure (interior s)` — a natural regularity condition satisfied by
every `Icc`, `Ioo`, half-open interval, open set, and finite union thereof.
In that case `h_st` is produced by `concrete_spatial_temporal_comm_generalOn`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Bundle SyntheticTensor CovariantDerivative
open TensorContractRealization NablaContractSynthetic KoszulCov

/-- Helper: convert the natural "joint smoothness of `τ ↦ g(τ)(X, Y)` for all
smooth sections `X, Y`" subset-time form into the tensor-form subset-time
smoothness hypothesis consumed by `IsRicciFlow`. Same recipe as
`SmoothRicciFlowSolution.g_joint_smooth_to_h_met`. -/
noncomputable def SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s)
    (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
        (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y)) :
    ∀ (vs : Fin 2 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (αs : Fin 0 → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯),
      (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
        (fun τ => ((concreteMetricDuality I M (g_fam τ)).g_tensor :
          TensorData C^∞⟮I, M; ℝ⟯
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ 0 2) vs αs) := by
  intro vs αs
  have h_vs : vs = ![vs 0, vs 1] := by ext i; fin_cases i <;> rfl
  have h_αs : αs = ![] := by ext i; exact i.elim0
  rw [h_vs, h_αs]
  exact g_joint_smooth (vs 0) (vs 1)

/-- A `SmoothRicciFlowSolutionOn s hs` packages the four essential ingredients
for a Ricci flow on a concrete Mathlib smooth manifold restricted to a set
`s ⊆ ℝ` with unique differentiability `hs`:

* `g_fam` — the time-dependent Riemannian metric family,
* `g_joint_smooth` — joint `(τ, x)` smoothness of the metric's scalar slices,
  stated in section-pairing form against the subset-time predicate,
* `h_st` — the subset-time spatial/temporal commutation witness (required
  because the subset-time Schwarz argument is deferred),
* `ricci_pde` — the Ricci flow PDE, against the subset-time time-derivative
  data.

From a `SmoothRicciFlowSolutionOn`, `.toBundle` produces the full subset-time
`RicciFlowBundle`. -/
structure SmoothRicciFlowSolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) where
  /-- Time-dependent Riemannian metric family. -/
  g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _)
  /-- Joint smoothness of the metric's scalar slices on `s`. -/
  g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
      (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y)
  /-- Subset-time spatial/temporal commutation witness. Deferred from the
  subset-time Schwarz argument. -/
  h_st : SpatialTemporalComm (concreteDerivationEmbedding I M)
    (concreteTimeDerivativeDataOn I M s hs)
  /-- The Ricci flow PDE against the subset-time time-derivative. -/
  ricci_pde : IsRicciFlow
    (concreteDerivationEmbedding I M)
    (concreteTimeDerivativeDataOn I M s hs)
    (concreteAbstractTrace I M)
    (fun t => concreteMetricDuality I M (g_fam t))
    (SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met I M s hs g_fam g_joint_smooth)
    (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
    (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))

/-- **Produce a full subset-time `RicciFlowBundle` from a
`SmoothRicciFlowSolutionOn`.** -/
noncomputable def SmoothRicciFlowSolutionOn.toBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {s : Set ℝ} {hs : UniqueDiffOn ℝ s}
    (sol : SmoothRicciFlowSolutionOn I M s hs) :
    RicciFlowBundle ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ ℝ
      (SmoothTimeAlgebraOn I M s) :=
  concreteRicciFlowBundleOn I M s hs sol.g_fam
    (SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met I M s hs
      sol.g_fam sol.g_joint_smooth)
    sol.h_st sol.ricci_pde

/-- **End-to-end demo.** From a `SmoothRicciFlowSolutionOn`, the Levi-Civita
property is immediately available at any time — the user never supplies it. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {s : Set ℝ} {hs : UniqueDiffOn ℝ s}
    (sol : SmoothRicciFlowSolutionOn I M s hs) (t : ℝ) :
    IsLeviCivita
      (concreteDerivationEmbedding I M)
      (concreteConn I M (concreteKoszulCov I M (sol.g_fam t)))
      (concreteMetricDuality I M (sol.g_fam t)) :=
  sol.toBundle.levi_civita t

/-- **Second demo.** The Ricci flow evolution equation `∂_t g = -2·Ric` against
the subset-time time-derivative is available at every time. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    {s : Set ℝ} {hs : UniqueDiffOn ℝ s}
    (sol : SmoothRicciFlowSolutionOn I M s hs) (t : ℝ) :
    metric_var_form
      (concreteTimeDerivativeDataOn I M s hs)
      (fun τ => concreteMetricDuality I M (sol.g_fam τ))
      (SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met I M s hs
        sol.g_fam sol.g_joint_smooth)
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

/-- **Convenience constructor.** Build a `SmoothRicciFlowSolutionOn` from
the three mathematically essential ingredients — `g_fam`, `g_joint_smooth`,
`ricci_pde` — plus the topological regularity hypothesis
`h_closure : s ⊆ closure (interior s)`. The subset-time spatial/temporal
commutation witness `h_st` is produced automatically by
`concrete_spatial_temporal_comm_generalOn`.

To discharge `h_closure` in common cases, use the following Mathlib lemmas:
* **Open sets:** `hs_open.interior_eq ▸ subset_closure`
  (`IsOpen.interior_eq` + `subset_closure`).
* **`Ioo a b`:** `Ioo_subset_closure_interior` (from `Topology.Order.OrderClosed`).
* **`Ico a b`, `Ioc a b`:** `Ico_subset_closure_interior`,
  `Ioc_subset_closure_interior` (from `Topology.Order.DenselyOrdered`).
* **`Icc a b` with `a < b`:** combine `closure_Ioo` and `interior_Icc` —
  `Ioo a b ⊆ Icc a b = closure (Ioo a b) = closure (interior (Icc a b))`. -/
noncomputable def SmoothRicciFlowSolutionOn.ofClosure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) (h_closure : s ⊆ closure (interior s))
    (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
    (g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
        (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y))
    (ricci_pde : IsRicciFlow
      (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeDataOn I M s hs)
      (concreteAbstractTrace I M)
      (fun t => concreteMetricDuality I M (g_fam t))
      (SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met I M s hs g_fam g_joint_smooth)
      (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))) :
    SmoothRicciFlowSolutionOn I M s hs where
  g_fam := g_fam
  g_joint_smooth := g_joint_smooth
  h_st := concrete_spatial_temporal_comm_generalOn I M hs h_closure
  ricci_pde := ricci_pde

section OfClosureDemo

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  {s : Set ℝ} {hs : UniqueDiffOn ℝ s} (h_closure : s ⊆ closure (interior s))
  (g_fam : ℝ → Bundle.ContMDiffRiemannianMetric I ω E (TangentSpace I : M → Type _))
  (g_joint_smooth : ∀ (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    (concreteTimeDerivativeDataOn I M s hs).isSmoothFam
      (fun τ => (concreteMetricDuality I M (g_fam τ)).g X Y))

/-- **End-to-end demo via `ofClosure`.** The user supplies only three
mathematical ingredients plus `h_closure`; `h_st` is derived automatically.
The ambient typeclass context and subset data are factored into the enclosing
`section`/`variable` block, so this signature mirrors `IsRicciFlow`'s
PDE parameters only. -/
example
    (ricci_pde : IsRicciFlow
      (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeDataOn I M s hs)
      (concreteAbstractTrace I M)
      (fun t => concreteMetricDuality I M (g_fam t))
      (SmoothRicciFlowSolutionOn.g_joint_smooth_to_h_met I M s hs g_fam g_joint_smooth)
      (fun t => concreteConn I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_add_right I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_add_left I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_smul_left I M (concreteKoszulCov I M (g_fam t)))
      (fun t => concreteConn_leibniz I M (concreteKoszulCov I M (g_fam t)))) (t : ℝ) :
    IsLeviCivita
      (concreteDerivationEmbedding I M)
      (concreteConn I M (concreteKoszulCov I M (g_fam t)))
      (concreteMetricDuality I M (g_fam t)) :=
  (SmoothRicciFlowSolutionOn.ofClosure I M s hs h_closure g_fam g_joint_smooth
    ricci_pde).toBundle.levi_civita t

end OfClosureDemo

end
