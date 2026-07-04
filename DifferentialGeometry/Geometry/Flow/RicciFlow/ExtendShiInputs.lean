import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendViaUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartGramUniformContinuity
import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# `ExtendShiInputs` — Shi/Lemma-3.11 inputs for the interior-restart extension route (Brick Y1)

This is the first file where the extension branch (`Evolution.ExtendViaUniqueness`, consumed by
`MaximalTime.extends_of_rmBounded`) imports the HCGCompactness Lemma-3.11 engine
(`AllTimesBounds`/`RicBound`).  The import is cycle-free (HCGCompactness does not depend on the
`CinftyLimitGlue`/`MaximalTime` branch); this file exists to discharge `ricci_flow_interior_restart`'s
`hell` + `hC3` hypotheses from a bounded-curvature solution, reusing Lemma 3.11 instead of the retired
bespoke chart-C³ producer (Brick W).  See `ExtendShiInputs.md` and `Evolution/ChartTailBounds.md`.
-/

set_option linter.unusedSectionVars false

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

-- Two small analysis helpers, ported down from `MaximalTime` (where they are private, above this
-- file) so `ricciFlowPDE_Ici_of_soln` can be stated here; both are self-contained.
private theorem hasDerivWithinAt_Ici_boundary {a b : ℝ} (hab : a < b) (f e : ℝ → ℝ)
    (h_cont : ContinuousOn f (Set.Ico a b))
    (h_e_cont : ContinuousWithinAt e (Set.Ioi a) a)
    (h_int : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun y hy => le_of_lt hy.1
  have h_within : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht => (h_int t ht).mono hsub
  have h_diff : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun t ht => (h_within t ht).differentiableWithinAt
  have h_derivEq : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b) h_diff ?_ ?_ ?_
  · exact (h_cont.continuousWithinAt ⟨le_rfl, hab⟩).mono Set.Ioo_subset_Ico_self
  · exact Ioo_mem_nhdsGT hab
  · exact (h_e_cont.tendsto).congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) h_derivEq).symm

private theorem tensor2_eval_contOn {K : Set ℝ}
    {A : (t : ℝ) → (x : M) →
      Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : ℝ => A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : ℝ // s ∈ K}) (τ := Subtype.val)
    (b := fun _ => x) continuous_subtype_val (fun p => p.2) continuous_const
    (v := fun i _ => vec2 v w i) (fun _ => continuous_const)

/-- **The Ricci-flow metric PDE of a solution, as a one-sided right-derivative on `Ico α ω`.**
Ported down from `MaximalTime.ricciFlowPDE_Ici_of_solution` (which is private and above this file) so
both the `hell` producer here and the Y2 rewiring can consume it. This is exactly Brick X's `hpde`
input for `g_fam := S.base.metric`. Proof route: interior right-derivative from `metricDerivAt` on the
regular times, extended to the closed endpoint `α` by `hasDerivWithinAt_Ici_boundary` using scalar
continuity of the metric and Ricci evaluations. -/
theorem ricciFlowPDE_Ici_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S) :
    ∀ t ∈ Set.Ico alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
  have hinterior : ∀ t ∈ Set.Ioo alpha omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (S.base.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (S.base.metric t) x v w) (Set.Ici alpha) t := by
    intro t ht x v w
    have hval : S.ricciAt t x (vec2 v w) = ricciTensor (I := I) (S.base.metric t) x v w :=
      metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    have h := metricDerivAt (I := I) S hS ⟨t, ht⟩ x v w
    rw [hval] at h
    exact h.hasDerivWithinAt
  have hric_cont : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ico alpha omega) := by
    intro x v w
    refine (tensor2_eval_contOn hS.ricciCont x v w).congr (fun s _ => ?_)
    have e1 : S.ricci s x = metricRicciAt (S.base.metric s) x := by
      simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    rw [e1]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with rfl | hlt
  · refine hasDerivWithinAt_Ici_boundary hαω
      (fun s => (S.base.metric s).inner x v w)
      (fun s => (-2 : ℝ) * ricciTensor (I := I) (S.base.metric s) x v w) ?_ ?_
      (fun s hs => hinterior s hs x v w)
    · refine (tensor2_eval_contOn hS.smoothMetric.metricTensor_cont x v w).congr
        (fun s _ => ?_)
      simp [Tensor0SBundle.metricTensorField_apply, vec2]
    · have hmem : Set.Ico alpha omega ∈ nhdsWithin alpha (Set.Ioi alpha) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT hαω) Set.Ioo_subset_Ico_self
      exact (((hric_cont x v w).continuousWithinAt ⟨le_rfl, hαω⟩).mono_of_mem_nhdsWithin
        hmem).const_mul (-2)
  · exact hinterior t ⟨hlt, ht.2⟩ x v w

/-- **`hell` for `ricci_flow_interior_restart`, from a solution.** A bounded-Ricci solution's metric
stays uniformly equivalent to its initial slice `S.base.metric α` on the tail — exactly (A)'s `hell`
hypothesis. This is the Brick X producer `metricEquiv_of_ricBound` fed by the solution's PDE
(`ricciFlowPDE_Ici_of_soln`); the pointwise Ricci-vs-metric bound `hric` (from `|Ric| ≤ c|Rm|` and the
solution's curvature bound) is the remaining input, taken as a hypothesis here (its discharge from
`Rm04NormSqBoundedAt` is Y2-level curvature algebra). -/
theorem hell_of_soln
    {alpha omega : ℝ} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    {K : ℝ} (hK : 0 ≤ K)
    (hric : ∀ t ∈ Set.Ico alpha omega, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v| ≤ K * (S.base.metric t).inner x v v) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ t₁ ∈ Set.Ico alpha omega, ∀ s ∈ Set.Ico t₁ omega,
      ∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * (S.base.metric alpha).inner x v v ≤ (S.base.metric s).inner x v v ∧
          (S.base.metric s).inner x v v ≤ Λ * (S.base.metric alpha).inner x v v :=
  metricEquiv_of_ricBound (fun t => S.base.metric t) hαω hK
    (ricciFlowPDE_Ici_of_soln hS) hric

/-- **Cauchy–Schwarz for a Riemannian metric's pointwise inner product.**  `(g(u,v))² ≤ g(u,u)·g(v,v)`.
Not available as a Mathlib `InnerProductSpace` fact here (the tangent space's registered inner product is
the ambient one, not `g`), so proved directly from positive-semidefiniteness via the nonnegative
quadratic `t ↦ g(u+tv, u+tv)`. Used for the off-diagonal chart-Gram entry bound (adapter `k = 0`). -/
private theorem metricInnerSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    (g.inner x u v) ^ 2 ≤ g.inner x u u * g.inner x v v := by
  have hnn : ∀ w : TangentSpace I x, 0 ≤ g.inner x w w := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (g.pos x w hw).le
  have hquad : ∀ t : ℝ, 0 ≤ g.inner x u u + 2 * t * g.inner x u v + t ^ 2 * g.inner x v v := by
    intro t
    have h := hnn (u + t • v)
    have hexp : g.inner x (u + t • v) (u + t • v)
        = g.inner x u u + 2 * t * g.inner x u v + t ^ 2 * g.inner x v v := by
      have hsym : g.inner x v u = g.inner x u v := g.symm x v u
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsym]; ring
    rwa [hexp] at h
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hc : 0 < g.inner x v v := g.pos x v hv
    have hval := hquad (-(g.inner x u v) / g.inner x v v)
    have he : g.inner x u u + 2 * (-(g.inner x u v) / g.inner x v v) * g.inner x u v
          + (-(g.inner x u v) / g.inner x v v) ^ 2 * g.inner x v v
        = (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) / g.inner x v v := by
      field_simp; ring
    rw [he] at hval
    have hX : 0 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
      have := mul_nonneg hval hc.le
      rwa [div_mul_cancel₀ _ hc.ne'] at this
    linarith

/-- **Adapter `k = 0` core.**  From metric equivalence `g ≈_C gRef` on `Q` and a bound `M0` on the
`gRef` chart-Gram diagonal entries over `Q`, every chart-Gram entry of `g` is bounded by `C·M0` —
uniformly in `g`.  Diagonal via equivalence + the `gRef` bound; off-diagonal via `metricInnerSq_le`
(Cauchy–Schwarz). -/
private theorem chartGramEntry_le_of_equiv
    (gRef g : SmoothRiemannianMetric I M) {C M0 : ℝ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0) (α₀ : M)
    {Q : Set M} (hequiv : MetricUniformEquivalentOn Q gRef g C)
    (hgRef : ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0)
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ Q) :
    |chartGramMatrix g α₀ x i j| ≤ C * M0 := by
  -- diagonal `g`-quadratics bounded by `C·M0`
  have hdiag : ∀ a : Fin (Module.finrank ℝ E),
      0 ≤ g.inner x (chartBasisVecFiber (I := I) α₀ a x) (chartBasisVecFiber (I := I) α₀ a x) ∧
        g.inner x (chartBasisVecFiber (I := I) α₀ a x) (chartBasisVecFiber (I := I) α₀ a x) ≤ C * M0 := by
    intro a
    set e := chartBasisVecFiber (I := I) α₀ a x with he
    have hnn : 0 ≤ g.inner x e e := by
      rcases eq_or_ne e 0 with he0 | hne
      · rw [he0]; simp
      · exact (g.pos x e hne).le
    refine ⟨hnn, ?_⟩
    have hup : g.inner x e e ≤ C * gRef.inner x e e := (hequiv.2 x hx e).2
    have hg : gRef.inner x e e = chartGramMatrix gRef α₀ x a a :=
      (chartGramMatrix_apply gRef α₀ x a a).symm
    calc g.inner x e e ≤ C * gRef.inner x e e := hup
      _ = C * chartGramMatrix gRef α₀ x a a := by rw [hg]
      _ ≤ C * M0 := by
        apply mul_le_mul_of_nonneg_left (hgRef a x hx) hC0
  -- off-diagonal via Cauchy–Schwarz
  rw [chartGramMatrix_apply]
  set ei := chartBasisVecFiber (I := I) α₀ i x
  set ej := chartBasisVecFiber (I := I) α₀ j x
  have hcs : (g.inner x ei ej) ^ 2 ≤ (C * M0) * (C * M0) := by
    calc (g.inner x ei ej) ^ 2 ≤ g.inner x ei ei * g.inner x ej ej := metricInnerSq_le g x ei ej
      _ ≤ (C * M0) * (C * M0) :=
          mul_le_mul (hdiag i).2 (hdiag j).2 (hdiag j).1 (by positivity)
  have habs : |g.inner x ei ej| ≤ C * M0 := by
    have hCM : (0 : ℝ) ≤ C * M0 := by positivity
    nlinarith [abs_nonneg (g.inner x ei ej), sq_abs (g.inner x ei ej), hcs, hCM]
  exact habs

/-- The fixed reference metric's chart-Gram diagonal entries are uniformly bounded on a compact
`Q ⊆ chartSource` — a single constant `M0` over all diagonal indices (finite sum of the per-index
`chartGramMatrix_entry_isBounded_on_compact` bounds). -/
private theorem exists_gRefDiag_bound (gRef : SmoothRiemannianMetric I M) (α₀ : M)
    {Q : Set M} (hQc : IsCompact Q) (hQs : Q ⊆ (chartAt H α₀).source) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0 := by
  classical
  choose Ci hCi_pos hCi using fun a : Fin (Module.finrank ℝ E) =>
    chartGramMatrix_entry_isBounded_on_compact gRef α₀ a a hQc hQs
  refine ⟨∑ a : Fin (Module.finrank ℝ E), Ci a,
    Finset.sum_nonneg (fun a _ => (hCi_pos a).le), ?_⟩
  intro a b hb
  calc chartGramMatrix gRef α₀ b a a ≤ |chartGramMatrix gRef α₀ b a a| := le_abs_self _
    _ ≤ Ci a := hCi a b hb
    _ ≤ ∑ a' : Fin (Module.finrank ℝ E), Ci a' :=
        Finset.single_le_sum (fun i _ => (hCi_pos i).le) (Finset.mem_univ a)

/-- Goodset points lie in the chart source. -/
private theorem goodSet_subset_chartSource (α₀ : M) :
    chartLeviCivitaGoodSet (I := I) α₀ ⊆ (chartAt H α₀).source :=
  fun _ hz => extChartAt_source I α₀ ▸ hz.1.1

/-- **Adapter k=0 conjunct.**  The 0-th entry bound of `ChartJetBoundAt`, from equivalence + the fixed
`gRef` diagonal bound `M0`: `|chartGramOnE g α₀ i j (extChartAt I α₀ x)| ≤ C·M0` on `Q`. -/
private theorem chartJet0_le_of_equiv
    (gRef g : SmoothRiemannianMetric I M) {C M0 : ℝ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0) (α₀ : M)
    {Q : Set M} (hQ : Q ⊆ chartLeviCivitaGoodSet (I := I) α₀)
    (hequiv : MetricUniformEquivalentOn Q gRef g C)
    (hgRef : ∀ (a : Fin (Module.finrank ℝ E)) (b : M), b ∈ Q →
      chartGramMatrix gRef α₀ b a a ≤ M0)
    (i j : Fin (Module.finrank ℝ E)) {x : M} (hx : x ∈ Q) :
    |Integral.DivergenceTheorem.chartGramOnE (I := I) g α₀ i j (extChartAt I α₀ x)| ≤ C * M0 := by
  have hxsrc : x ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact goodSet_subset_chartSource α₀ (hQ hx)
  have hred : Integral.DivergenceTheorem.chartGramOnE (I := I) g α₀ i j (extChartAt I α₀ x)
      = chartGramMatrix g α₀ x i j := by
    rw [Integral.DivergenceTheorem.chartGramOnE_def, (extChartAt I α₀).left_inv hxsrc]
  rw [hred]
  exact chartGramEntry_le_of_equiv gRef g hC0 hM0 α₀ hequiv hgRef i j hx

end DifferentialGeometry.PDE.RicciFlow
