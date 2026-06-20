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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Linearity of the unit read-off and the operator-field action (mechanical) -/

/-- The unit read-off `unitModel` is additive in the `(0, s)`-tensor argument: `unitModel (S + S') =
unitModel S + unitModel S'`.  Re-derived locally (the `RicciDeTurckRicciArm` version is `private`). -/
private lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

/-- The unit read-off `unitModel` is subtractive in the `(0, s)`-tensor argument: `unitModel (S − S') =
unitModel S − unitModel S'`.  Re-derived locally (the `RicciDeTurckRicciArm` version is `private`). -/
private lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_sub]

/-- The operator-field action `appCc` is subtractive in the operator-field (coefficient) factor:
`appCc (Φ − Ψ) W = appCc Φ W − appCc Ψ W`.  Mirrors the on-disk `appCc_add_left`. -/
private theorem appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Ψ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ - Ψ) W =
      appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ W - appCc (I := I) (M := M) g r s Ψ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ W).toSection x
        - (appCc (I := I) (M := M) g r s Ψ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ - Ψ).toSection x : TensorRSSpace r s I x) = Φ.toSection x - Ψ.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

/-- The unit read-off `unitModel` is `ℝ`-homogeneous in the `(0, s)`-tensor argument:
`unitModel (c • S) = c • unitModel S`.  Re-derived locally (the `RicciDeTurckRicciArm` version is
`private`). -/
private lemma unitModel_smul_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (W : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • W) x =
      c • unitModel (I := I) (M := M) g s W x := by
  rw [unitModel, unitModel]
  have hsec : (c • W).toSection x = c • W.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • W).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_smul]

/-- The operator-field action `appCc` is `ℝ`-homogeneous in the operator-field (coefficient) factor:
`appCc (c • Φ) W = c • appCc Φ W`.  Re-derived locally (the `RicciDeTurckRicciArm` version is
`private`). -/
private theorem appCc_smul_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in
/-- Joint `(s, x)`-smoothness of the constant `ℝ`-scaling of a jointly-smooth `(r, s)`-operator family.
A local copy of the `RicciDeTurckRicciArm` private combinator `jointRSsmul`, needed here to scale the
unscaled bare three-slot coefficient families by `(-2)`. -/
private theorem jointRSsmul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

/-- **The per-arm `unitModel`/`appCc` read-off is continuous in `s` whenever the model-fibre value of
the coefficient family is.**  Re-derived locally (the `RicciDeTurckRicciArm` version is `private`):
the scalar read-off `s ↦ unitModel g₀ 2 (appCc g₀ r 2 (Ψ s) W) x v` factors through the fixed
continuous-linear chain `T ↦ ((T) (toModel u)) v` applied to the model-fibre value
`toModel ((Ψ s).toSection x)` (where `u = (W x) unit`), via `toModel_tensorRS_apply`. -/
private theorem appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r) {S : Set ℝ}
    {x : M} (hΨ : ContinuousOn (fun s : ℝ => TensorRSSpace.toModel ((Ψ s).toSection x)) S)
    (v : Fin 2 → TangentSpace I x) :
    ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v) S := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have key : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v =
        ((TensorRSSpace.toModel ((Ψ s).toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Ψ s).toSection x) u]
  have hchain : Continuous (fun T : Tensor0SBundle.TensorRSModel r 2 ℝ E =>
      (T (Tensor0SBundle.Tensor0SSpace.toModel u)) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp
      (ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (Tensor0SBundle.Tensor0SSpace.toModel u)).continuous
  exact (hchain.comp_continuousOn hΨ).congr (fun s _ => (key s).symm)

/-! ## The pure `−2 Ric`-arm order-graded `appCc` eval-matching (posited deep mean-value input) -/

/-- **The re-basing of the bare realized chart-Ricci `s`-derivative at an interior parameter.**

For the realized metric path `g_s = realizedFam g₀ T T' s` and every interior parameter `s ∈ (0,1)`,
the `s`-derivative of the bare realized chart-Ricci sum `deriv (realizedRicciChartSum) s` equals the
`chartModelBasis`-trace read-off, at the re-base metric `g_s`, of the on-disk **bare** chart-Ricci
`s`-derivative split `chartRicciSecondOrderPart g_s h + ricciDerivFirstOrderRemainder g_s h`, where `h`
is the section-difference chart velocity (`IsRealizedChartVelocity`).

This is the **bare-Ricci** analogue of the combined re-basing
`deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol`: it reuses the very same cutoff
metric-perturbation family `exists_rebased_cutoffMetricPerturbationFamily` (whose third output is the
bare-Ricci base-point locality `_hlocRic` for `chartRicciTensor`), the bare metric-family
chart-linearization keystone `hasDerivAt_chartRicciTensor` (which computes the `σ`-derivative at
`σ = 0` of `σ ↦ chartRicciTensor (gfam σ) x i k y` for the cutoff family, giving
`chartRicciSecondOrderPart g_s h + ricciDerivFirstOrderRemainder g_s h`), the bare-Ricci base-point
locality to transfer (`HasDerivAt.congr_of_eventuallyEq`) to the re-based realized family, and the
translation invariance of the derivative (`HasDerivAt.comp_sub_const`) to re-base from `σ = 0` of the
translated family to `s`.  All pieces are on disk and sorry-free; this lemma mirrors the combined
keystone with `chartRicciTensor` in place of `chartFComponentOnE (deTurckRicciRHS g_bg)`. -/
private theorem deriv_realizedRicciChartSum_eq_rebased_chartSymbol
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    ∃ h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E,
      IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
            (I := I) g₀ T T' hδ hδ' x v w) s =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
              (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart (I := I)
                  (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                    (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                  (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                    (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x)) := by
  classical
  -- The cutoff metric-perturbation family of `g_s`, its velocity-pin, and its bare-Ricci locality.
  obtain ⟨h, gfam, hfam, hvel, hlocRic, _hloc⟩ :=
    exists_rebased_cutoffMetricPerturbationFamily (I := I) g₀ g₀ T T' hδ_lt hδ hδ'_lt hδ' hs x
  refine ⟨h, hvel, ?_⟩
  set gs : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  set y₀ : E := extChartAt I x x with hy₀
  have hy : y₀ ∈ interior (extChartAt I x).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  set Pval : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart (I := I)
        gs x h i k y₀ +
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
        (I := I) gs x h i k y₀ with hPval
  -- Per-summand: `t ↦ chartRicciTensor (realizedFam t) x i k y₀` has, at `s`, the bare chart-Ricci split.
  have hper : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
          x i k y₀)
        (Pval i k) s := by
    intro i k
    -- The bare chart-Ricci `σ`-derivative split at `σ = 0` for the cutoff family `gfam` of `g_s`.
    have hsplit : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (gfam σ) x i k y₀) (Pval i k) 0 := by
      rw [hPval, hgs]
      exact DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.hasDerivAt_chartRicciTensor
        (I := I) hfam i k hy
    -- Transfer to the re-based realized family by the family's base-point bare-Ricci locality.
    have htrans : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + σ))
          x i k y₀)
        (Pval i k) 0 :=
      hsplit.congr_of_eventuallyEq (hlocRic i k).symm
    have htrans' : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + σ))
          x i k y₀)
        (Pval i k) (s - s) := by
      rwa [sub_self]
    have hsub := htrans'.comp_sub_const s s
    have hcongr : (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' (s + (t - s)))
          x i k y₀) =
        (fun t : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
          x i k y₀) := by
      funext t; rw [add_sub_cancel]
    rwa [hcongr] at hsub
  -- Differentiate the bare chart sum term by term, then read off the derivative.
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
            x i k y₀)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i * (Pval i k)) s := by
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact (hper i k).const_mul _
  have hfun : DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
        (I := I) g₀ T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor (I := I)
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam (I := I) g₀ T T' hδ hδ' t)
            x i k y₀) := by
    funext t
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum, hy₀]
  rw [hfun]
  exact hsum.deriv

/-- **(Posited single irreducible bare-Ricci chart→covariant transfer — the per-`s` three-slot
`appCc` read-off of the UNSCALED bare chart-Ricci symbol.)**

For the realized metric path `g_s = realizedFam g₀ T T' s`, there are order-graded coefficient families
```
Q₀fib : ℝ → SmoothCcTensor g₀ 2 2,  Q₁fib : ℝ → SmoothCcTensor g₀ 3 2,  Q₂fib : ℝ → SmoothCcTensor g₀ 4 2,
```
such that, at every interior parameter `s ∈ (0,1)` and every realized chart velocity `h`
(`IsRealizedChartVelocity`), the UNSCALED bare chart-Ricci-symbol read-off
`∑ᵢₖ repr·repr·(chartRicciSecondOrderPart g_s h + ricciDerivFirstOrderRemainder g_s h)` is the three-slot
`unitModel`/`appCc` read-off of `(Q₀fib s, Q₁fib s, Q₂fib s)` on the iterated covariant gradients
`Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')`; the per-slot read-offs are jointly `(s, x)`-smooth on the slab
`univ ×ˢ realizedSmallSet` and continuous in `s` on `realizedSmallSet`.

This is the **single irreducible covariant content** of the bare-Ricci chart → intrinsic transfer, the
bare-Ricci mirror of the combined `rebased_chartSymbol_eq_appCc_pointwise` (`RicciDeTurckRicciArm`).
Its genuine differential-geometric core is the bare three-slot covariant Lichnerowicz bridge: the bare
chart Ricci principal symbol `ricciSymbolComp_eq_closedForm` splits into the order-`2` rough Laplacian
`−½|ξ|² h` (slot `Q₂`), the **two order-`1` divergence terms** `½ξᵢ(ξh)ₖ + ½ξₖ(ξh)ᵢ` (slot `Q₁`, the
gauge terms that the combined chart symbol cancels but the bare symbol keeps), and the order-`0`
trace term `−½ξᵢξₖ tr h` plus the curvature remainder (slot `Q₀`), each transferred from the chart
trace to the intrinsic `∇₀`-covariant `appCc` form.  Unlike the combined arm, the bare symbol has NO
gauge cancellation, so the order-`1` slot `Q₁` is GENUINELY NONZERO and there is no on-disk order-`1`
covariant read-off bridge (`chartCovariantFirstGrad_partialDeriv_form`) to reuse; this bare three-slot
transfer is therefore irreducible here and posited as the lone sorry-child, to be recursed into
downstream via the bare order-`1` covariant divergence read-off.  The `(-2)`-scaling that the
consumer `exists_negTwoRicciArm_chartSymbolSum_appCc_families` needs is NOT part of this transfer: it is
discharged separately by the consumer pushing the scalar `(-2)` through the `appCc`/`unitModel`
multilinear read-off.  The predicate genuinely constrains the families to reproduce the bare
chart-Ricci-symbol value, so it is non-vacuous: the zero families fail it on any background where the
bare chart Ricci symbol is nonzero. -/
private theorem bareChartRicci_threeSlot_appCc_covariantTransfer
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Q₀fib : ℝ → SmoothCcTensor g₀ 2 2) (Q₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (Q₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x)
          (h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E),
          IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                  DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Q₀fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Q₁fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Q₂fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 ((Q₀fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 ((Q₁fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 ((Q₂fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₀fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₁fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Q₂fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) :=
  sorry

/-- **(Posited deep bare-Ricci input — the per-`s` three-slot Lichnerowicz `appCc` read-off of the bare
chart-Ricci symbol, with order-graded `(-2)`-scaled coefficient families and their path-integration
controls.)**

For the realized metric path `g_s = realizedFam g₀ T T' s`, there are order-graded `(-2)`-scaled
coefficient families
```
P₀fib : ℝ → SmoothCcTensor g₀ 2 2,  P₁fib : ℝ → SmoothCcTensor g₀ 3 2,  P₂fib : ℝ → SmoothCcTensor g₀ 4 2,
```
such that, at every interior parameter `s ∈ (0,1)` and every realized chart velocity `h`
(`IsRealizedChartVelocity`), the `(-2)`-scaled bare chart-Ricci-symbol read-off
`(-2)·∑ᵢₖ repr·repr·(chartRicciSecondOrderPart g_s h + ricciDerivFirstOrderRemainder g_s h)` is the
three-slot `unitModel`/`appCc` read-off of `(P₀fib s, P₁fib s, P₂fib s)` on the iterated covariant
gradients `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')`; the per-slot read-offs are jointly `(s, x)`-smooth
on the slab `univ ×ˢ realizedSmallSet` (the `hjoint*` controls, consumed by `exists_pathIntegralCoeffField`)
and continuous in `s` on `realizedSmallSet` (the `hcont*` slices).

This `(-2)`-scaled packaging is now assembled on disk from the single irreducible chart→covariant
transfer `bareChartRicci_threeSlot_appCc_covariantTransfer` (the UNSCALED three-slot read-off plus the
joint smoothness/continuity of its coefficient families): the `(-2)`-scaling is pushed through the
`appCc`/`unitModel` multilinear read-off (`appCc_smul_local`/`unitModel_smul_local`), and the joint
smoothness/continuity of the `(-2)`-scaled families follow from the unscaled controls by the
`(-2)`-`smul` smoothness combinator (`jointRSsmul_local`) and the model-fibre `smul` continuity.  The
genuine differential-geometric content remains the bare three-slot covariant Lichnerowicz bridge —
the order-`2` rough Laplacian (slot `P₂`), the **two order-`1` divergence terms** `½ξᵢ(ξh)ₖ + ½ξₖ(ξh)ᵢ`
(slot `P₁`, the gauge terms that the combined chart symbol cancels but the bare symbol keeps), and the
order-`0` trace plus curvature remainder (slot `P₀`) — which is the lone sorry-child
`bareChartRicci_threeSlot_appCc_covariantTransfer`.  The predicate genuinely constrains the families to
reproduce the bare chart-Ricci-symbol value, so it is non-vacuous: the zero families fail it on any
background where the bare chart Ricci symbol is nonzero. -/
private theorem exists_negTwoRicciArm_chartSymbolSum_appCc_families
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀fib : ℝ → SmoothCcTensor g₀ 2 2) (P₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (P₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x)
          (h : DifferentialGeometry.PDE.DeTurck.RicciLinearization.ChartMetricPerturbation E),
          IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
          ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                  DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                      (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (P₁fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (P₂fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 ((P₀fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 ((P₁fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 ((P₂fib p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₀fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₁fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
      (∀ x : M, ContinuousOn
        (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((P₂fib t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ'))) := by
  classical
  -- The single irreducible UNSCALED bare three-slot chart→covariant transfer: its coefficient families
  -- `Q₀/Q₁/Q₂` together with the unscaled per-`s` value identity and their joint smoothness/continuity.
  obtain ⟨Q₀fib, Q₁fib, Q₂fib, hQval, hQj₀, hQj₁, hQj₂, hQc₀, hQc₁, hQc₂⟩ :=
    bareChartRicci_threeSlot_appCc_covariantTransfer (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  -- The `(-2)`-scaled families are the constant-`smul` of the unscaled ones.
  refine ⟨fun s => (-2 : ℝ) • Q₀fib s, fun s => (-2 : ℝ) • Q₁fib s, fun s => (-2 : ℝ) • Q₂fib s,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Value identity: push the scalar `(-2)` through the `appCc`/`unitModel` multilinear read-off and
    -- apply the unscaled transfer identity `hQval`.
    intro s hs x v h hvel
    rw [show ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
        (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (Q₀fib s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 (Q₁fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 (Q₂fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v from by
      rw [hQval s hs x v h hvel]]
    -- LHS: `-2 * unitModel(appCc Q₀ W₀ + appCc Q₁ W₁ + appCc Q₂ W₂) x v` → `-2 * (u₀ + u₁ + u₂)`.
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
    -- RHS: replace each `appCc ((-2)•Qₖ) Wₖ` by `(-2)•(appCc Qₖ Wₖ)`, then distribute `unitModel`.
    rw [show (fun (s : ℝ) => (-2 : ℝ) • Q₀fib s) s = (-2 : ℝ) • Q₀fib s from rfl,
      show (fun (s : ℝ) => (-2 : ℝ) • Q₁fib s) s = (-2 : ℝ) • Q₁fib s from rfl,
      show (fun (s : ℝ) => (-2 : ℝ) • Q₂fib s) s = (-2 : ℝ) • Q₂fib s from rfl,
      appCc_smul_local, appCc_smul_local, appCc_smul_local,
      unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply,
      unitModel_smul_local, unitModel_smul_local, unitModel_smul_local]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  · -- Joint smoothness of `(-2)•Q₀`.
    exact jointRSsmul_local (r := 2) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₀fib p.2).toSection p.1) hQj₀
  · -- Joint smoothness of `(-2)•Q₁`.
    exact jointRSsmul_local (r := 3) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₁fib p.2).toSection p.1) hQj₁
  · -- Joint smoothness of `(-2)•Q₂`.
    exact jointRSsmul_local (r := 4) (s := 2) (-2 : ℝ)
      (fun p : M × ℝ => (Q₂fib p.2).toSection p.1) hQj₂
  · -- Continuity of `(-2)•Q₀`: a constant `smul` of the unscaled continuity slice.
    intro x
    refine ((hQc₀ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]
  · -- Continuity of `(-2)•Q₁`.
    intro x
    refine ((hQc₁ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]
  · -- Continuity of `(-2)•Q₂`.
    intro x
    refine ((hQc₂ x).const_smul (-2 : ℝ)).congr (fun t _ => ?_)
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SBundle.TensorRSSpace.toModel_smul]

private theorem integratedLinearizedRicci_negTwo_chartSum_appCc_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ∫ s in (0 : ℝ)..1,
              deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
                (I := I) g₀ T T' hδ hδ' x (v 0) (v 1)) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The posited bare three-slot families (covariant bridge + coefficient families + joint smoothness).
  obtain ⟨P₀fib, P₁fib, P₂fib, hpt, hj₀, hj₁, hj₂, hc₀, hc₁, hc₂⟩ :=
    exists_negTwoRicciArm_chartSymbolSum_appCc_families (I := I) (M := M) g₀ T T'
      hδ_lt hδ hδ'_lt hδ'
  -- The open slab membership data for the path-integral coefficient fields.
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have hIccS : Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSI : Set.uIcc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]; exact hIccS
  -- The three integrated coefficient fields are the fibre path integrals of the families.
  obtain ⟨IΦ₀, heval₀⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 2 P₀fib
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₀ hc₀
  obtain ⟨IΦ₁, heval₁⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 3 P₁fib
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₁ hc₁
  obtain ⟨IΦ₂, heval₂⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 4 P₂fib
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj₂ hc₂
  refine ⟨IΦ₀, IΦ₁, IΦ₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
  -- Distribute `unitModel` over the three-`appCc` sum, evaluated at `v`.
  have hrhs :
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀
            + appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁
            + appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v := by
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
  rw [hrhs]
  -- The three per-term path-integral swaps.
  rw [heval₀ x v, heval₁ x v, heval₂ x v]
  -- The `(-2)`-scaled integral of the chart-Ricci derivative splits into the three per-slot read-offs
  -- integrated, via the per-`s` covariant bridge `hpt` composed with the re-basing keystone.
  -- First, pull the `(-2)` scalar inside the interval integral.
  rw [← intervalIntegral.integral_const_mul]
  -- Replace the per-slot integrals by a single integral of their sum (interval-integrability from the
  -- continuity slices), then match integrands a.e. on `Ι 0 1 = Ioc 0 1`.
  have hii₀ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s) W₀) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 2 P₀fib W₀
      (hc₀ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  have hii₁ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (P₁fib s) W₁) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 3 P₁fib W₁
      (hc₁ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  have hii₂ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (P₂fib s) W₂) x v)
      MeasureTheory.volume 0 1 :=
    (appCc_unitModel_read_continuousOn_of_toModel_continuousOn_local (I := I) (M := M) g₀ 4 P₂fib W₂
      (hc₂ x) v |>.mono hIccS).intervalIntegrable_of_Icc zero_le_one
  rw [← intervalIntegral.integral_add hii₀ hii₁, ← intervalIntegral.integral_add
    (hii₀.add hii₁) hii₂]
  -- Match the integrands a.e.: on the interior `Ioo 0 1` the integrand equals the `(-2)`-scaled
  -- chart-derivative by re-basing + the per-`s` covariant bridge `hpt`; the bad set `⊆ {1}` is null.
  refine intervalIntegral.integral_congr_ae ?_
  refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
    (MeasureTheory.measure_singleton 1)
  rw [Set.mem_singleton_iff]
  by_contra hne1
  apply hs
  intro hsmem
  rw [Set.mem_uIoc] at hsmem
  rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
  · -- `s ∈ Ioo 0 1`: re-base the chart-derivative, then apply the per-`s` covariant bridge.
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs0, lt_of_le_of_ne hs1 hne1⟩
    obtain ⟨h, hvel, hderiv⟩ :=
      deriv_realizedRicciChartSum_eq_rebased_chartSymbol (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        hsIoo x (v 0) (v 1)
    rw [hderiv]
    -- `hpt` is the per-`s` three-slot covariant bridge for the realized chart velocity `h`.
    rw [show ((-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
            (DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciSecondOrderPart
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.ricciDerivFirstOrderRemainder
                (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
                  (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x))) =
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (P₀fib s) W₀
              + appCc (I := I) (M := M) g₀ 3 2 (P₁fib s) W₁
              + appCc (I := I) (M := M) g₀ 4 2 (P₂fib s) W₂) x v from
      hpt s hsIoo x v h hvel]
    rw [unitModel_add_local, unitModel_add_local, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.add_apply]
  · exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)

/-- **(Posited deep input — the pure `(−2)`-scaled integrated linearized-Ricci operator in
order-graded `appCc` form.)**

For the convex realized metric path `g_s = realize(g₀, (1 − s)·T' + s·T)`, the `(−2)`-scaled
`s`-integral over `[0,1]` of the bare linearized Ricci integrand `linearizedRicciAt g_s (T − T')`
(the integrand of the bare-Ricci mean-value reduction
`ricciTensor_realized_sub_eq_integral_linearizedRicci`) is the order-graded `unitModel`/`appCc`
read-off on the iterated covariant gradients `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the
perturbation difference `S = T − T'`:
```
(−2)·∫₀¹ DRic(g_s)[T − T']_x(v 0, v 1) ds
  = unitModel g₀ 2 (appCc g₀ 2 2 P₀ W₀ + appCc g₀ 3 2 P₁ W₁ + appCc g₀ 4 2 P₂ W₂) x v.
```

This is the **bare-Ricci** analogue of the combined-operator integrated Lichnerowicz form
`integratedLinearizedRicci_appCc_eq` (whose integrand is the COMBINED chart-sum derivative
`deriv (realizedDeTurckRicciChartSum …)`, i.e. `−2 Ric + 𝓛_W` AFTER the DeTurck gauge cancellation,
hence has no genuine order-`1` slot).  Here the integrand is the **bare** linearized Ricci
`linearizedRicciAt` (equivalently `deriv (realizedRicciChartSum …)` on `(0,1)` by
`linearizedRicciAt_eq_deriv_chartSum_on_Ioo`), which keeps its genuine order-`1` connection-coupling
slot `P₁` (the gauge terms that the combined chart symbol cancels survive in the bare Ricci symbol).

**The genuine differential-geometric content.**  The bare-Ricci Lichnerowicz decomposition of the
chart Ricci symbol — the pointwise-in-`s` `appCc` form of `DRic(g_s)` reading off the order-`0`
curvature multiplier `P₀`, the order-`1` connection-coupling multiplier `P₁`, and the order-`2`
rough-Laplacian principal `P₂` — together with the operator-field path integration producing the
exact endpoint coefficient fields `(P₀, P₁, P₂)` as smooth compactly-supported tensors (the path
metric `g_s` stays `g₀`-fibre small with constant `< 1` on `[0,1]`, so the coefficient families are
jointly `(s, x)`-smooth and their fibre Bochner path integrals are again smooth fields).  This is the
bare-Ricci mirror of the combined chart-symbol → intrinsic `appCc` tower
(`deriv_realizedDeTurckRicciChartSum_eq_appCc_pointwise` + `exists_pathIntegralCoeffField`), recursed
into downstream.  It is *posited* here as the single deferred bare-Ricci input.  The predicate
genuinely constrains `(P₀, P₁, P₂)` to *reproduce the actual `(−2)`-scaled integrated bare linearized
Ricci value*, so it is non-vacuous: the zero triple fails it on any background where the integrated
linearized Ricci is nonzero. -/
private theorem integratedLinearizedRicci_negTwo_appCc_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ∫ s in (0 : ℝ)..1,
              DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt (I := I)
                g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The bare chart-sum integral form supplies the order-graded coefficient fields `(P₀, P₁, P₂)`.
  obtain ⟨P₀, P₁, P₂, heq⟩ :=
    integratedLinearizedRicci_negTwo_chartSum_appCc_eq (I := I) (M := M) g₀ T T'
      hδ_lt hδ hδ'_lt hδ'
  refine ⟨P₀, P₁, P₂, fun x v => ?_⟩
  -- The bare linearized-Ricci integrand `linearizedRicciAt` agrees with the bare chart-Ricci
  -- `s`-derivative `deriv (realizedRicciChartSum)` on the interior `(0,1)`
  -- (`linearizedRicciAt_eq_deriv_chartSum_on_Ioo`), which differs from `Ι 0 1 = Ioc 0 1` only on the
  -- volume-null set `{1}`, so the two `s`-integrals over `[0,1]` are equal.
  have hint : (∫ s in (0 : ℝ)..1,
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt (I := I)
          g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s) =
      ∫ s in (0 : ℝ)..1,
        deriv (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedRicciChartSum
          (I := I) g₀ T T' hδ hδ' x (v 0) (v 1)) s := by
    refine intervalIntegral.integral_congr_ae ?_
    refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
      (MeasureTheory.measure_singleton 1)
    rw [Set.mem_singleton_iff]
    by_contra hne1
    apply hs
    intro hsmem
    rw [Set.mem_uIoc] at hsmem
    rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
    · exact DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_eq_deriv_chartSum_on_Ioo
        (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) ⟨hs0, lt_of_le_of_ne hs1 hne1⟩
    · exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)
  rw [hint]
  exact heq x v

/-- **(Posited deep input — the pure `(−2)·Ric`-arm order-graded `appCc` eval-matching.)**

There exist endpoint-dependent operator coefficient fields
```
P₀ : SmoothCcTensor g₀ 2 2,   P₁ : SmoothCcTensor g₀ 3 2,   P₂ : SmoothCcTensor g₀ 4 2,
```
reproducing the `(−2)`-scaled difference of the two *pure* realized Ricci tensors
`(−2)·Ric(g₁) − (−2)·Ric(g₁')` (with `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`, both metrics in
the `∞`-aliased form `smoothRiemannianMetricToInfty (tensorSectionRealizeMetric …)` consumed by
`ricciTensor`) as the `unitModel`/`appCc` order-graded read-off on the iterated covariant gradients
`Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the perturbation difference `S = T − T'`:
```
((−2)·Ric(g₁) − (−2)·Ric(g₁'))(v 0, v 1)
  = unitModel g₀ 2 (appCc g₀ 2 2 P₀ W₀ + appCc g₀ 3 2 P₁ W₁ + appCc g₀ 4 2 P₂ W₂) x v.
```

This is the pure-curvature-arm analogue of the combined-operator eval-matching
`deTurckRicciArm_appCc_eval` (which grades the COMBINED `deTurckRicciRHS = −2 Ric + 𝓛_W` after the
DeTurck gauge cancellation).  Subtracting this pure `−2 Ric` grading from the combined grading isolates
the pure Lie-arm grading: this is exactly the classical decomposition `𝓛_W g = deTurckRicciRHS g − (−2)
Ric(g)` read off in the `appCc` form, which `deTurckLieArm_appCc_eval` assembles.

**The genuine differential-geometric content.**  The pure Ricci-arm difference is the bare-curvature
mean-value (FTC) reduction `ricciTensor_realized_sub_eq_integral_linearizedRicci`
(`RicciDifferenceMeanValue`): `Ric(g₁)_x(v0,v1) − Ric(g₁')_x(v0,v1) = ∫₀¹ DRic(g_s)[T − T']_x(v0,v1) ds`,
the `s`-integral of the linearized Ricci operator (the two-term Lichnerowicz form: order-`0` curvature
`Rm·h`, order-`2` rough Laplacian `g_s⁻¹∂²h`, plus the genuine order-`1` connection couplings) along the
convex metric path `g_s`.  Producing the exact endpoint operator fields `(P₀, P₁, P₂)` and the
eval-matching identity is the deep mean-value/Leibniz content of the pure Ricci-arm linearization — the
analogue of the combined arm's posited `integratedLinearizedRicci_appCc_eq` together with the bare-Ricci
FTC; it is the pure-curvature half of the combined grading.  It is stated here as the genuine existential
grading node, to be discharged by recursing into the bare-Ricci linearized `appCc` form together with the
operator-field path integration producing the coefficient fields.

**Non-vacuity.**  The predicate genuinely constrains `(P₀, P₁, P₂)` to *reproduce the actual
`(−2)`-scaled pure Ricci-arm difference value*, so it is non-vacuous: the zero triple fails it whenever
the realized Ricci arm is nonzero (the realization is `ℝ`-linear in `S` and its jets, so it vanishes as
`S → 0`, but does NOT vanish on a non-flat, genuinely second-order perturbation).  Consumers transitively
depend on its `sorryAx`. -/
theorem negTwoRicciArm_appCc_eval
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (P₀ : SmoothCcTensor g₀ 2 2) (P₁ : SmoothCcTensor g₀ 3 2) (P₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 P₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The bare-Ricci integrated Lichnerowicz `appCc` form supplies the order-graded coefficient fields.
  obtain ⟨P₀, P₁, P₂, heq⟩ :=
    integratedLinearizedRicci_negTwo_appCc_eq (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨P₀, P₁, P₂, fun x v => ?_⟩
  -- `smoothRiemannianMetricToInfty` is the definitional alias `:= g`, so it is transparent to
  -- `ricciTensor`; unfold it to expose the bare realized metrics.
  show ((-2 : ℝ) * ricciTensor (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
        - (-2 : ℝ) * ricciTensor (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) = _
  -- Pull out the `(−2)` scalar and rewrite the bare Ricci-tensor difference as the FTC integral of the
  -- bare linearized Ricci integrand along the convex realized metric path (`RicciDifferenceMeanValue`).
  rw [show ((-2 : ℝ) * ricciTensor (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
          - (-2 : ℝ) * ricciTensor (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
        (-2 : ℝ) * (ricciTensor (I := I)
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - ricciTensor (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) from by ring]
  rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.ricciTensor_realized_sub_eq_integral_linearizedRicci
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
  -- The `(−2)`-scaled integrated bare linearized Ricci is the order-graded `appCc` read-off.
  exact heq x v

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
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The COMBINED Ricci–DeTurck-arm grading `−2 Ric + 𝓛_W` supplies `(R₀, R₁, R₂)`; the pure `−2 Ric`-arm
  -- grading supplies `(P₀, P₁, P₂)`.  The Lie arm is their difference: `𝓛_W = deTurckRicciRHS − (−2)Ric`.
  obtain ⟨R₀, R₁, R₂, heval⟩ :=
    deTurckRicciArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  obtain ⟨P₀, P₁, P₂, hP⟩ :=
    negTwoRicciArm_appCc_eval (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨R₀ - P₀, R₁ - P₁, R₂ - P₂, fun x v => ?_⟩
  -- The pointwise decomposition of each realized DeTurck arm: in CLM form `deTurckRicciRHS g_bg g =
  -- (−2)•Ric(g∞) + lieDerivMetricClm g (deTurckVF g∞ g_bg∞)`, so the Lie term is the combined value
  -- minus the `(−2)Ric` value.  Read off both endpoints.
  have hsplit : ∀ (T₀ : SmoothCcTensor g₀ 0 2) {d : ℝ} (hd_lt : d < 1)
      (hd : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) d),
      lieDerivMetricClm (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd)
            (deTurckVF (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd))
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
        DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd) x (v 0) (v 1)
          - (-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T₀ hd_lt hd)) x (v 0) (v 1) := by
    intro T₀ d hd_lt hd
    rw [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- Rewrite the Lie-arm difference as the combined-arm difference minus the `(−2)Ric`-arm difference.
  rw [hsplit T hδ_lt hδ, hsplit T' hδ'_lt hδ']
  rw [show
      (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1))
          - (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)
              - (-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
              - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1))
          - ((-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
              - (-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) from by
    ring]
  rw [heval x v, hP x v]
  -- The RHS is the difference of the two `unitModel`/`appCc` triples; push subtraction through
  -- `unitModel`, then through `appCc`, collecting `(R₀ − P₀, R₁ − P₁, R₂ − P₂)`.
  rw [appCc_sub_left, appCc_sub_left, appCc_sub_left]
  rw [show
      (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
            - appCc (I := I) (M := M) g₀ 2 2 P₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')))
          + (appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                - appCc (I := I) (M := M) g₀ 3 2 P₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')))
          + (appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
                - appCc (I := I) (M := M) g₀ 4 2 P₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) =
        (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')))
          - (appCc (I := I) (M := M) g₀ 2 2 P₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 P₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 P₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) from by
    abel]
  rw [unitModel_sub_local, ContinuousMultilinearMap.sub_apply]

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
