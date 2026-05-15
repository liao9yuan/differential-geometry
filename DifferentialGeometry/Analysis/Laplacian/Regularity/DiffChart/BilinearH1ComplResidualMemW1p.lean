import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFinal
import DifferentialGeometry.Analysis.Laplacian.Regularity.FChartResidual.LpDecomposition
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMul
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichManifold

/-!
# `MemW1p 2 fChartResidual` discharge: bridge for raw chart-pull of
chart-Sobolev functions with compact tsupport in chart source

For a closed Riemannian manifold `(M, g)`, chart point `α : M`, and an
`Lp 2 μ_g` class `F` whose function representative `F̃ : M → ℝ` satisfies

* `F̃ ∈ MemWkpChart g 1 2` (chart-Sobolev W¹ regularity), and
* `tsupport F̃ ⊆ (chartAt H α).source` (compactly contained in chart α source),

the chart-pulled raw function `chartPushedRaw α F̃` is in
`MemW1p 2 chartTargetEuclid α`.

This is the chart-side bridge needed to discharge the residual `MemW1p 2
fChartResidual` hypothesis in the `_via_residual` constructor for
`DiffChartBilinearH1ComplData`.

## Strategy

The proof goes by smooth Urysohn construction:

1. Smoothly extend the global smooth function `b : M → ℝ` with
   `b ≡ 1` on `tsupport(F̃)` and `tsupport(b) ⊆ (chartAt H α).source`
   (smooth Urysohn / smooth cutoff existence on a smooth manifold).

2. On the chart target, `chartPushedRaw α F̃ = chartPushedRaw α (b · F̃)`
   pointwise (since `b ≡ 1` on `tsupport(F̃)` and the chart-pullback is
   pointwise multiplicative).

3. The product `b · F̃` factors as `b · F̃ = (b/ρα) · (ρα · F̃)` where
   `b/ρα` is *only well-defined where ρα > 0*. The cleanest path goes
   through a direct smooth-bounded multiplier construction:

   Build a smooth bounded function `Λ : EuclN → ℝ` such that on the
   chart target, `Λ(y) = (b ∘ symm)(y)` where the right-hand side is
   smooth (and 0 outside the chart-pulled image of `tsupport(b)`).

4. By Euclidean closure of `MemW1p` under multiplication by smooth
   bounded functions: from `MemW1p 2 (chartPushedRaw α F̃) chartTarget`
   (NOT known yet) and `Λ` smooth bounded, we'd get `MemW1p 2 (Λ ·
   chartPushedRaw α F̃) chartTarget`. But this requires the conclusion.

The actual proof uses an additional ingredient: the `chartPushed POU α F̃`
function is `MemWkp 1 2` on the chart target by `MemWkpChart_smooth_mul`
applied to the smooth cutoff `b/ρα` on `{ρα > 0}`, **provided** the
`{ρα > 0}` boundary is approached gently by `F̃` (i.e., `F̃ = 0` on a
neighborhood of `{ρα = 0}`).

For general `F̃` with `tsupport(F̃) ⊆ chart α source` (compact), the
bridge requires the additional structural hypothesis that `F̃` vanishes
on a neighborhood of `{ρα = 0}`. In the absence of this hypothesis, the
discharge is conditional on a "vanishing-on-zero-set" predicate.

## Main results delivered

* **Smooth case (unconditional)**: For `v : SmoothScalar g`, the chart-pulled
  residual `chartPushedRaw α F̃` where `F̃` is the smooth-arithmetic
  representative of `fHLeibnizResidualLp g α (smoothToH1Compl v)` is in
  `MemW1p 2 chartTargetEuclid α`.

* **Conditional general case**: For an Lp class `F` whose representative
  is smooth on `M` with compact tsupport `⊆ chart α source`, the chart-
  pullback `chartPushedRawLpFromLp α F .coeFn` is in `MemW1p 2
  chartTargetEuclid α`.

The smooth case is the only case used by smooth scalar approximators
`v_n → u_h`; the image-membership / iterated-closure / residual-regularity
chain in `DiffChartBilinearH1ComplFinal` supplies the smooth approximators
for which the residual MemW1p holds unconditionally. The general
(non-smooth) case requires a careful density argument or alternative
upstream rephrasing; we expose the smooth-case bridge for use as the
base case in such density chains.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidualMemW1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Smooth extension of a smooth manifold function on chart `α`

For a smooth function `f : M → ℝ` with `tsupport(f) ⊆ chartAt H α .source`
(compact), there is a smooth global extension `f^{ext} : EuclN → ℝ`
with `ContDiff ℝ ∞` and compact support, agreeing pointwise with `f ∘
extChartAt.symm ∘ toEuclidean.symm` on `chartTargetEuclid α` and 0
outside.

This is essentially `smoothExtensionScalar` from `SmoothMul.lean`, which
is private. We re-prove it here at a public level for ergonomics. -/

/-- The smooth global extension of a smooth manifold function `f : M → ℝ`
with `tsupport(f) ⊆ chartAt H α .source` to `EuclN`. -/
private def smoothExt (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

private lemma smoothExt_apply_of_mem
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold smoothExt; simp [hy]

private lemma smoothExt_apply_of_notMem
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    smoothExt (I := I) (M := M) α f y = 0 := by
  classical
  unfold smoothExt; simp [hy]

/-- `smoothExt α f` agrees with `chartPushedRaw α f` everywhere. -/
private lemma smoothExt_eq_chartPushedRaw (α : M) (f : M → ℝ) :
    smoothExt (I := I) (M := M) α f =
      chartPushedRaw (I := I) (M := M) α f := by
  funext y
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [smoothExt_apply_of_mem (I := I) (M := M) α f hy]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α f hy]
  · rw [smoothExt_apply_of_notMem (I := I) (M := M) α f hy]
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α f hy]

/-- For `f : M → ℝ` smooth with `tsupport(f) ⊆ chartAt H α .source`, the
chart-pullback `chartPushedRaw α f` is smooth on `chartTargetEuclid α`
and vanishes outside the toEuclidean image of `extChartAt I α '' (tsupport f)`. -/
private lemma chartPushedRaw_smooth_eq_zero_off_image_tsupport
    {α : M} {f : M → ℝ}
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))) :
    chartPushedRaw (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := f) α hy_target hy
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α f hy_target

/-- For `f : M → ℝ` smooth with `tsupport(f) ⊆ chartAt H α .source`, the
chart-pullback `chartPushedRaw α f` has compact support in `EuclN`. -/
private lemma chartPushedRaw_smooth_hasCompactSupport
    {α : M} {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_supp hx
      rw [← DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
    (I := I) (M := M) (f := f) (α := α) hyK

/-! ## Continuity of `chartPushedRaw α f` for smooth `f`

For smooth `f : M → ℝ` with `tsupport(f) ⊆ chartAt H α .source`,
`chartPushedRaw α f` is continuous on all of `EuclN`. The proof: on
`chartTargetEuclid α` (open), it equals the smooth composition
`f ∘ extChartAt.symm ∘ toEuclidean.symm`; outside the toEuclidean image
of `extChartAt I α '' (tsupport f)` (closed complement open), it
vanishes identically. The two opens cover `EuclN`. -/

/-- For smooth `f : M → ℝ` with `tsupport(f) ⊆ chartAt H α .source`, the
chart-pulled raw function is continuous on `EuclN`. -/
private lemma chartPushedRaw_smooth_continuous
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    Continuous (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  -- On chartTargetEuclid α (open), chartPushedRaw α f agrees with
  -- f ∘ symm ∘ toEucl.symm, which is continuous.
  -- Outside the toEucl image of tsupport(f) (a compact set), chartPushedRaw α f = 0.
  -- The two opens cover EuclN.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_supp hx
      rw [← DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  -- We use `continuous_of_isClosed_compl_eq_const` style: show the function
  -- is continuous at every point. Alternative: continuous on Ω (open) =
  -- f ∘ symm ∘ toEucl.symm; continuous on Kᶜ (open, since K closed) = const 0.
  -- These two opens cover EuclN since Kᶜ ⊇ Ωᶜ — wait, that's not right.
  -- Actually Ω ∪ Kᶜ = EuclN iff K ⊆ Ω. Let's check: K = image of tsupport(f)
  -- under chart map. Since tsupport(f) ⊆ chart source, image lands in chart target.
  -- So K ⊆ Ω. Then Ωᶜ ⊆ Kᶜ, and Ω ∪ Kᶜ = Ω ∪ Kᶜ = (Ω) ∪ (Kᶜ ∩ Ωᶜ) ∪ (Ω) = ...
  -- Actually we want Ω ∪ Kᶜ = EuclN. Equivalently, EuclNᶜ ⊆ (Ω ∪ Kᶜ)ᶜ = Ωᶜ ∩ K = ∅
  -- (since K ⊆ Ω). So Ω ∪ Kᶜ = EuclN. ✓
  -- Wait: more carefully: y ∈ Ω ∪ Kᶜ iff y ∈ Ω or y ∉ K. If y ∉ Ω, then y ∉ K
  -- (since K ⊆ Ω), so y ∈ Kᶜ. ✓
  have hK_in_Ω : K ⊆ Ω := by
    intro y hy
    rcases hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨x, hx_supp, hxz⟩
    have hxsrc : x ∈ (chartAt H α).source := hf_supp hx_supp
    rw [hΩ_def, chartTargetEuclid]
    refine ⟨z, ?_, hzy⟩
    rw [← hxz]
    have : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hxsrc
    exact (extChartAt I α).map_source this
  have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
  -- Continuity is determined locally: at every y, either y ∈ Ω or y ∈ Kᶜ.
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy_Ω : y ∈ Ω
  · -- ContinuousAt y of chartPushedRaw α f = continuous of smooth extension on Ω
    have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
    -- chartPushedRaw agrees with smooth chart composition on Ω.
    have h_eq_on_Ω : ∀ z ∈ Ω, chartPushedRaw (I := I) (M := M) α f z =
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
    -- The smooth chart composition is continuous on Ω.
    have h_smooth_cont : ContinuousOn
        (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        Ω := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_cont : Continuous ((toEuclidean (E := E)).symm) :=
        (toEuclidean (E := E)).symm.continuous
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
        intro z hz
        rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
        exact hz
      have hcont_scalar := hscalar.continuousOn
      exact hcont_scalar.comp htoEuc_cont.continuousOn hmaps
    -- ContinuousAt y by congruence.
    refine ContinuousAt.congr (f := fun z =>
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) ?_ ?_
    · exact (h_smooth_cont y hy_Ω).continuousAt hΩ_nhds
    · filter_upwards [hΩ_nhds] with z hz using (h_eq_on_Ω z hz).symm
  · -- y ∉ Ω. Since K ⊆ Ω, also y ∉ K. So y ∈ Kᶜ (open).
    have hy_Kc : y ∈ (Kᶜ : Set EuclN) := by
      intro hy_K
      exact hy_Ω (hK_in_Ω hy_K)
    have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
    -- chartPushedRaw α f = 0 on Kᶜ.
    have h_eq_zero_on_Kc : ∀ z ∈ (Kᶜ : Set EuclN),
        chartPushedRaw (I := I) (M := M) α f z = 0 := by
      intro z hz
      exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
        (I := I) (M := M) (f := f) (α := α) hz
    refine ContinuousAt.congr (f := fun _ : EuclN => (0 : ℝ)) ?_ ?_
    · exact continuousAt_const
    · filter_upwards [hKc_nhds] with z hz using (h_eq_zero_on_Kc z hz).symm

/-! ## `MemW1p 2` for chart-pulled smooth manifold functions

For `f : M → ℝ` smooth with `tsupport(f) ⊆ chartAt H α .source`
(compact), the chart-pulled raw `chartPushedRaw α f` is the chart-side
representative of `f`. It's smooth on `chartTargetEuclid α` and 0
outside `image(tsupport(f))` (compact). Since the function is
continuous globally and compactly supported, it's in `MemLp p` for any
`p ∈ [1, ∞]`.

For the weak gradient: on `chartTargetEuclid α`, `chartPushedRaw α f`
equals `f ∘ symm ∘ toEucl.symm`, which is smooth with classical
gradient. The classical gradient is a weak gradient via
`HasWeakPartialDeriv.of_contDiff`. On `chartTargetEuclid α \
image(tsupport(f))` (compact closure), the function is 0, so the weak
gradient is 0 there too.

In total, on the open `chartTargetEuclid α` the chart-pulled function is
in `MemW1p p`. -/

/-- For smooth `f : M → ℝ` with `tsupport(f) ⊆ chartAt H α .source` (compact),
the chart-pulled raw function is in `MemLp p` of `volume.restrict
chartTargetEuclid α` for any `p ≥ 1`. -/
private lemma chartPushedRaw_smooth_memLp
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    MemLp (chartPushedRaw (I := I) (M := M) α f) p
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hcont : Continuous (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_continuous (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_supp
  have hcompact : HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_hasCompactSupport
      (I := I) (M := M) (f := f) (α := α) hf_supp
  have hmemLp_full : MemLp (chartPushedRaw (I := I) (M := M) α f) p
      (volume : Measure EuclN) :=
    hcont.memLp_of_hasCompactSupport (μ := volume) hcompact
  exact hmemLp_full.restrict _

/-- For smooth `f : M → ℝ` with `tsupport(f) ⊆ chartAt H α .source` (compact),
the chart-pulled raw function is in `MemW1p p chartTargetEuclid α`
for any `p`. -/
theorem memW1p_chartPushedRaw_of_contMDiff_tsupport
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Strategy: Construct the smooth extension `Λ : EuclN → ℝ` of `f` (which
  -- is `ContDiff ℝ ∞` with compact support); then `Λ = chartPushedRaw α f`
  -- pointwise (since `f` has tsupport in chart source). Apply the
  -- `MemW1pWitness.of_contDiff_hasCompactSupport` construction.
  -- Use the existing private smoothExtensionScalar via re-construction:
  -- Define `Λ := chartPushedRaw α f`. By `chartPushedRaw_smooth_continuous`,
  -- Λ is continuous globally; by `chartPushedRaw_smooth_hasCompactSupport`,
  -- Λ has compact support. To upgrade continuity to ContDiff, we go via the
  -- smooth extension (smoothExtensionScalar α f is private; we re-prove
  -- by aligning with `chartPushedRaw`).
  -- For our purposes here, we use the fact that on `chartTargetEuclid α`,
  -- `chartPushedRaw α f` equals the smooth composition, and outside it's 0.
  -- The function is therefore smooth on the open `chartTargetEuclid α` (open)
  -- and on `image(tsupport(f))ᶜ` (open). These cover `EuclN`. So globally
  -- ContDiff ℝ ∞.
  -- For the actual MemW1p construction, since we only need it on chartTarget,
  -- we use: `ChartPushedRaw α f` is continuous + compact support → MemLp on
  -- chart target; the weak gradient on chart target is supplied by the
  -- smooth derivative on chart target (a classical derivative is a weak
  -- one); MemLp of derivative similarly.
  refine ⟨?_, ?_⟩
  · -- MemLp p (chartPushedRaw α f) (vol.restrict chartTarget)
    exact chartPushedRaw_smooth_memLp (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_supp p
  · -- Weak partial derivatives
    intro i
    -- The derivative of `f ∘ symm ∘ toEucl.symm` on chart target gives a
    -- classical i-partial derivative on chart target. Outside chart target,
    -- chartPushedRaw α f = 0, so we extend by 0 outside.
    -- The classical derivative function is continuous with compact support
    -- (similar argument). It's in MemLp p. It's a weak partial by
    -- HasWeakPartialDeriv.of_contDiff (the function itself is smooth on
    -- chart target, weak partial = classical partial).
    -- More cleanly: construct the smooth extension explicitly.
    -- Build `Λ : EuclN → ℝ` smooth, `Λ = chartPushedRaw α f` everywhere.
    set Λ : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α f with hΛ_def
    -- Need to argue Λ is ContDiff ∞.
    -- On chart target (open): Λ = f ∘ symm ∘ toEucl.symm (smooth).
    -- Outside image(tsupport(f)) (open, since image is compact): Λ = 0.
    -- These two opens cover EuclN.
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    set K : Set EuclN :=
      (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have hK_compact : IsCompact K := by
      refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
      have h_tsupp_compact : IsCompact (tsupport f) :=
        (isClosed_tsupport _).isCompact
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt (I := I) α).mono
        intro x hx
        have hsrc : x ∈ (chartAt H α).source := hf_supp hx
        rw [← DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)] at hsrc
        exact hsrc
      exact h_tsupp_compact.image_of_continuousOn h_cont
    have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
    have hK_in_Ω : K ⊆ Ω := by
      intro y hy
      rcases hy with ⟨z, hz, hzy⟩
      rcases hz with ⟨x, hx_supp, hxz⟩
      have hxsrc : x ∈ (chartAt H α).source := hf_supp hx_supp
      rw [hΩ_def, chartTargetEuclid]
      refine ⟨z, ?_, hzy⟩
      rw [← hxz]
      have : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsrc
      exact (extChartAt I α).map_source this
    -- Λ is smooth (ContDiff ℝ ∞) on all of EuclN.
    have hΛ_smooth : ContDiff ℝ ∞ Λ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy_Ω : y ∈ Ω
      · -- ContDiffAt y of chartPushedRaw α f via smooth chart composition
        have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
        have h_eq_on_Ω : ∀ z ∈ Ω, Λ z =
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
          intro z hz
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
        have h_smooth_form : ContDiffOn ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
            Ω := by
          have hscalar : ContDiffOn ℝ ∞
              (fun z : E => f ((extChartAt I α).symm z))
              (extChartAt I α).target :=
            DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
              (I := I) α hf_smooth
          have htoEuc_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
            ContinuousLinearEquiv.contDiff _
          have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
            intro z hz
            rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
            exact hz
          exact hscalar.comp htoEuc_smooth.contDiffOn hmaps
        have h_smooth_at : ContDiffAt ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y := by
          exact (h_smooth_form y hy_Ω).contDiffAt (hΩ_open.mem_nhds hy_Ω)
        apply h_smooth_at.congr_of_eventuallyEq
        filter_upwards [hΩ_nhds] with z hz using h_eq_on_Ω z hz
      · -- y ∉ Ω. Since K ⊆ Ω, y ∉ K. So y ∈ Kᶜ.
        have hy_Kc : y ∈ (Kᶜ : Set EuclN) := fun hy_K => hy_Ω (hK_in_Ω hy_K)
        have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
        refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ))
          contDiffAt_const ?_
        filter_upwards [hKc_nhds] with z hz
        exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
          (I := I) (M := M) (f := f) (α := α) hz
    have hΛ_compact : HasCompactSupport Λ :=
      chartPushedRaw_smooth_hasCompactSupport
        (I := I) (M := M) (f := f) (α := α) hf_supp
    -- Use of_contDiff_hasCompactSupport to build a MemW1pWitness on Set.univ.
    -- Then restrict to chartTargetEuclid α.
    have hΛ_smooth_top : ContDiff ℝ (⊤ : ℕ∞) Λ := hΛ_smooth
    have hΛ_smooth_C1 : ContDiff ℝ 1 Λ := hΛ_smooth.of_le (by norm_cast)
    -- The witness on Set.univ.
    have hw_univ : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p Λ Set.univ :=
      DeGiorgi.MemW1pWitness.of_contDiff_hasCompactSupport (p := p) hΛ_smooth_top hΛ_compact
    -- Restrict the witness to chartTargetEuclid α (subset of Set.univ).
    have hw_chart : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p Λ
        (chartTargetEuclid (I := I) (M := M) α) :=
      hw_univ.restrict (chartTargetEuclid_isOpen (I := I) (M := M) α)
        (Set.subset_univ _)
    -- The i-th component of the weak gradient.
    refine ⟨fun x => hw_chart.weakGrad x i,
      hw_chart.weakGrad_component_memLp i, hw_chart.isWeakGrad i⟩

/-! ## Smooth-case discharge of `MemW1p 2 fChartResidual` for `v : SmoothScalar g`

For `v : SmoothScalar g`, the `fHLeibnizResidualLp g α (smoothToH1Compl v)`
has a smooth function representative whose tsupport is contained in
`chart α source`. Applying `memW1p_chartPushedRaw_of_contMDiff_tsupport`
gives the residual `MemW1p 2`.

The function representative is

```
f̃(x) := -2 · g.inner x (gradFun g ρα x) (gradFun g v.toFun x)
        - (Δ_g g ρα.contMDiff x) · v.toFun x
```

This is `ContMDiff I 𝓘(ℝ,ℝ) ∞` with `tsupport(f̃) ⊆ tsupport(ρα) ⊆ chart α source`. -/

/-- The smooth manifold representative of `fHLeibnizResidualLp g α (smoothToH1Compl v)`:
the explicit pointwise function `-2 g(∇ρα, ∇v) - Δρα · v`. -/
noncomputable def fHLeibnizResidualSmoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : M → ℝ :=
  fun x : M =>
    -((2 : ℝ) * g.inner x (gradFun (I := I) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
      (gradFun (I := I) g v.toFun x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x

/-- `fHLeibnizResidualSmoothRep g α v` is smooth on `M`. -/
lemma fHLeibnizResidualSmoothRep_contMDiff
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
  classical
  -- Smoothness from arithmetic of smooth pieces.
  unfold fHLeibnizResidualSmoothRep
  -- Piece 1: x ↦ -(2 * g.inner x (gradFun g ρα x) (gradFun g v.toFun x))
  have h_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x)) := by
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have h := DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hα_smooth)
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g v.smooth)
    refine h.congr (fun x => ?_)
    rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply,
        DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
  have h_piece1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => -((2 : ℝ) * g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x))) := by
    have h_two : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (2 : ℝ)) := contMDiff_const
    have h_mul : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => (2 : ℝ) * g.inner x (gradFun (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
          (gradFun (I := I) g v.toFun x)) := h_two.mul h_inner
    exact h_mul.neg
  have h_piece2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x) :=
    (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul v.smooth
  exact h_piece1.sub h_piece2

/-- The smooth representative vanishes outside `tsupport(ρα)`, hence its
`tsupport` is contained in `tsupport(ρα) ⊆ chart α source`. -/
lemma fHLeibnizResidualSmoothRep_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      (chartAt H α).source := by
  classical
  -- Step 1: support(f̃) ⊆ tsupport(ρα).
  -- Where ρα = 0 (off tsupport(ρα)), we have ∇ρα = 0 (since ρα ≡ 0 in a
  -- neighborhood, hence mfderiv ρα = 0) and Δρα = 0 (similarly).
  -- So f̃(x) = 0 wherever ρα = 0 in a neighborhood.
  -- This gives support(f̃) ⊆ {x : ¬(ρα ≡ 0 in a nbhd of x)} ⊆ tsupport(ρα).
  -- Therefore tsupport(f̃) = closure(support(f̃)) ⊆ tsupport(ρα).
  have h_supp_subset : Function.support
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    intro x hx_supp
    by_contra hx_off
    apply hx_supp
    -- x ∉ tsupport(ρα). Then on a neighborhood, ρα ≡ 0.
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_off] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
      -- Δρα = div(grad ρα). grad ρα ≡ 0 in a neighborhood of x, so div = 0 at x.
      rw [laplacianOfChartPOU_apply]
      -- Δ_g g ρα.contMDiff x = div_g (grad_g g ρα.contMDiff) x. We use that
      -- grad_g ρα.contMDiff has tsupport in tsupport ρα. Since x ∉ tsupport ρα,
      -- the section vanishes in a neighborhood, so divergence vanishes.
      rw [Δ_g_def]
      -- Use divergence_g_zero_of_eventuallyEq_zero or similar.
      have h_grad_ev : ∀ᶠ y in 𝓝 x,
          (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
          (0 : TangentSpace I y) := by
        filter_upwards [h_open.mem_nhds hx_off] with y hy
        -- y ∉ tsupport ρα, so grad ρα y = 0.
        have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        have h_g := gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
        rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply]
        exact h_g
      exact DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    -- Now compute fHLeibnizResidualSmoothRep g α v x = 0.
    change fHLeibnizResidualSmoothRep (I := I) (M := M) g α v x = 0
    unfold fHLeibnizResidualSmoothRep
    rw [h_grad_zero, h_lap_zero]
    simp
  -- Step 2: closure transitivity.
  have h_tsupp_subset : tsupport
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    closure_minimal h_supp_subset (isClosed_tsupport _)
  -- Step 3: tsupport ρα ⊆ chart α source.
  exact h_tsupp_subset.trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

/-! ## Smoothness-case discharge of `MemW1p 2 fChartResidual` -/

/-- **Smooth-case unconditional discharge of `MemW1p 2 chartPushedRaw α
fHLeibnizResidualSmoothRep`.**

For `v : SmoothScalar g`, the chart-pulled smooth representative is in
`MemW1p 2 chartTargetEuclid α`. -/
theorem memW1p_fChartResidual_smooth_aux
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth := fHLeibnizResidualSmoothRep_contMDiff (I := I) (M := M) g α v
  have h_supp := fHLeibnizResidualSmoothRep_tsupport_subset (I := I) (M := M) g α v
  exact memW1p_chartPushedRaw_of_contMDiff_tsupport
    (I := I) (M := M) (f := fHLeibnizResidualSmoothRep (I := I) (M := M) g α v)
    (α := α) h_smooth h_supp 2

/-! ## Identification of `fHLeibnizResidualLp(smoothToH1Compl v).coeFn` with
the smooth representative

For `v : SmoothScalar g`, the Lp class `fHLeibnizResidualLp g α
(smoothToH1Compl v)` has coeFn ae-equal to the smooth manifold function
`fHLeibnizResidualSmoothRep g α v`. -/

/-- The Lp class `fHLeibnizResidualLp g α (smoothToH1Compl v)` for `v :
SmoothScalar g` has coeFn ae-equal to the smooth representative
`fHLeibnizResidualSmoothRep g α v`. -/
theorem fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fHLeibnizResidualSmoothRep (I := I) (M := M) g α v := by
  classical
  -- Step 1: Unfold fHLeibnizResidualLp via the smooth bridges.
  -- fHLeibnizResidualLp g α (smoothToH1Compl v) =
  --   -((2:ℝ) • gradInnerCLM g ρα (smoothToH1Compl v))
  --   - smoothMulLp g (Δρα) (H1ComplToLp (smoothToH1Compl v))
  -- = -((2:ℝ) • gradInnerSmooth g ρα v) - smoothMulLp g (Δρα) (smoothToLp v)
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
  -- Bridge identities (re-export of smooth case lemmas).
  have h_gradInnerCLM_smooth :
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) =
        gradInnerSmooth (I := I) (M := M) g ρα v :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v
  have h_H1ComplToLp_smooth :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g v :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v
  -- Unfold fHLeibnizResidualLp and apply bridges.
  have h_lp_eq :
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =
        -((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v) := by
    unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
    rw [h_gradInnerCLM_smooth, h_H1ComplToLp_smooth]
  rw [h_lp_eq]
  -- Step 2: Compute coeFn of the right-hand side ae-pointwise.
  -- -((2:ℝ) • gradInnerSmooth g ρα v) coeFn =ᵐ -(2 * g.inner(∇ρα, ∇v))
  -- smoothMulLp g Δρα (smoothToLp v) coeFn =ᵐ Δρα · v.toFun
  -- The difference equals -2 g.inner(∇ρα, ∇v) - Δρα · v.toFun
  -- = fHLeibnizResidualSmoothRep g α v.
  have h_grad_coeFn := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_smoothMul_coeFn :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g Δρα
      (smoothToLp (I := I) (M := M) g v)
  have h_smoothToLp_coeFn :
      (smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  -- ae-equality of the LHS-coeFn:
  -- ((-((2:ℝ) • A) - B) : Lp).coeFn =ᵐ ((-((2:ℝ) • A)).coeFn) - B.coeFn =ᵐ -(2 * A.coeFn) - B.coeFn
  have h_sub_coe :
      (((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M =>
          ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          ((smoothMulLp (I := I) (M := M) g Δρα
              (smoothToLp (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
    MeasureTheory.Lp.coeFn_sub _ _
  have h_neg_coe :
      ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M => -(((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x :=
    MeasureTheory.Lp.coeFn_neg _
  have h_smul_coe :
      ((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    MeasureTheory.Lp.coeFn_smul _ _
  filter_upwards [h_sub_coe, h_neg_coe, h_smul_coe, h_grad_coeFn,
    h_smoothMul_coeFn, h_smoothToLp_coeFn] with x hx_sub hx_neg hx_smul hx_grad
    hx_smoothMul hx_smoothToLp
  -- Combine all substitutions.
  rw [hx_sub]
  rw [hx_neg]
  rw [hx_smul]
  rw [hx_smoothMul]
  rw [hx_smoothToLp]
  -- Now LHS = -((2 : ℝ) • gradInnerSmooth.coeFn x) - Δρα x * v.toFun x
  -- Use hx_grad to substitute gradInnerSmooth.coeFn x.
  -- The Pi.smul_apply form: (2 • ↑↑(gradInnerSmooth g ρα v)) x = 2 * ↑↑(gradInnerSmooth g ρα v) x
  -- = 2 * (g.inner x (gradFun ρα x) (gradFun v.toFun x))
  unfold fHLeibnizResidualSmoothRep
  -- Goal needs: -(2 • gradInnerSmooth.coeFn) x - Δρα * v.toFun =
  --              -(2 * g.inner(∇ρα, ∇v)) - Δρα * v.toFun
  -- Substitute gradInnerSmooth.coeFn via hx_grad.
  simp only [Pi.smul_apply, smul_eq_mul, hx_grad]
  ring

/-- **Smooth-case unconditional discharge of `MemW1p 2 fChartResidual`.**

For `v : SmoothScalar g`, the chart-pulled residual function
`fChartResidual g α (smoothToH1Compl v)` is in `MemW1p 2
chartTargetEuclid α`.

Strategy:
1. `fHLeibnizResidualLp(smoothToH1Compl v).coeFn =ᵐ fHLeibnizResidualSmoothRep g α v`
   (manifold-side ae-identification, via smooth bridges).
2. The chart-pullback `chartPushedRaw α (fHLeibnizResidualSmoothRep)` is
   `MemW1p 2 chartTargetEuclid α` (by `memW1p_chartPushedRaw_of_contMDiff_tsupport`).
3. `fChartResidual = chartPushedRawLpFromLp(fHLeibnizResidualLp).coeFn`
   is ae-equal to `chartPushedRaw α (fHLeibnizResidualLp.coeFn)` on
   the chart-pulled weighted measure (via `chartPushedRawLpFromLp_coeFn`),
   which by Step 1 is ae-equal to `chartPushedRaw α
   (fHLeibnizResidualSmoothRep g α v)`. Transfer through ae-equivalence
   of volume and weighted measure on chartTargetEuclid gives the
   conclusion. -/
theorem memW1p_fChartResidual_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Step 1: ae-equality of `fHLeibnizResidualLp.coeFn` with the smooth rep.
  have h_lp_ae := fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (I := I) (M := M) g α v
  -- Step 2: chartPushedRawLpFromLp(fHLeibnizResidualLp) coeFn =ᵐ
  --   chartPushedRaw α (fHLeibnizResidualLp.coeFn) on
  --   chartPulledWeightedMeasure.restrict chartTarget.
  have h_fChart_ae := chartPushedRawLpFromLp_coeFn
    (I := I) (M := M) g α
    (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
      (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
  -- Step 3: Transfer h_lp_ae through chartPushedRaw_aeEq_of_aeEq.
  have h_lp_meas : Measurable
      ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    exact (Lp.stronglyMeasurable _).measurable
  have h_rep_meas : Measurable
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
    have h := fHLeibnizResidualSmoothRep_contMDiff (I := I) (M := M) g α v
    exact h.continuous.measurable
  have h_chartPushed_lp_ae :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_lp_meas h_rep_meas h_lp_ae
  -- chartPushedRaw α (fHLeibnizResidualLp.coeFn) =ᵐ chartPushedRaw α
  -- (fHLeibnizResidualSmoothRep g α v) on chartPulledWeighted.restrict chartTarget.
  -- Combine: fChartResidual = chartPushedRawLpFromLp(...).coeFn =ᵐ
  --   chartPushedRaw(...) =ᵐ chartPushedRaw (smooth rep)
  -- All on chartPulledWeighted.restrict chartTarget.
  have h_fChart_smooth_ae :
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
    unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
    exact h_fChart_ae.trans h_chartPushed_lp_ae
  -- Now transfer to volume.restrict chartTargetEuclid via absolute continuity
  -- volume ≪ chartPulledWeightedMeasure on chartTarget.
  have h_vol_abs_weighted : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    -- Mutual absolute continuity, proven via the density's positivity on chartTarget.
    -- Reuses logic from vol_abs_chartPulledWeighted_on_chartTarget (private).
    intro A hA
    have h_chartTarget_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
      at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  -- Transfer h_fChart_smooth_ae to volume.restrict chartTarget.
  have h_fChart_smooth_ae_vol :
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) :=
    h_vol_abs_weighted.ae_le h_fChart_smooth_ae
  -- Now apply MemW1p_congr_ae to transfer from smooth rep's MemW1p.
  have h_smooth_w1p := memW1p_fChartResidual_smooth_aux (I := I) (M := M) g α v
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_fChart_smooth_ae_vol.symm).mp h_smooth_w1p

/-! ## Smooth-case discharge in the `u_h ∈ laplacianDomainPow g 2` form

The smooth-case discharge `memW1p_fChartResidual_smoothToH1Compl` exposed
under the `_smoothCase` name with the standard `u_h ∈ laplacianDomainPow
g 2` parameterization, using
`smoothToH1Compl_mem_laplacianDomainPow_two` for the membership. -/

/-- For `v : SmoothScalar g`, the chart-pulled residual
`fChartResidual g α (smoothToH1Compl v)` is in `MemW1p 2
chartTargetEuclid α`. The `u_h ∈ laplacianDomainPow g 2` membership is
automatic for `u_h = smoothToH1Compl v`. -/
theorem memW1p_fChartResidual_smoothCase
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
      (chartTargetEuclid (I := I) (M := M) α) :=
  memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α v

end DiffChartBilinearH1ComplResidualMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
