import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping

/-!
# `C^∞`/`Cᵏ`-Banach completeness of the smooth-tensor space

This file isolates the **`Cᵏ`-Banach completeness keystone** of the smooth,
compactly-supported tensor space: a sequence of smooth tensors that is Cauchy in
*every* spectral order `H^{2k}` (i.e. `SmoothCcTensor.toHs (2k)`) and converges in
`L²` to an abstract limit `u : TensorL2 r s g` has its `L²` limit `u` *realised by a
genuine smooth section*.

```
theorem smoothCcTensor_limit_of_allOrders_toHs_cauchy
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ, CauchySeq (fun n => SmoothCcTensor.toHs (2*k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u
```

This is the precise `Cᵏ`-Banach-completeness content of the all-orders spectral
Sobolev embedding `⋂_σ Hˢ ⊆ C^∞`. The smooth inclusion `SmoothCcTensor ↪ TensorL2`
is only `DenseRange` (not a closed embedding), so this is a genuine theorem, not a
formality: the abstract `L²` limit `u` lives in the completion, and the keystone
exhibits an honest smooth representative.

## The argument

For each chart center `α : M` and component multi-index `P : TensorCompIdx r s`, the
chart-pushed raw scalar components
`u_n := chartPushedRaw I α (tensorChartComponentRaw g r s (F n) α P.1 P.2) : EuclN → ℝ`
are uniformly Cauchy in *every* `Cᵐ` on the open Euclidean chart target
(`chartComponentScalar_chartPushed_allOrder_uniformCauchy`): one combines the
pointwise reverse-Christoffel order-peeling
(`iteratedFDeriv` of a chart component is controlled, up to uniform
Christoffel-coefficient corrections, by the order-`0` content of the iterated
covariant gradients `∇^i (F n)`) with the unconditional `Cᵐ` tensor Sobolev
embedding (`∑_{j≤m} ‖(∇^j T).toSection x‖ ≤ C·‖T.toHs(2k)‖`, `2k > finrank + 2m`),
so that the `toHs(2k)`-Cauchy hypothesis pushes down to per-chart `Cᵐ`-Cauchy of
the components.

The Euclidean uniform-limit-of-derivatives machinery
(`EuclideanMorrey.cauchyLimitFun` / `iteratedFDeriv_cauchyLimitFun_eq`) then produces
a common `C^∞` pointwise limit `u_∞,α,P : EuclN → ℝ`, compactly supported strictly
inside the chart target. Assembling these via
`tensorBundleSectionOfChartComponents` and summing against the chart-atlas partition
of unity yields a global `SmoothCcTensor`, whose `L²` chart components agree a.e.
with those of `u`; by `tensorL2_eq_of_chartComponent_eq` its `L²` class is `u`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`0` reverse fibre bound (the converse of
`riemannianFiberNormSq_le_raw_components_on_pouTsupport`).**

For a chart base point `α` and tensor ranks `(r, s)`, there is a non-negative
constant `C` such that for every smooth compactly-supported section `S` and every
point `b` in the closed support of the chart-atlas partition-of-unity weight at
`α`, the order-`0` raw content `zeroContentR g r s S α y` (the sum of magnitudes
of the chart-`α` raw scalar components), read at the chart-target image `y` of
`b`, is bounded by `C` times the intrinsic Riemannian fibre norm
`‖S.toSection b‖`.

The chart-`α` trivialisation is a continuous-linear iso on the chart source whose
operator norm is, by
`tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional`, uniformly
bounded on the compact partition-of-unity kernel; composing with the fixed
component projections `tensorChartComponentProjection` gives the bound. This is
the missing converse that converts the pointwise raw content produced by the
reverse-Christoffel order-peeling into the intrinsic fibre norms controlled by the
`Cᵐ` tensor Sobolev embedding. -/
theorem exists_zeroContentR_le_fiberNorm_on_pouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {y : EuclN},
        y ∈ chartPouKernel (I := I) (M := M) α →
        zeroContentR (I := I) (M := M) g r s S α y ≤
          C * ‖S.toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  -- The closed POU support of the chart-atlas weight at `α`.
  set Tα : Set M := tsupport
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hTα_def
  have hTα_src : Tα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  -- The order-`0` raw-component ↔ fibre-inner quadratic-form bound (no model norm).
  obtain ⟨Craw, hCraw_nn, hCraw⟩ :=
    tensorChartComponentRaw_sq_le_const_mul_tensorInner (I := I) (M := M) g r s α
  -- The number of component pairs.
  set Npair : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * Real.sqrt Craw, by positivity, ?_⟩
  intro S y hy
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  -- `b` lies in the closed POU support (hence the chart source).
  have hb_supp : b ∈ Tα := by
    obtain ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩ := hy
    have hx_chart : x ∈ (chartAt H α).source := hTα_src hx_supp
    have hb_eq : b = x := by
      rw [hb_def, ← hzy, (toEuclidean (E := E)).symm_apply_apply, ← hxz]
      exact (extChartAt I α).left_inv
        (by rw [extChartAt_source (I := I)]; exact hx_chart)
    rw [hb_eq]; exact hx_supp
  -- The fibre norm of `S.toSection b` in terms of the model pointwise inner product.
  have hfib_eq : ‖S.toSection b‖ =
      Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) := by
    rw [show S.toFun b = TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (S.toSection b) from rfl]
    exact DifferentialGeometry.Integral.Connection.norm_eq_sqrt_tensorInnerPointwise
      (I := I) (M := M) g r s b (S.toSection b)
  have hInner_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hfib_nn : 0 ≤ ‖S.toSection b‖ := norm_nonneg _
  -- `rawPullR S α q y = tensorChartComponentRaw S α q b` at the chart preimage `b`.
  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      rawPullR (I := I) (M := M) g r s S α Idx Jdx y =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
    intro Idx Jdx
    rw [rawPullR, Function.comp_apply, Function.comp_apply, ← hb_def]
  -- Bound each raw magnitude by `√Craw · ‖S.toSection b‖`, then sum.
  have h_each : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))),
      |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y| ≤
        Real.sqrt Craw * ‖S.toSection b‖ := by
    intro q
    rw [h_raw_eq q.1 q.2]
    have hsq := hCraw S q.1 q.2 b hb_supp
    have hroot :
        Real.sqrt
            ((tensorChartComponentRaw (I := I) (M := M) g r s S α q.1 q.2 b) ^ 2) ≤
          Real.sqrt (Craw * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs] at hroot
    refine hroot.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCraw_nn, hfib_eq]
  calc zeroContentR (I := I) (M := M) g r s S α y
      = ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          |rawPullR (I := I) (M := M) g r s S α q.1 q.2 y| := rfl
    _ ≤ ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          Real.sqrt Craw * ‖S.toSection b‖ :=
        Finset.sum_le_sum (fun q _ => h_each q)
    _ = Npair * Real.sqrt Craw * ‖S.toSection b‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]; ring

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-chart, per-order constant for the chart-component derivative bound.**
For a chart `α`, component multi-index `P`, and Fréchet order `j`, there is a
non-negative constant `C` such that for every smooth compactly-supported
difference section `D`, the order-`j` Fréchet derivative operator norm of the
Euclidean chart component `tensorChartComponent g r s D α P.1 P.2`, at every point
`y`, is bounded by `C` times the sum over `i ≤ j` of the intrinsic Riemannian
fibre norms of the iterated covariant gradients `‖(∇^i D).toSection x‖`. Off the
chart-target it vanishes; on the partition-of-unity kernel the bound combines the
partition-of-unity Leibniz expansion of `chartComponent = ρ_α · rawPullR` with the
reverse-Christoffel order-peeling and the order-`0` reverse fibre bound. -/
private theorem exists_iteratedFDeriv_chartComponent_le_fiberNorm_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g r s) (y : EuclN),
        ‖iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2) y‖ ≤
          C * ∑ i ∈ Finset.range (j + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
            ‖(iteratedCovGrad g r s i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
  classical
  -- Uniform bound on the chart-pushed partition-of-unity weight `ρ_α` and all its
  -- derivatives, on the compact partition-of-unity kernel.
  obtain ⟨Cpou, hCpou_nn, hCpou⟩ :=
    exists_iteratedFDeriv_norm_bound_on_compactR
      (chartPushedRaw_chartAtlasPOU_contDiffOn
        (I := I) (M := M) α)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
      (chartImagePOUTsupport_subset_target (I := I) (M := M) α) j
  -- The pointwise reverse-peeling constant (covering all orders `≤ j`).
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum (I := I) (M := M) g r s α j j (le_refl j)
  -- The order-`0` reverse fibre bound, for each derived rank `s + i`.
  have h_fib : ∀ i : ℕ,
      ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (T : SmoothCcTensor g r (s + i)) {z : EuclN},
        z ∈ chartPouKernel (I := I) (M := M) α →
        zeroContentR (I := I) (M := M) g r (s + i) T α z ≤
          Ci * (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
            ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))‖) :=
    fun i => exists_zeroContentR_le_fiberNorm_on_pouKernel (I := I) (M := M) g r (s + i) α
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (j + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  refine ⟨(2 : ℝ) ^ j * Cpou * Cpeel * Cfibmax, by positivity, ?_⟩
  intro D y
  set fibSum : ℝ := ∑ i ∈ Finset.range (j + 1),
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
    ‖(iteratedCovGrad g r s i D).toSection
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) with hfibSum_def
  have hfibSum_nn : 0 ≤ fibSum := by
    rw [hfibSum_def]
    refine Finset.sum_nonneg (fun i _ => ?_)
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
    exact norm_nonneg _
  by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
  · -- On the kernel: Leibniz expansion + reverse-peeling + fibre bound.
    have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α hyK
    set ρ : EuclN → ℝ :=
      chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_def
    set raw : EuclN → ℝ :=
      chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g r s D α P.1 P.2)
      with hraw_def
    -- On the chart target, the chart component equals `ρ · raw` (eventually).
    have h_evEq : tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 =ᶠ[nhds y]
        (fun z => ρ z * raw z) :=
      tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw_raw
        (I := I) (M := M) g r s D α P.1 P.2 hyT
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq j).self_of_nhds]
    -- Smoothness of the two factors at `y`.
    have hO_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hρ_cdOn : ContDiffOn ℝ ∞ ρ (chartTargetEuclid (I := I) (M := M) α) :=
      chartPushedRaw_chartAtlasPOU_contDiffOn
        (I := I) (M := M) α
    have hraw_cdOn : ContDiffOn ℝ ∞ raw (chartTargetEuclid (I := I) (M := M) α) := by
      refine (rawPullR_contDiffOn (I := I) (M := M) g r s D α P.1 P.2).congr (fun z hz => ?_)
      rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]; rfl
    -- Leibniz for the iterated derivative of the product.
    have hLeib := norm_iteratedFDerivWithin_mul_le
      (𝕜 := ℝ) (f := ρ) (g := raw) (n := j) hρ_cdOn hraw_cdOn
      hO_open.uniqueDiffOn hyT (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => ρ z * raw z) j hO_open hyT] at hLeib
    refine le_trans hLeib ?_
    -- Bound each Leibniz summand.
    have hbound_term : ∀ l ∈ Finset.range (j + 1),
        (j.choose l : ℝ) *
            ‖iteratedFDerivWithin ℝ l ρ (chartTargetEuclid (I := I) (M := M) α) y‖ *
            ‖iteratedFDerivWithin ℝ (j - l) raw
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) := by
      intro l hl
      have hlj : l ≤ j := by have := Finset.mem_range.mp hl; omega
      -- `‖D^l ρ y‖ ≤ Cpou`.
      have hρ_l : ‖iteratedFDerivWithin ℝ l ρ
          (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ Cpou := by
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := ρ) l hO_open hyT]
        exact hCpou l hlj y hyK
      -- `‖D^{j-l} raw y‖ ≤ Cpeel · ∑_{i≤j-l} zeroContentR (∇^i D) ≤ Cpeel·Cfibmax·fibSum`.
      have hraw_l : ‖iteratedFDerivWithin ℝ (j - l) raw
          (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ Cpeel * Cfibmax * fibSum := by
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := raw) (j - l) hO_open hyT]
        -- `raw = chartPushedRaw(rawComp) = rawPullR D α P` near `y`.
        have hraw_evEq : raw =ᶠ[nhds y]
            rawPullR (I := I) (M := M) g r s D α P.1 P.2 := by
          filter_upwards [hO_open.mem_nhds hyT] with z hz
          rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]; rfl
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hraw_evEq (j - l)).self_of_nhds]
        -- Reverse-peeling (with `p = 0`, so the rank is `s + 0 = s` via `iteratedCovGrad … 0`).
        have hpeel := hCpeel D (j - l) (Nat.sub_le j l) 0 (by omega) P.1 P.2 y hyK
        have h0eq : (iteratedCovGrad g r s 0 D) = D :=
          DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) (M := M) g r s D
        rw [h0eq] at hpeel
        -- Reindex `0 + i ↦ i` in the peeling sum.
        have hreindex : (∑ i ∈ Finset.range ((j - l) + 1),
              zeroContentR (I := I) (M := M) g r (s + (0 + i))
                (iteratedCovGrad g r s (0 + i) D) α y) =
            ∑ i ∈ Finset.range ((j - l) + 1),
              zeroContentR (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i D) α y := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          congr 1 <;> rw [Nat.zero_add]
        rw [hreindex] at hpeel
        -- Convert the sum of `zeroContentR (∇^i D)` to fibre norms.
        refine le_trans hpeel ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn
        -- `∑_{i≤j-l} zeroContentR (∇^i D) ≤ Cfibmax · fibSum`.
        have hstep : ∀ i ∈ Finset.range ((j - l) + 1),
            zeroContentR (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i D) α y ≤
              Cfibmax *
                (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                ‖(iteratedCovGrad g r s i D).toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
          intro i hi
          have hij : i ≤ j := by
            have := Finset.mem_range.mp hi; omega
          have hib := hCfib i (iteratedCovGrad g r s i D) hyK
          refine le_trans hib ?_
          letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
          exact mul_le_mul_of_nonneg_right
            (Finset.le_sup' Cfib (Finset.mem_range.mpr (by omega))) (norm_nonneg _)
        calc (∑ i ∈ Finset.range ((j - l) + 1),
              zeroContentR (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i D) α y)
            ≤ ∑ i ∈ Finset.range ((j - l) + 1),
                Cfibmax *
                  (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                  ‖(iteratedCovGrad g r s i D).toSection
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) :=
              Finset.sum_le_sum hstep
          _ = Cfibmax * ∑ i ∈ Finset.range ((j - l) + 1),
                (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                ‖(iteratedCovGrad g r s i D).toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖) := by
              rw [Finset.mul_sum]
          _ ≤ Cfibmax * fibSum := by
              refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
              rw [hfibSum_def]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
              · intro i hi
                exact Finset.mem_range.mpr
                  (lt_of_lt_of_le (Finset.mem_range.mp hi)
                    (Nat.succ_le_succ (Nat.sub_le j l)))
              · letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
                exact norm_nonneg _
      -- Combine.
      have hchoose_nn : 0 ≤ (j.choose l : ℝ) := by positivity
      have hraw_l_nn : 0 ≤ ‖iteratedFDerivWithin ℝ (j - l) raw
          (chartTargetEuclid (I := I) (M := M) α) y‖ := norm_nonneg _
      have h1 : (j.choose l : ℝ) *
          ‖iteratedFDerivWithin ℝ l ρ
            (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          (j.choose l : ℝ) * Cpou :=
        mul_le_mul_of_nonneg_left hρ_l hchoose_nn
      have h2 : (j.choose l : ℝ) *
            ‖iteratedFDerivWithin ℝ l ρ
              (chartTargetEuclid (I := I) (M := M) α) y‖ *
            ‖iteratedFDerivWithin ℝ (j - l) raw
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
          ((j.choose l : ℝ) * Cpou) * (Cpeel * Cfibmax * fibSum) :=
        mul_le_mul h1 hraw_l hraw_l_nn (by positivity)
      have h3 : ((j.choose l : ℝ) * Cpou) * (Cpeel * Cfibmax * fibSum) =
          (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) := by ring
      exact h3 ▸ h2
    have hsum_choose : (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    have hstep_sum :
        (∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) *
              ‖iteratedFDerivWithin ℝ l ρ (chartTargetEuclid (I := I) (M := M) α) y‖ *
              ‖iteratedFDerivWithin ℝ (j - l) raw
                (chartTargetEuclid (I := I) (M := M) α) y‖) ≤
          ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) * Cpou * (Cpeel * Cfibmax * fibSum) :=
      Finset.sum_le_sum hbound_term
    refine hstep_sum.trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum_choose]; ring
  · -- Off the kernel: the chart component vanishes in a neighbourhood, so the
    -- derivative is zero.
    have h_evZero : tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 =ᶠ[nhds y]
        (fun _ => (0 : ℝ)) := by
      have hKclosed : IsClosed (chartPouKernel (I := I) (M := M) α) :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      filter_upwards [hKclosed.isOpen_compl.mem_nhds hyK] with z hz
      exact tensorChartComponent_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s D α P.1 P.2 hz
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_evZero j).self_of_nhds,
      iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-chart all-order uniform Cauchy property of the canonical Euclidean chart
components.**

Let `F n : SmoothCcTensor g r s` be a sequence whose spectral norms `‖(F n).toHs(2k)‖`
are Cauchy in every order `k`. Then for each chart center `α : M` and each component
multi-index `P : TensorCompIdx r s`, the canonical Euclidean chart components
`tensorChartComponent g r s (F n) α P.1 P.2 : EuclN → ℝ`
(the partition-of-unity-weighted chart-frame scalar component pushed to the Euclidean
chart target) are uniformly Cauchy in `Cᵐ` for every order `m`, over all of `EuclN`.

This is the genuine analytic core of the keystone: it combines the pointwise
reverse-Christoffel order-peeling bound (the `iteratedFDeriv` of a chart-pushed
component is bounded, up to uniform Christoffel corrections, by the order-`0` content
of the iterated covariant gradients on the compact partition-of-unity kernel) with the
unconditional `Cᵐ` tensor Sobolev embedding that converts the per-order spectral
Cauchy hypothesis into pointwise `Cᵐ`-Cauchy data of the components. Off the compact
kernel every component vanishes together with all its derivatives, so the bound is
global on `EuclN`. -/
theorem tensorChartComponent_allOrder_uniformCauchy
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (j : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
      ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2) y -
          iteratedFDeriv ℝ j
            (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) y‖ ≤ ε := by
  classical
  -- Choose a spectral order `k` with `2k > dim + 2j`, so the `Cʲ` tensor Sobolev
  -- embedding applies.
  set n : ℕ := Module.finrank ℝ E with hn_def
  set k : ℕ := n + 2 * j + 1 with hk_def
  have h_super : 2 * k > n + 2 * j := by rw [hk_def]; omega
  -- The all-order fibre-norm constant for the chart-component derivative bound.
  obtain ⟨Cder, hCder_nn, hCder⟩ :=
    exists_iteratedFDeriv_chartComponent_le_fiberNorm_sum (I := I) (M := M) g r s α P j
  -- The unconditional `Cʲ` tensor Sobolev embedding (fibre side).
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_toSobolev_embedding_Cm_unconditional
      (I := I) (M := M) g r s k j h_super
  -- The `toHs(2k)`-Cauchy hypothesis at order `k`.
  have hF_cauchy_k := Metric.cauchySeq_iff.mp (hF_cauchy k)
  set δ : ℝ := ε / (Cder * Cemb + 1) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  obtain ⟨N, hN⟩ := hF_cauchy_k δ hδ_pos
  refine ⟨N, fun n' n'' hn' hn'' y => ?_⟩
  -- The difference section.
  set D : SmoothCcTensor g r s := F n' - F n'' with hD_def
  -- Components are linear: `chartComponent (F n') - chartComponent (F n'') = chartComponent D`.
  have h_comp_sub :
      (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 -
          tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) =
      tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2 := by
    have hsub : D = F n' + (-1 : ℝ) • F n'' := by
      rw [hD_def, neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, tensorChartComponent_add (I := I) (M := M) g r s (F n') ((-1 : ℝ) • F n'') α P.1 P.2,
      tensorChartComponent_smul (I := I) (M := M) g r s (-1 : ℝ) (F n'') α P.1 P.2]
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  -- The derivative of the difference is the difference of derivatives.
  have h_iter_sub :
      iteratedFDeriv ℝ j
          (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) y -
        iteratedFDeriv ℝ j
          (tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) y =
      iteratedFDeriv ℝ j (tensorChartComponent (I := I) (M := M) g r s D α P.1 P.2) y := by
    have hcd1 : ContDiff ℝ (j : ℕ∞)
        (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) :=
      (tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n') α P.1 P.2).of_le
        (by exact_mod_cast le_top)
    have hcd2 : ContDiff ℝ (j : ℕ∞)
        (tensorChartComponent (I := I) (M := M) g r s (F n'') α P.1 P.2) :=
      (tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n'') α P.1 P.2).of_le
        (by exact_mod_cast le_top)
    rw [← iteratedFDeriv_sub_apply (hcd1.contDiffAt) (hcd2.contDiffAt), h_comp_sub]
  rw [h_iter_sub]
  -- Apply the derivative bound and the embedding.
  refine le_trans (hCder D y) ?_
  -- The fibre-norm sum is bounded by `Cemb · ‖D.toHs(2k)‖` at the point.
  have hemb := hCemb D ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  set N2k : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) D‖ with hN2k_def
  have hN2k_nn : 0 ≤ N2k := norm_nonneg _
  -- `‖D.toHs(2k)‖ < δ` from the Cauchy hypothesis (`D = F n' - F n''`).
  have hD_small : N2k < δ := by
    rw [hN2k_def, hD_def,
      DifferentialGeometry.PDE.RicciFlow.SmoothCcTensor.toHs_sub (g := g) (2 * k) (F n') (F n'')]
    have := hN n' hn' n'' hn''
    rwa [dist_eq_norm] at this
  have h_fibSum_le :
      (∑ i ∈ Finset.range (j + 1),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
        ‖(iteratedCovGrad g r s i D).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖)) ≤ Cemb * N2k :=
    hemb
  calc Cder * (∑ i ∈ Finset.range (j + 1),
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + i) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
          ‖(iteratedCovGrad g r s i D).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖))
      ≤ Cder * (Cemb * N2k) :=
        mul_le_mul_of_nonneg_left h_fibSum_le hCder_nn
    _ = (Cder * Cemb) * N2k := by ring
    _ ≤ (Cder * Cemb) * δ := by
        refine mul_le_mul_of_nonneg_left hD_small.le ?_
        positivity
    _ ≤ ε := by
        rw [hδ_def]
        have hden_pos : 0 < Cder * Cemb + 1 := by positivity
        rw [mul_div_assoc', div_le_iff₀ hden_pos]
        have hCC_nn : 0 ≤ Cder * Cemb := by positivity
        nlinarith [mul_nonneg hCC_nn hε.le]

/-- **The per-chart common `C^∞` limit of the chart-pushed scalar components,
compactly supported strictly inside the chart target.**

From the all-order uniform-Cauchy property
`chartComponentScalar_chartPushed_allOrder_uniformCauchy`, the Euclidean
uniform-limit-of-derivatives machinery produces, for each chart center `α` and
component multi-index `P`, a function `u_∞ : EuclN → ℝ` that is `C^∞` on `EuclN`,
compactly supported with topological support strictly inside the open chart target,
and is the pointwise `Cᵐ` limit (every order) of the chart-pushed raw components of
`F n`. -/
theorem exists_chartComponent_limit_smooth_compactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) :
    ∃ u : TensorCompIdx (E := E) r s → EuclN → ℝ,
      (∀ P, ContDiffOn ℝ ∞ (u P) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ P, HasCompactSupport (u P) ∧
        tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) ∧
      (∀ (P : TensorCompIdx (E := E) r s) (y : EuclN),
        Filter.Tendsto
          (fun n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y)
          Filter.atTop (𝓝 (u P y))) := by
  classical
  -- Each component's sequence of canonical Euclidean chart functions.
  set gseq : TensorCompIdx (E := E) r s → ℕ → EuclN → ℝ :=
    fun P n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 with hgseq_def
  -- The all-order uniform Cauchy property, phrased per component / order.
  have hcauchy : ∀ (P : TensorCompIdx (E := E) r s) (j : ℕ),
      ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j (gseq P n) y - iteratedFDeriv ℝ j (gseq P n') y‖ ≤ ε := by
    intro P j ε hε
    exact tensorChartComponent_allOrder_uniformCauchy
      (I := I) (M := M) g r s F hF_cauchy α P j ε hε
  -- The `C^0` uniform Cauchy hypothesis feeding `cauchyLimitFun`.
  have hcauchy0 : ∀ (P : TensorCompIdx (E := E) r s),
      ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ y : EuclN,
        ‖gseq P n y - gseq P n' y‖ ≤ ε := by
    intro P ε hε
    obtain ⟨N, hN⟩ := hcauchy P 0 ε hε
    refine ⟨N, fun n n' hn hn' y => ?_⟩
    have hraw := hN n n' hn hn' y
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at hraw
    exact hraw
  -- The smoothness of each member function.
  have hsmooth : ∀ (P : TensorCompIdx (E := E) r s) (n : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) (gseq P n) := by
    intro P n
    exact tensorChartComponent_contDiff' (I := I) (M := M) g r s (F n) α P.1 P.2
  -- The candidate limit, component by component.
  set u : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun P => cauchyLimitFun (d := Module.finrank ℝ E)
      (gseq P) (hcauchy0 P) with hu_def
  refine ⟨u, ?_, ?_, ?_⟩
  · -- `C^∞` on the chart target, in fact globally `C^∞`.
    intro P
    have hcontDiff : ContDiff ℝ (⊤ : ℕ∞) (u P) := by
      rw [contDiff_infty]
      intro m
      exact (iteratedFDeriv_cauchyLimitFun_eq (d := Module.finrank ℝ E)
        m (hsmooth P) (hcauchy0 P) (fun j _ => hcauchy P j)).1
    exact hcontDiff.contDiffOn
  · -- Compact support inside the chart target: the limit vanishes off the
    -- compact partition-of-unity kernel, hence so does its closure-support.
    intro P
    have hsupp_subset : Function.support (u P) ⊆ chartPouKernel (I := I) (M := M) α := by
      intro z hz
      by_contra hzk
      -- Off the kernel, every member vanishes, so the pointwise limit vanishes.
      have hzero : ∀ n, gseq P n z = 0 := by
        intro n
        have hsub := tensorChartComponent_tsupport_subset_chartPouKernel
          (I := I) (M := M) g r s (F n) α P.1 P.2
        exact image_eq_zero_of_notMem_tsupport (fun hmem => hzk (hsub hmem))
      have htends : Filter.Tendsto (fun n => gseq P n z) Filter.atTop (𝓝 (u P z)) :=
        cauchyLimitFun_tendsto (d := Module.finrank ℝ E)
          (hcauchy0 P) z
      have hlim0 : u P z = 0 :=
        tendsto_nhds_unique htends (by simpa only [hzero] using tendsto_const_nhds)
      exact hz hlim0
    have htsupp_subset : tsupport (u P) ⊆ chartPouKernel (I := I) (M := M) α :=
      closure_minimal hsupp_subset
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
    refine ⟨?_, htsupp_subset.trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)⟩
    exact HasCompactSupport.of_support_subset_isCompact
      (chartPouKernel_isCompact (I := I) (M := M) α) hsupp_subset
  · -- The pointwise limit identification of the chart components.
    intro P y
    exact cauchyLimitFun_tendsto (d := Module.finrank ℝ E) (hcauchy0 P) y


/-- **The per-chart assembled smooth section** built from the common `C^∞` limits of
the chart-pushed components, supported in the chart-`α` source. -/
def chartLimitSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1

/-- **The global smooth limit section.**

The chart-atlas assembly of the per-chart smooth limit sections: the finite sum
over the chart-atlas partition-of-unity index of the per-chart assembled sections.
The partition-of-unity weight is already carried inside each per-chart component
limit `u_∞,α,P` (the canonical chart component `tensorChartComponent` is the
partition-of-unity-weighted chart-frame projection), so the assembled sections are
summed directly — exactly as the eigenvector smooth representative `eigenvectorSmooth`
sums its per-chart pieces. This is the smooth representative whose `L²` class is the
abstract limit `u`. -/
def globalLimitSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n))) :
    SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    chartLimitSection (I := I) (M := M) g r s F hF_cauchy α

/-- The chosen per-chart common `C^∞` limit functions of the chart-pushed
components. -/
private def chartLimitComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) : TensorCompIdx (E := E) r s → EuclN → ℝ :=
  (exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose

private lemma chartLimitComp_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  ((exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P).2

private lemma chartLimitComp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (y : EuclN) :
    Tendsto
      (fun n => tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y)
      atTop (𝓝 (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y)) :=
  (exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.2 P y

/-- **Uniform convergence of the chart components to the chosen limit.** The
order-`0` all-order uniform-Cauchy bound plus the pointwise limit promote the
pointwise convergence `tensorChartComponent (F n) α P → chartLimitComp α P` to a
*uniform* convergence over all of `EuclN`: for every `ε > 0` there is an `N` such
that `‖tensorChartComponent (F n) α P y - chartLimitComp α P y‖ ≤ ε` for all
`n ≥ N` and all `y`. -/
private lemma chartLimitComp_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y : EuclN,
      ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
        chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖ ≤ ε := by
  obtain ⟨N, hN⟩ := tensorChartComponent_allOrder_uniformCauchy
    (I := I) (M := M) g r s F hF_cauchy α P 0 (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn y => ?_⟩
  -- `‖g_n y - g_{n'} y‖ ≤ ε/2` for `n, n' ≥ N`, and `g_{n'} y → limit`.
  have hcauchy0 : ∀ n', N ≤ n' →
      ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
        tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 y‖ ≤ ε / 2 := by
    intro n' hn'
    have hraw := hN n n' hn hn' y
    rwa [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
      Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at hraw
  -- Take the limit `n' → ∞`.
  have htends :
      Tendsto (fun n' =>
        ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
          tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2 y‖)
        atTop (𝓝 ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
          chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_const_nhds.sub
        (chartLimitComp_tendsto (I := I) (M := M) g r s F hF_cauchy α P y))
  have hlim_le : ‖tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 y -
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y‖ ≤ ε / 2 :=
    le_of_tendsto htends
      (Filter.eventually_atTop.mpr ⟨N, fun n' hn' => hcauchy0 n' hn'⟩)
  linarith

/-- The chosen limit function is continuous: it is `C^∞` on the open chart target
and supported strictly inside it. -/
private lemma chartLimitComp_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Continuous (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) := by
  have hcdOn : ContDiffOn ℝ ∞
      (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1 P
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine continuous_of_tsupport (fun x hx => ?_)
  have hxO : x ∈ chartTargetEuclid (I := I) (M := M) α :=
    chartLimitComp_tsupport (I := I) (M := M) g r s F hF_cauchy α P hx
  exact ((hcdOn.contDiffAt (hO.mem_nhds hxO)).continuousAt)

/-- The chosen limit function has compact support. -/
private lemma chartLimitComp_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) :=
  ((exists_chartComponent_limit_smooth_compactSupport
    (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P).1

/-- The chosen limit function is `MemLp 2` of the chart-`L²` reference measure: it
is continuous with compact support. -/
private lemma chartLimitComp_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) 2
      (chartL2Measure (I := I) (M := M) α) := by
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure]; infer_instance
  exact Continuous.memLp_of_hasCompactSupport
    (chartLimitComp_continuous (I := I) (M := M) g r s F hF_cauchy α P)
    (chartLimitComp_hasCompactSupport (I := I) (M := M) g r s F hF_cauchy α P)

/-- **`L²` convergence of the chart components to the chosen limit.** The
chart-pushed components `tensorChartComponent (F n) α P`, which converge uniformly
to the chosen limit `chartLimitComp α P` and share the common compact support
`chartPouKernel α ∪ tsupport(chartLimitComp α P)`, converge to it as `L²` classes
in `Lp ℝ 2 (chartL2Measure α)`. -/
private lemma chartComponent_toLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Tendsto
      (fun n => (tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
        (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2))
      atTop (𝓝 ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
        (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P))) := by
  classical
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure]; infer_instance
  set μ : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμ_def
  -- The common compact support.
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α ∪
    tsupport (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) with hK_def
  have hK_compact : IsCompact K :=
    (chartPouKernel_isCompact (I := I) (M := M) α).union
      (chartLimitComp_hasCompactSupport (I := I) (M := M) g r s F hF_cauchy α P)
  have hμK_lt : μ K < ⊤ := by
    rw [hμ_def, chartL2Measure]
    exact lt_of_le_of_lt (Measure.restrict_apply_le _ K) hK_compact.measure_lt_top
  set c : ℝ≥0∞ := (μ K) ^ ((2 : ℝ≥0∞).toReal⁻¹) with hc_def
  have hc_lt : c < ⊤ := by
    rw [hc_def]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hμK_lt.ne
  -- The difference's support lies in `K`.
  set dseq : ℕ → EuclN → ℝ := fun n =>
    tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2 -
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P with hdseq_def
  have hdsupp : ∀ n, Function.support (dseq n) ⊆ K := by
    intro n z hz
    rw [Function.mem_support] at hz
    by_contra hzK
    apply hz
    rw [hdseq_def]
    simp only [Pi.sub_apply]
    rw [hK_def, Set.mem_union, not_or] at hzK
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hzK.1
        (tensorChartComponent_tsupport_subset_chartPouKernel
          (I := I) (M := M) g r s (F n) α P.1 P.2 hmem)),
      image_eq_zero_of_notMem_tsupport hzK.2, sub_zero]
  -- The `eLpNorm` of the difference is bounded by `c · ofReal εₙ`, with `εₙ → 0`.
  have heLp_le : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      eLpNorm (dseq n) 2 μ ≤ c * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := chartLimitComp_uniform (I := I) (M := M) g r s F hF_cauchy α P ε hε
    refine ⟨N, fun n hn => ?_⟩
    -- Restrict to `K`, where the function is bounded by `ε`.
    have hrestrict : eLpNorm (dseq n) 2 (μ.restrict K) = eLpNorm (dseq n) 2 μ :=
      eLpNorm_restrict_eq_of_support_subset (hdsupp n)
    have hbound_ae : ∀ᵐ z ∂(μ.restrict K), ‖dseq n z‖ ≤ ε := by
      filter_upwards with z
      rw [hdseq_def]
      exact hN n hn z
    have hle := eLpNorm_le_of_ae_bound (p := 2) hbound_ae
    rw [hrestrict] at hle
    refine hle.trans ?_
    rw [hc_def, Measure.restrict_apply_univ]
  -- Hence `eLpNorm (dseq n) 2 μ → 0`.
  have htendsto_eLp : Tendsto (fun n => eLpNorm (dseq n) 2 μ) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with hεtop | hεtop
    · -- `ε = ⊤`: trivial.
      obtain ⟨N, hN⟩ := heLp_le 1 one_pos
      exact ⟨N, fun n hn => hεtop ▸ le_top⟩
    rcases eq_or_lt_of_le (zero_le c) with hc0 | hc0
    · -- `c = 0`: the bound is `0`.
      obtain ⟨N, hN⟩ := heLp_le 1 one_pos
      refine ⟨N, fun n hn => le_trans (hN n hn) ?_⟩
      rw [← hc0, zero_mul]
      exact zero_le _
    · -- `c > 0`: pick a real `δ` with `c · ofReal δ ≤ ε`.
      have hc_ne : c ≠ ⊤ := hc_lt.ne
      have hdiv_ne_top : ε / c ≠ ⊤ := by
        rw [Ne, ENNReal.div_eq_top]; push_neg
        exact ⟨fun _ => hc0.ne', fun h => absurd h hεtop⟩
      have hδ_pos : 0 < (ε / c).toReal :=
        ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hε.ne', hc_ne⟩) hdiv_ne_top
      obtain ⟨N, hN⟩ := heLp_le ((ε / c).toReal) hδ_pos
      refine ⟨N, fun n hn => le_trans (hN n hn) ?_⟩
      rw [ENNReal.ofReal_toReal hdiv_ne_top, ENNReal.mul_div_cancel hc0.ne' hc_ne]
  -- Convert to convergence of the `L²` classes via `edist_toLp_toLp`.
  rw [tendsto_iff_edist_tendsto_0]
  have hedist_eq : ∀ n,
      edist ((tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2))
        ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P)) =
        eLpNorm (dseq n) 2 μ := by
    intro n
    rw [Lp.edist_toLp_toLp]
  simp only [hedist_eq]
  exact htendsto_eLp

/-- **The abstract limit's chart component is the chosen limit (Lemma K).** For
every chart center `α` and component multi-index `P`, the canonical chart-`α`
`P`-component of the abstract `L²` limit `u` agrees almost everywhere (for the
chart-`α` `L²` reference measure) with the chosen per-chart `C^∞` limit
`chartLimitComp α P`. Both are the `L²` limit of the chart components
`tensorChartComponent (F n) α P`: the abstract side by continuity of
`tensorL2ChartComponentCLM` along `hF_L2`, the chosen side by the uniform
(hence `L²`) convergence of the chart components. -/
private lemma tensorL2ChartComponent_eq_chartLimitComp_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P := by
  classical
  -- The chart components of `F n` as `L²` classes equal the canonical chart components.
  have h_chartEq : ∀ n,
      tensorL2ChartComponent (I := I) (M := M) g r s (F n : TensorL2 r s g) α P =
        (tensorChartComponent_memLp (I := I) (M := M) g r s (F n) α P.1 P.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s (F n) α P.1 P.2) :=
    fun n => tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s (F n) α P
  -- Side 1: the chosen-limit side, via uniform-`L²` convergence.
  have h_lim_chosen :
      Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
          (F n : TensorL2 r s g) α P)
        atTop (𝓝 ((chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P))) := by
    simp only [h_chartEq]
    exact chartComponent_toLp_tendsto (I := I) (M := M) g r s F hF_cauchy α P
  -- Side 2: the abstract side, via continuity of the chart-component CLM along `hF_L2`.
  have h_lim_abstract :
      Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
          (F n : TensorL2 r s g) α P)
        atTop (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s u α P)) := by
    have hcont := continuous_tensorL2ChartComponent (I := I) (M := M) g r s α P
    exact (hcont.tendsto u).comp hF_L2
  -- Uniqueness of limits in the `L²` chart space.
  have h_eq :
      tensorL2ChartComponent (I := I) (M := M) g r s u α P =
        (chartLimitComp_memLp (I := I) (M := M) g r s F hF_cauchy α P).toLp
          (chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P) :=
    tendsto_nhds_unique h_lim_abstract h_lim_chosen
  rw [h_eq]
  exact MemLp.coeFn_toLp _

/-- The raw chart-`α` frame component of `chartLimitSection α`, read at the chart
preimage of a chart-target point `y`, is the chosen limit `chartLimitComp α P`. -/
private lemma tensorChartComponentRaw_chartLimitSection_self
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chartLimitComp (I := I) (M := M) g r s F hF_cauchy α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 P hy

/-- The underlying section of `chartLimitSection α` vanishes off the chart-`α`
source. -/
private lemma chartLimitSection_toSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α).toSection x = 0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.1
    (exists_chartComponent_limit_smooth_compactSupport
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2.1 hx

/-- The raw chart-`β` frame component of `chartLimitSection α` vanishes off the
chart-`α` source. -/
private lemma tensorChartComponentRaw_chartLimitSection_eq_zero_off_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P.1 P.2 x = 0 := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  have hsec : (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α).toSection x = 0 :=
    chartLimitSection_toSection_eq_zero_off_source (I := I) (M := M) g r s F hF_cauchy α hx
  rw [tensorChartComponentRaw_def, tensorTrivProj, hsec,
    ContinuousLinearMap.map_zero, map_zero]

open Classical in
/-- For a chart-`β`-source point `x`, the raw chart-`β` frame component of
`chartLimitSection α` is the `(r, s)`-tensor transformation-law sum when `x` lies in
the chart-`α` source, and `0` otherwise. -/
private lemma raw_chartLimitSection_eq_ite
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
      α β P₀ ⟨hxα, hxβ⟩
  · rw [if_neg hxα]
    exact tensorChartComponentRaw_chartLimitSection_eq_zero_off_source
      (I := I) (M := M) g r s F hF_cauchy α β P₀ hxα

open Classical in
/-- **The canonical Euclidean chart-`β` component of `chartLimitSection α`.** As a
function on the chart target of `β`, it equals almost everywhere the chart-pushed
partition-of-unity weight of `β` times the chart-`β` push of the function which is
the transformation-law sum on the chart-`α` source and `0` off it. -/
private lemma chartLimitSection_tensorL2ChartComponent_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α) β P₀
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_isOpen (I := I) (M := M) β).measurableSet
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  rw [hy_coe]
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
    β P₀.1 P₀.2 hy]
  congr 1
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)
              α Q.1 Q.2 x
        else 0) hy]
  exact raw_chartLimitSection_eq_ite (I := I) (M := M) g r s F hF_cauchy
    α β P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)

/-- **The `L²` class of the global limit section equals the abstract limit `u`.**

By `tensorL2_eq_of_chartComponent_eq`, it suffices to check that the canonical
`L²` chart components of the assembled global section agree, in every chart `α` and
every component direction `P₀`, with those of `u`. Both equal the `L²` limit of the
chart components of `F n`: the global section's components are the `Cᵐ` (hence `L²`)
limits of the chart-pushed components of `F n` (by the assembly recovery identity and
`exists_chartComponent_limit_smooth_compactSupport`), while `u`'s chart components are
the `L²` limits of those of `F n` by continuity of `tensorL2ChartComponentCLM` along
`hF_L2`. -/
theorem globalLimitSection_toL2_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u)) :
    (globalLimitSection (I := I) (M := M) g r s F hF_cauchy : TensorL2 r s g) = u :=
  sorry

/-- **`Cᵏ`-Banach completeness keystone of the smooth-tensor space.**

A sequence of smooth compactly-supported tensors that is Cauchy in *every* spectral
order `H^{2k}` (`SmoothCcTensor.toHs (2k)`) and converges in `L²` to an abstract limit
`u : TensorL2 r s g` has its `L²` limit `u` realised by a genuine smooth section
`T : SmoothCcTensor g r s` with `↑T = u`.

The smooth inclusion `SmoothCcTensor ↪ TensorL2` is only `DenseRange`, so the limit
`u` is a priori only an abstract `L²` element; the keystone exhibits an honest smooth
representative. -/
theorem smoothCcTensor_limit_of_allOrders_toHs_cauchy
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n)))
    (hF_L2 : Tendsto (fun n => (F n : TensorL2 r s g)) atTop (𝓝 u)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u :=
  ⟨globalLimitSection (I := I) (M := M) g r s F hF_cauchy,
    globalLimitSection_toL2_eq (I := I) (M := M) g r s u F hF_cauchy hF_L2⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
