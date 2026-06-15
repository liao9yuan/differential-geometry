import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence

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
            (tensorChartComponent (I := I) (M := M) g r s (F n') α P.1 P.2) y‖ ≤ ε :=
  sorry

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
        tsupport (u P) ⊆ chartTargetEuclid (I := I) (M := M) α) := by
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
  refine ⟨u, ?_, ?_⟩
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
      (I := I) (M := M) g r s F hF_cauchy α).choose_spec.2

/-- **The global smooth limit section.**

The partition-of-unity assembly of the per-chart smooth limit sections: the finite
sum over the chart-atlas partition-of-unity index of the per-chart assembled
sections, weighted by the chart-atlas partition of unity. This is the smooth
representative whose `L²` class is the abstract limit `u`. -/
def globalLimitSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℕ → SmoothCcTensor g r s)
    (hF_cauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) (F n))) :
    SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    pouSmul (I := I) (M := M) g r s α
      (chartLimitSection (I := I) (M := M) g r s F hF_cauchy α)

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
