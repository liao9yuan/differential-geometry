import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact

/-!
# The spectral → chart-local joint-continuity bridge for the realized metric

The DeTurck–Ricci interior-regularity bundle
(`deturck_ricci_parabolic_interior_regularity`,
`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`) asks for the chart-local
`ContinuousOn`/`ContMDiffOn` data of the realized DeTurck metric family `g_DT`,
*jointly* in time and space.  The interior spectral smoothing
(`solField_into_all_tensorHs_interior`,
`Analysis/Spectral/Intrinsic/HeatSemigroup/ParabolicInteriorSmoothing.lean`) and the
supercritical Sobolev embedding `H^{2k} ↪ C⁰`
(`tensorPouSobolevHilbert_embedding_Ck`) deliver the *time-continuity into every
spatial Sobolev scale*; what is missing — and what this file builds — is the upgrade
from "continuous in time into `Hˢ`" to the **joint `(t, x)` continuity** of the
pointwise chart-Gram entries.

The mechanism is the classical "continuous-in-one-variable + uniform-modulus-in-the-
other ⟹ jointly continuous" argument, supplied here in two reusable, manifold-free
forms (`joint_continuousOn_of_slice_normModulus` and its locally-uniform-on-an-open-
set corollary `joint_continuousOn_open_of_slice_normModulus`), and then specialised
to the realized metric.

## The uniform spatial modulus

For a smooth-section family `T_s : ℝ → SmoothCcTensor g_bg 0 2` whose order-`2k`
Sobolev image `t ↦ (T_s t).toHs (2k)` is continuous, the symmetric bilinear
extraction obeys, at every point and against the chart frame, the embedding bound
`|ccTensorBilinSymm g_bg (T_s t − T_s t') x e_i e_j|
   ≤ C · √(g_bg x e_i e_i) · √(g_bg x e_j e_j) · ‖(T_s t).toHs − (T_s t').toHs‖`
(`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm` applied to the section difference,
`ccTensorBilinSymm_sub`, `SmoothCcTensor.toHs_sub`).  On any compact set the chart-
frame `g_bg`-lengths are bounded, so the modulus is uniform in `x`, and the time-
continuity of `t ↦ (T_s t).toHs (2k)` closes the joint upgrade.

## Main results

* `joint_continuousOn_of_slice_normModulus` — abstract joint-continuity engine: a
  real-valued `f : ℝ × X → ℝ` (`X` topological), continuous in `x` on each time
  slice, with a normed-control time modulus uniform on `K`, is `ContinuousOn` on
  `J ×ˢ K`.
* `joint_continuousOn_open_of_slice_normModulus` — its locally-compact corollary on
  an open base set `U`, where the modulus is required only uniformly on each compact
  subset of `U`.
* `exists_chartGram_realized_uniform_modulus` — the uniform-in-space time modulus of
  the realized chart-Gram entry over a compact subset of the chart base set, off the
  `H^{2k} ↪ C⁰` embedding and `ccTensorBilinSymm_sub`.
* `chartGram_realizedMetric_jointContinuousOn` — the chart-Gram entry of a metric
  family realized as `g_bg + ccTensorBilinSymm (T_s ·)` is jointly `(t, x)`
  continuous on `J ×ˢ baseSet`, from the time-continuity of `t ↦ (T_s t).toHs (2k)`.
* `chartGram_realizedMetric_jointContMDiffOn` — the interior `C∞` arm (conjunct (4)): the
  chart-Gram entry is jointly `(t, x)`-`C∞` from the joint smoothness of the metric
  inner-product `Hom`-section, via `ContMDiffOn.clm_bundle_apply₂` over base map `Prod.snd`.
* `chartGramOnE_realizedMetric_jointContinuousOn` — the `chartGramOnE` `C⁰` arm
  (conjunct (6)): the chart-pulled-back Gram entry is jointly continuous on the chart source,
  the chart round-trip collapsing it to `chartGram_realizedMetric_jointContinuousOn`.
* `iteratedFDeriv_zero_chartGramOnE_realizedMetric_jointContinuousOn` — the `k = 0` arm of the
  spatial-jet conjunct (7).  The higher jets `k ∈ {1, 2}` need a partial-iteratedFDeriv ↔
  joint-regularity bridge that is absent in Mathlib and in this library (the jet wall).
-/

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Abstract joint-continuity engine (normed time-modulus).**

Let `f : ℝ × X → ℝ` with `X` a topological space.  Suppose:

* on each time slice `t ∈ J`, `x ↦ f (t, x)` is continuous on `K` (`hslice`);
* there is a normed-space-valued control `ψ : ℝ → V`, continuous on `J` (`hψ`), and a
  constant `B` such that `|f (t, x) − f (t', x)| ≤ B · ‖ψ t − ψ t'‖` for all
  `t, t' ∈ J` and `x ∈ K` (`hmod`) — the time-modulus is *uniform in `x ∈ K`*.

Then `f` is jointly continuous on `J ×ˢ K`.

The proof is the textbook triangle split
`f (t, x) − f (t₀, x₀) = (f (t, x) − f (t₀, x)) + (f (t₀, x) − f (t₀, x₀))`: the first
term is `≤ B · ‖ψ t − ψ t₀‖ → 0` by the uniform modulus and the continuity of `ψ`, the
second `→ 0` by the slice continuity at `x₀`; the product neighbourhood basis
`nhdsWithin_prod_eq` packages the two one-variable limits. -/
theorem joint_continuousOn_of_slice_normModulus
    {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V]
    (f : ℝ × X → ℝ) {J : Set ℝ} {K : Set X} (B : ℝ) (ψ : ℝ → V)
    (hslice : ∀ t ∈ J, ContinuousOn (fun x => f (t, x)) K)
    (hψ : ContinuousOn ψ J)
    (hmod : ∀ t ∈ J, ∀ t' ∈ J, ∀ x ∈ K,
      |f (t, x) - f (t', x)| ≤ B * ‖ψ t - ψ t'‖) :
    ContinuousOn f (J ×ˢ K) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, hx₀⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds, nhdsWithin_prod_eq]
  intro ε hε
  set B' : ℝ := max B 0 with hB'_def
  have hmod' : ∀ t ∈ J, ∀ t' ∈ J, ∀ x ∈ K,
      |f (t, x) - f (t', x)| ≤ B' * ‖ψ t - ψ t'‖ := fun t ht t' ht' x hx =>
    (hmod t ht t' ht' x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hxcont : ContinuousWithinAt (fun x => f (t₀, x)) K x₀ := hslice t₀ ht₀ x₀ hx₀
  have hx_ev : ∀ᶠ x in 𝓝[K] x₀, |f (t₀, x) - f (t₀, x₀)| < ε / 2 := by
    have h := hxcont.tendsto
    rw [Metric.tendsto_nhds] at h
    filter_upwards [h (ε / 2) (by positivity)] with x hx
    rw [Real.dist_eq] at hx; simpa using hx
  have hψcont : ContinuousWithinAt ψ J t₀ := hψ t₀ ht₀
  have ht_ev : ∀ᶠ t in 𝓝[J] t₀, B' * ‖ψ t - ψ t₀‖ < ε / 2 := by
    have h := hψcont.tendsto
    rw [Metric.tendsto_nhds] at h
    filter_upwards [h (ε / (2 * (B' + 1))) (by positivity)] with t ht
    rw [dist_eq_norm] at ht
    have hstep1 : B' * ‖ψ t - ψ t₀‖ ≤ (B' + 1) * ‖ψ t - ψ t₀‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hstep2 : (B' + 1) * ‖ψ t - ψ t₀‖ < (B' + 1) * (ε / (2 * (B' + 1))) :=
      mul_lt_mul_of_pos_left ht (by positivity)
    have hB'_nn : (0 : ℝ) ≤ B' := le_max_right _ _
    have hne : (B' : ℝ) + 1 ≠ 0 := by positivity
    have heq : (B' + 1) * (ε / (2 * (B' + 1))) = ε / 2 := by
      field_simp
    linarith [hstep1, hstep2, heq.le, heq.ge]
  have htJ : ∀ᶠ t in 𝓝[J] t₀, t ∈ J := self_mem_nhdsWithin
  have hxK : ∀ᶠ x in 𝓝[K] x₀, x ∈ K := self_mem_nhdsWithin
  rw [Filter.eventually_prod_iff]
  refine ⟨fun t => t ∈ J ∧ B' * ‖ψ t - ψ t₀‖ < ε / 2,
    ht_ev.and htJ |>.mono (fun t h => ⟨h.2, h.1⟩),
    fun x => x ∈ K ∧ |f (t₀, x) - f (t₀, x₀)| < ε / 2,
    hx_ev.and hxK |>.mono (fun x h => ⟨h.2, h.1⟩), ?_⟩
  rintro t ⟨htJ', htmod⟩ x ⟨hxK', hxmod⟩
  rw [Real.dist_eq]
  calc |f (t, x) - f (t₀, x₀)|
      = |(f (t, x) - f (t₀, x)) + (f (t₀, x) - f (t₀, x₀))| := by ring_nf
    _ ≤ |f (t, x) - f (t₀, x)| + |f (t₀, x) - f (t₀, x₀)| := abs_add_le _ _
    _ ≤ B' * ‖ψ t - ψ t₀‖ + |f (t₀, x) - f (t₀, x₀)| := by
        gcongr; exact hmod' t htJ' t₀ ht₀ x hxK'
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

/-- **Joint-continuity engine on an open base set (locally-uniform modulus).**

The same upgrade as `joint_continuousOn_of_slice_normModulus`, but over an *open*
spatial set `U` (whose `g_bg`-frame lengths need not be globally bounded), in a
locally compact space `X`.  The uniform time-modulus is required only on each compact
subset `K ⊆ U`; joint continuity is then a local statement, proved at each point by
choosing a compact neighbourhood (`exists_compact_subset`), applying the global engine
there, and transporting the resulting `ContinuousWithinAt` to `U` along the
neighbourhood (`ContinuousWithinAt.mono_of_mem_nhdsWithin`). -/
theorem joint_continuousOn_open_of_slice_normModulus
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {V : Type*} [NormedAddCommGroup V]
    (f : ℝ × X → ℝ) {J : Set ℝ} {U : Set X} (hU : IsOpen U) (ψ : ℝ → V)
    (hslice : ∀ t ∈ J, ContinuousOn (fun x => f (t, x)) U)
    (hψ : ContinuousOn ψ J)
    (hmod : ∀ K : Set X, K ⊆ U → IsCompact K → ∃ B : ℝ,
      ∀ t ∈ J, ∀ t' ∈ J, ∀ x ∈ K, |f (t, x) - f (t', x)| ≤ B * ‖ψ t - ψ t'‖) :
    ContinuousOn f (J ×ˢ U) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, hx₀⟩
  obtain ⟨K, hK_compact, hK_int, hK_sub⟩ := exists_compact_subset hU hx₀
  obtain ⟨B, hB⟩ := hmod K hK_sub hK_compact
  have hcont_K : ContinuousOn f (J ×ˢ K) :=
    joint_continuousOn_of_slice_normModulus f B ψ
      (fun t ht => (hslice t ht).mono hK_sub) hψ hB
  refine (hcont_K (t₀, x₀) ⟨ht₀, interior_subset hK_int⟩).mono_of_mem_nhdsWithin ?_
  rw [nhdsWithin_prod_eq]
  exact Filter.prod_mem_prod self_mem_nhdsWithin
    (nhdsWithin_le_nhds
      (mem_nhds_iff.mpr ⟨interior K, interior_subset, isOpen_interior, hK_int⟩))

/-- **Uniform spatial modulus of the realized chart-Gram entry over a compact set.**

For a smooth-section family `T_s : ℝ → SmoothCcTensor g_bg 0 2`, a supercritical order
`2k > dim M + 4`, and a compact set `K ⊆ M`, there is a constant `B ≥ 0` with
`|ccTensorBilinSymm g_bg (T_s t) x e_i e_j − ccTensorBilinSymm g_bg (T_s t') x e_i e_j|
   ≤ B · ‖(T_s t).toHs (2k) − (T_s t').toHs (2k)‖`
for all `t, t'` and `x ∈ K`, with `e_i, e_j` the chart-`α` basis frame.

`B = C · (sup_{x∈K} √(g_bg x e_i e_i)) · (sup_{x∈K} √(g_bg x e_j e_j))`, where `C` is
the fixed `0`-jet `C⁰`-Sobolev embedding constant
(`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`); the chart-frame `g_bg`-lengths
are bounded on `K` by `metric_inner_chartBasisFibers_continuousOn`, the continuity of
`√`, and the extreme-value theorem `IsCompact.bddAbove_image`.  The section-difference
bound is `ccTensorBilinSymm_sub` together with `SmoothCcTensor.toHs_sub`. -/
theorem exists_chartGram_realized_uniform_modulus
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    {K : Set M} (hK : IsCompact K)
    (hK_sub : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ B : ℝ, ∀ t t' : ℝ, ∀ x ∈ K,
      |ccTensorBilinSymm (I := I) g_bg (T_s t) x
          (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x) -
        ccTensorBilinSymm (I := I) g_bg (T_s t') x
          (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x)| ≤
        B * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t) -
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t')‖ := by
  classical
  obtain ⟨C, hC_nonneg, hC⟩ :=
    gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm (I := I) (M := M) g_bg
  have hcont_len : ∀ l : Fin (Module.finrank ℝ E),
      ContinuousOn (fun x : M => Real.sqrt (g_bg.inner x
        (chartBasisVecFiber (I := I) α l x)
        (chartBasisVecFiber (I := I) α l x))) K :=
    fun l => Real.continuous_sqrt.comp_continuousOn
      ((Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn
        (I := I) (M := M) g_bg α l l).mono hK_sub)
  obtain ⟨Bi, hBi⟩ : BddAbove ((fun x : M => Real.sqrt (g_bg.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α i x))) '' K) := hK.bddAbove_image (hcont_len i)
  obtain ⟨Bj, hBj⟩ : BddAbove ((fun x : M => Real.sqrt (g_bg.inner x
      (chartBasisVecFiber (I := I) α j x)
      (chartBasisVecFiber (I := I) α j x))) '' K) := hK.bddAbove_image (hcont_len j)
  refine ⟨C * max Bi 0 * max Bj 0, fun t t' x hxK => ?_⟩
  set N : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2)
      (2 * k) (T_s t) -
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2)
      (2 * k) (T_s t')‖ with hN_def
  have hsub : ccTensorBilinSymm (I := I) g_bg (T_s t) x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) -
      ccTensorBilinSymm (I := I) g_bg (T_s t') x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) =
      ccTensorBilinSymm (I := I) g_bg (T_s t - T_s t') x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) :=
    (ccTensorBilinSymm_sub (I := I) g_bg (T_s t) (T_s t') x _ _).symm
  rw [hsub]
  have hbound := hC k hk (T_s t - T_s t') x
    (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
  have htoHs : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k)
      (T_s t - T_s t')‖ = N := by
    rw [hN_def, SmoothCcTensor.toHs_sub]
  rw [htoHs] at hbound
  have hli : Real.sqrt (g_bg.inner x (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α i x)) ≤ max Bi 0 :=
    le_trans (hBi ⟨x, hxK, rfl⟩) (le_max_left _ _)
  have hlj : Real.sqrt (g_bg.inner x (chartBasisVecFiber (I := I) α j x)
      (chartBasisVecFiber (I := I) α j x)) ≤ max Bj 0 :=
    le_trans (hBj ⟨x, hxK, rfl⟩) (le_max_left _ _)
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hCN_nn : 0 ≤ C * N := mul_nonneg hC_nonneg hN_nn
  calc |ccTensorBilinSymm (I := I) g_bg (T_s t - T_s t') x
          (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)|
      ≤ C * N *
          Real.sqrt (g_bg.inner x (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α i x)) *
          Real.sqrt (g_bg.inner x (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α j x)) := hbound
    _ ≤ C * N * max Bi 0 * max Bj 0 := by gcongr
    _ = C * max Bi 0 * max Bj 0 * N := by ring

/-- **The realized chart-Gram entry is jointly `(t, x)` continuous (the spectral →
chart-local bridge, `C⁰` arm).**

Let `g_DT : ℝ → SmoothRiemannianMetric I M` be realized off the background metric by a
smooth-section family `T_s`, i.e. on the time set `J`
`(g_DT t).inner x v w = g_bg.inner x v w + ccTensorBilinSymm g_bg (T_s t) x v w`
(`hreal`), and suppose the order-`2k` Sobolev image `t ↦ (T_s t).toHs (2k)` is
continuous on `J` at a supercritical order `2k > dim M + 4` (`hHs`).  Then for the
chart centred at `x₀` the chart-Gram entry `(t, x) ↦ chartGramMatrix (g_DT t) x₀ x i j`
is jointly continuous on `J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet`.

This is the joint upgrade of the per-time continuity carried by the interior spectral
smoothing: each time slice is continuous in `x` (the fixed-metric chart-Gram
smoothness `metric_inner_chartBasisFibers_continuousOn`), and the time modulus is
uniform on every compact piece of the base set
(`exists_chartGram_realized_uniform_modulus`, off the `H^{2k} ↪ C⁰` embedding), so the
locally-uniform joint-continuity engine `joint_continuousOn_open_of_slice_normModulus`
applies.  It is the `C⁰`-up-to-interior foundation of conjuncts (4)/(5) of
`deturck_ricci_parabolic_interior_regularity` (the `chartGramMatrix` continuity); the
interior `ContMDiffOn` form and the `chartGramOnE` jets are layered on top downstream. -/
theorem chartGram_realizedMetric_jointContinuousOn
    (g_bg : SmoothRiemannianMetric I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ} {J : Set ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hHs : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t)) J) :
    ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  refine joint_continuousOn_open_of_slice_normModulus
    (fun p : ℝ × M => chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
    (trivializationAt E (TangentSpace I) x₀).open_baseSet
    (fun t : ℝ => IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2)
      (2 * k) (T_s t))
    (fun t _ =>
      Analysis.Parabolic.TensorSpectral.metric_inner_chartBasisFibers_continuousOn
        (I := I) (M := M) (g_DT t) x₀ i j)
    hHs ?_
  intro K hK_sub hK_compact
  obtain ⟨B, hB⟩ := exists_chartGram_realized_uniform_modulus (I := I) (M := M)
    g_bg x₀ i j T_s hk hK_compact hK_sub
  refine ⟨B, fun t htJ t' ht'J x hxK => ?_⟩
  have hcancel :
      chartGramMatrix (I := I) (g_DT t) x₀ x i j -
          chartGramMatrix (I := I) (g_DT t') x₀ x i j =
        ccTensorBilinSymm (I := I) g_bg (T_s t) x
            (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x) -
          ccTensorBilinSymm (I := I) g_bg (T_s t') x
            (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x) := by
    rw [chartGramMatrix_apply, chartGramMatrix_apply,
      hreal t htJ x _ _, hreal t' ht'J x _ _]
    ring
  rw [hcancel]
  exact hB t t' x hxK

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- **The chart-Gram entry is jointly `(t, x)` `C∞` on the interior (the spectral →
chart-local bridge, `C∞` arm).**

Let `g_DT : ℝ → SmoothRiemannianMetric I M` be a metric family whose *bundle inner-product
`Hom`-section* `(t, x) ↦ (g_DT t).inner x` is jointly `C∞` over the product model
`𝓘(ℝ, ℝ).prod I` on `J ×ˢ baseSet` (`hsmooth`).  Then for the chart centred at `x₀` each
chart-Gram entry `(t, x) ↦ chartGramMatrix (g_DT t) x₀ x i j` is jointly `C∞` on
`J ×ˢ baseSet`.

This is the joint `(t, x)`-`C∞` analogue of the fixed-metric chart-Gram smoothness
`chartGramMatrix_entry_contMDiffOn`: the chart-Gram entry is the metric `Hom`-section
paired against the (`t`-independent, jointly smooth) chart frame `chartBasisVec`, so it is
delivered by `ContMDiffOn.clm_bundle_apply₂` over base `M` with base map `Prod.snd`.  It is
the interior `C∞` form of conjunct (4) of
`deturck_ricci_parabolic_interior_regularity` (the `chartGramMatrix` `ContMDiffOn`).

The hypothesis is the *joint* smoothness of the metric `Hom`-section, NOT a Sobolev
time-jet datum: separate regularity (continuity-in-time into every spatial `Hˢ` plus the
spatial `Hˢ ↪ C^m` embedding) yields only an anisotropic tensor-product regularity and
does *not* close to joint `C∞` (there is no separate-variable → joint-smoothness principle
for manifolds, in Mathlib or here).  The interior parabolic smoothing supplies this joint
smoothness directly; this lemma is the reduction from it to the scalar chart-Gram entry. -/
theorem chartGram_realizedMetric_jointContMDiffOn
    (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 ((g_DT q.1).inner q.2))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => chartBasisVec (I := I) x₀ i q.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (chartBasisVec_contMDiffOn (I := I) x₀ i).comp contMDiffOn_snd (fun q hq => hq.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => chartBasisVec (I := I) x₀ j q.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    (chartBasisVec_contMDiffOn (I := I) x₀ j).comp contMDiffOn_snd (fun q hq => hq.2)
  have happ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
          ((g_DT q.1).inner q.2
            (chartBasisVecFiber (I := I) x₀ i q.2)
            (chartBasisVecFiber (I := I) x₀ j q.2))))
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) hsmooth hv hw
  intro p hp
  have hpb := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

/-- **The chart-pulled-back Gram entry `chartGramOnE` is jointly `(t, x)` continuous on the
chart source (the spectral → chart-local bridge, `chartGramOnE` `C⁰` arm).**

Under the same realization data as `chartGram_realizedMetric_jointContinuousOn` — the family
realized off `g_bg` by a smooth-section family `T_s` (`hreal`) with continuous order-`2k`
Sobolev time-trace (`hHs`) at a supercritical order — the chart-`α`-pulled-back Gram entry
`(t, x) ↦ chartGramOnE (g_DT t) α i j (extChartAt I α x)` is jointly continuous on
`J ×ˢ (chartAt H α).source`.

On the chart source the chart round-trip is the identity
(`(extChartAt I α).left_inv`), so `chartGramOnE (g_DT t) α i j (extChartAt I α x)` equals the
chart-Gram entry `chartGramMatrix (g_DT t) α x i j`; the statement is then
`chartGram_realizedMetric_jointContinuousOn` transported along the identification
`(trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source`
(`TangentBundle.trivializationAt_baseSet`).  It is the `chartGramOnE` form of conjunct (6) of
`deturck_ricci_parabolic_interior_regularity`. -/
theorem chartGramOnE_realizedMetric_jointContinuousOn
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ} {J : Set ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hHs : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t)) J) :
    ContinuousOn
      (fun q : ℝ × M =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2))
      (J ×ˢ (chartAt H α).source) := by
  have hbase :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (I := I) α
  have hjoint := chartGram_realizedMetric_jointContinuousOn (I := I) (M := M)
    g_bg α i j g_DT T_s hk hreal hHs
  rw [hbase] at hjoint
  refine hjoint.congr ?_
  rintro ⟨t, x⟩ ⟨_, hx⟩
  change Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) α i j (extChartAt I α x)
    = chartGramMatrix (I := I) (g_DT t) α x i j
  rw [Integral.DivergenceTheorem.chartGramOnE_def]
  have hxsource : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  rw [(extChartAt I α).left_inv hxsource]

/-- **The `0`-jet of `chartGramOnE` is jointly `(t, x)` continuous (the `k = 0` arm of the
spatial-jet conjunct).**

The Euclidean `iteratedFDeriv ℝ 0` of the chart-pulled-back Gram entry is, by
`iteratedFDeriv_zero_eq_comp`, the order-`0` curry isometry applied to the value, so its
joint continuity is equivalent to that of the value `chartGramOnE (g_DT t) α i j`
(`chartGramOnE_realizedMetric_jointContinuousOn`).  This is the `k = 0` component of conjunct
(7) of `deturck_ricci_parabolic_interior_regularity` and the joint feed for
`RicciContJointAux.jointGram_continuousOn`.

The higher jets `k ∈ {1, 2}` are NOT delivered here: producing joint `(t, x)`-continuity of
the *partial spatial* iterated Fréchet derivative `(t, y) ↦ iteratedFDeriv ℝ k
(chartGramOnE (g_DT t) α i j) y` requires a partial-iteratedFDeriv ↔ joint-regularity bridge
that is absent both in Mathlib and in this library (see the file's note); it is the genuine
jet wall for this conjunct. -/
theorem iteratedFDeriv_zero_chartGramOnE_realizedMetric_jointContinuousOn
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2) {k : ℕ} {J : Set ℝ}
    (hk : 2 * k > Module.finrank ℝ E + 4)
    (hreal : ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace I x),
      (g_DT t).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s t) x v w)
    (hHs : ContinuousOn (fun t : ℝ =>
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) (T_s t)) J) :
    ContinuousOn
      (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
        (extChartAt I α q.2))
      (J ×ˢ (chartAt H α).source) := by
  have hjoint := chartGramOnE_realizedMetric_jointContinuousOn (I := I) (M := M)
    g_bg α i j g_DT T_s hk hreal hHs
  have hcurry : Continuous ((continuousMultilinearCurryFin0 ℝ E ℝ).symm) :=
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous
  refine (hcurry.comp_continuousOn hjoint).congr ?_
  intro q _
  simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
