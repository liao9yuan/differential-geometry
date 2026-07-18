import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# Joint continuity of the AA limit metric family (C⁰ layer of the `hsmooth` brick)

Toward `MetricFamilySmoothOn` for the Arzelà–Ascoli limit family `gInf` of
MSM135 Thm 3.10 ⇐ 3.9 (the `hsmooth` input of `isSolutionOn_of_reg`,
`FlowLimitBuild.lean`), this file provides the C⁰ half: joint `(t, x)` continuity
of the chart-Gram entries of `gInf` on window × base-set products, transferred
from the window-uniform order-0 covariant convergence produced by Brick 5
(`windowGInfAll_pt`) and the joint continuity of the approximating families.

* `chartGram_sub_le` — chart-Gram entry difference of two metrics at ANY point,
  bounded by `metricDerivNorm 0` times the `gRef`-norms of the chart frame
  vectors (pointwise Cauchy–Schwarz; anchor-free version of the single-point
  bound inside `RicciFromJets.lean`).
* `chartGramBound_contOn` — the Cauchy–Schwarz factor is continuous on the base
  set (it is built from `gRef`'s own chart-Gram diagonal).
* `chartGramLim_contOn` — the transfer: window-uniform order-0 convergence on
  compacts + per-`k` joint continuity ⟹ joint continuity of the limit's
  chart-Gram entries (locally-uniform-limit argument).
* `metricTensorContLim` — the endpoint consumed by `MetricFamilySmoothOn`'s
  `metricTensor_cont` field: the `Tensor0SFamilyContinuousOnSet` package for
  `gInf` on the window, via `metricTensorCont_of_chartGram`.

Route + the remaining (C^∞) half of the brick: `FlowLimitRegularity.md`.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow (SolutionOn)
open Tensor0SBundle
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
/-- The Cauchy–Schwarz factor of `chartGram_sub_le` is continuous on the trivialization
base set: it is built from the diagonal of `gRef`'s own chart-Gram matrix
(`chartGramMatrix_entry_contMDiffOn`). -/
theorem chartGramBound_contOn
    (gRef : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank Real E)) :
    ContinuousOn (fun x : M =>
      Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
          (chartBasisVecFiber (I := I) x₀ i x))
        * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
            (chartBasisVecFiber (I := I) x₀ j x)))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hii : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x i i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ i i).continuousOn
  have hjj : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x j j)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ j j).continuousOn
  exact (Real.continuous_sqrt.comp_continuousOn hii).mul
    (Real.continuous_sqrt.comp_continuousOn hjj)

variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Pointwise chart-Gram difference bound.**  The chart-Gram entry difference of two
metrics at any point `x` (any anchor `x₀`) is bounded by the order-0 covariant seminorm
`metricDerivNorm 0` times the `gRef`-norms of the two chart frame vectors.  Pointwise
Cauchy–Schwarz (`abs_apply_le_sqrt_normSq0S` at a `gRef`-orthonormal basis); no base-set
membership is needed — off the base set both sides use the same (junk) frame values. -/
theorem chartGram_sub_le
    (gRef u u' : SmoothRiemannianMetric I M) (x₀ x : M)
    (i j : Fin (Module.finrank Real E)) :
    |chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j|
      ≤ metricDerivNorm (I := I) 0 u u' gRef x
        * (Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ i x))
          * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
              (chartBasisVecFiber (I := I) x₀ j x))) := by
  classical
  have hentry : chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j
      = (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
          ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x] := by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    have hu := Tensor0SBundle.metricTensorField_apply (I := I) u x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    have hu' := Tensor0SBundle.metricTensorField_apply (I := I) u' x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    simp only [metricDiffCovDerivAt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hu'
    change u.inner x _ _ - u'.inner x _ _
      = (metricCovDeriv (I := I) u gRef 0 x) _ - (metricCovDeriv (I := I) u' gRef 0 x) _
    rw [show (metricCovDeriv (I := I) u gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u x from rfl,
      show (metricCovDeriv (I := I) u' gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u' x from rfl,
      hu, hu']
  rw [hentry]
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have h := abs_apply_le_sqrt_normSq0S (I := I) (g := gRef) (x := x) (s := 2)
    basis hON (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
    ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x]
  refine h.trans (le_of_eq ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- **Joint continuity of the limit chart-Gram entries (the C⁰ transfer).**  If the
chart-Gram entries of each `gSeq k` are jointly continuous on the window × base-set
product and `gSeq k → gInf` in the order-0 covariant seminorm, uniformly on
window × compacts (the Brick-5 `windowGInfAll_pt` shape), then the chart-Gram entries of
`gInf` are jointly continuous on the same product.  Locally-uniform-limit argument: near
each point pick a compact neighborhood inside the base set, bound the Cauchy–Schwarz
factor there, and apply `TendstoUniformlyOn.continuousOn`. -/
theorem chartGramLim_contOn
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (x₀ : M) (i j : Fin (Module.finrank Real E))
    (hkcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  intro p₀ hp₀
  obtain ⟨hp₀t, hp₀x⟩ := hp₀
  -- a compact neighborhood of `p₀.2` inside the base set
  obtain ⟨K, hKc, hKint, hKsub⟩ := exists_compact_subset
    (trivializationAt E (TangentSpace I) x₀).open_baseSet hp₀x
  have hKne : K.Nonempty := ⟨p₀.2, interior_subset hKint⟩
  -- the Cauchy–Schwarz factor and its sup on `K`
  set c : M → ℝ := fun x =>
    Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ i x))
      * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
          (chartBasisVecFiber (I := I) x₀ j x)) with hc
  have hcnonneg : ∀ x : M, 0 ≤ c x := fun x =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨z, hzK, hz⟩ := hKc.exists_isMaxOn hKne
    ((chartGramBound_contOn (I := I) gRef x₀ i j).mono hKsub)
  set Cb : ℝ := c z with hCb
  have hCb0 : 0 ≤ Cb := hcnonneg z
  have hzle : ∀ x ∈ K, c x ≤ Cb := fun x hx => isMaxOn_iff.mp hz x hx
  -- uniform convergence of the chart-Gram entries on `Icc β ψ ×ˢ K`
  have htu : TendstoUniformlyOn
      (fun (k : ℕ) (p : ℝ × M) => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      atTop (Set.Icc β ψ ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv K hKc (ε / (Cb + 1)) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hd : metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x ≤ ε / (Cb + 1) :=
      (hk0 k hk t ht x hx).le
    have hcs := chartGram_sub_le (I := I) gRef (gSeq k t) (gInf t) x₀ x i j
    calc dist (chartGramMatrix (I := I) (gInf t) x₀ x i j)
          (chartGramMatrix (I := I) (gSeq k t) x₀ x i j)
        = |chartGramMatrix (I := I) (gSeq k t) x₀ x i j
            - chartGramMatrix (I := I) (gInf t) x₀ x i j| := by
          rw [Real.dist_eq, abs_sub_comm]
      _ ≤ metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x * c x := hcs
      _ ≤ (ε / (Cb + 1)) * Cb := by
          exact mul_le_mul hd (hzle x hx) (hcnonneg x) (by positivity)
      _ < (ε / (Cb + 1)) * (Cb + 1) := by
          have hpos : 0 < ε / (Cb + 1) := by positivity
          exact mul_lt_mul_of_pos_left (by linarith) hpos
      _ = ε := div_mul_cancel₀ ε (by positivity)
  -- continuity of the limit on the smaller product, then within the full set
  have hcOn : ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ K) :=
    htu.continuousOn (Filter.Eventually.of_forall (fun k =>
      (hkcont k).mono (Set.prod_mono le_rfl hKsub))).frequently
  have hmem : Set.Icc β ψ ×ˢ K
      ∈ 𝓝[Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet] p₀ := by
    have hnhds : (Set.univ ×ˢ interior K : Set (ℝ × M)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hKint)
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hxK⟩
    exact ⟨ht, interior_subset hxK⟩
  exact (hcOn.continuousWithinAt
    ⟨hp₀t, interior_subset hKint⟩).mono_of_mem_nhdsWithin hmem

set_option maxHeartbeats 1000000 in
/-- **`metricTensor_cont` endpoint for the AA limit.**  The joint total-space continuity
package (`Tensor0SFamilyContinuousOnSet`) for `gInf` on the window `Icc β ψ`, from the
Brick-5-shaped order-0 uniform convergence and the joint chart-Gram continuity of the
approximating families.  This is the `metricTensor_cont` field of `MetricFamilySmoothOn`
(and `coeff_cont` follows from it by evaluation) for the limit flow. -/
theorem metricTensorContLim
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (hkcont : ∀ (k : ℕ) (x₀ : M) (i j : Fin (Module.finrank Real E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 (Set.Icc β ψ)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (gInf t) x) := by
  apply metricTensorCont_of_chartGram (I := I) (K := Set.Icc β ψ) gInf
  intro x₀ i j
  have hlim := chartGramLim_contOn (I := I) gSeq gInf gRef β ψ hconv x₀ i j
    (fun k => hkcont k x₀ i j)
  have hincl : ContinuousOn
      (fun q : {t : ℝ // t ∈ Set.Icc β ψ} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ Set.Icc β ψ} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  exact hlim.comp hincl (fun q hq => ⟨q.1.2, hq⟩)

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem metricCLMSection_Ioo
    [NeZero (Module.finrank Real E)]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ Set.univ) := by
  set gsh : ℝ → SmoothRiemannianMetric I M := fun s => g (s + a) with hgsh
  have haddC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 + a, p.2)) :=
    (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
  have hsubC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 - a, p.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have hgram_sh : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (gsh p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1 + a, p.2))
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      rintro ⟨s, m⟩ ⟨hs, hm⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hm⟩
    exact (hgram x₀ i j).comp haddC.contMDiffOn hmaps
  have hsh := metricCLMSection_jointContMDiffOn_of_chartGram
    (I := I) gsh (b - a) hgram_sh
  have hmaps2 : Set.MapsTo (fun p : ℝ × M => (p.1 - a, p.2))
      (Set.Ioo a b ×ˢ (Set.univ : Set M))
      (Set.Ioo (0 : ℝ) (b - a) ×ˢ (Set.univ : Set M)) := by
    rintro ⟨t, m⟩ ⟨ht, _⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Set.mem_univ _⟩
  have hcomp := hsh.comp hsubC.contMDiffOn hmaps2
  refine hcomp.congr ?_
  rintro ⟨t, m⟩ _
  simp only [Function.comp_apply, hgsh, sub_add_cancel]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
private theorem metricFrameComp_Ioo
    [NeZero (Module.finrank Real E)]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (Set.Ioo a b ×ˢ u) := by
  have hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2))
      (Set.Ioo a b ×ˢ u) :=
    (metricCLMSection_Ioo (I := I) g a b hgram).mono
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2))
      (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × M => p.2) (s := Set.Ioo a b ×ˢ u)
    (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    (v := fun p : ℝ × M => frame i p.2)
    (w := fun p : ℝ × M => frame j p.2) hψ hv hw
  intro p hp
  have hpx := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

section OpenInterval

variable [NeZero (Module.finrank Real E)]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace ConvOut

variable [I.Boundaryless]

/-- Fixed-window joint spacetime smoothness of the limit metric in the
trivialization-based chart-Gram readout. This is the remaining analytic
regularity frontier. -/
theorem gramSmooth
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  sorry

end ConvOut

namespace OpenConvOut

set_option maxHeartbeats 1600000 in
/-- Assemble joint smoothness of the open-interval limit metric from joint
chart-Gram smoothness on every canonical compact window. -/
theorem smoothMetric
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (hgramWin : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
          (Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
              (RealTimeInterval.openWindowRight b t₀ n) ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    MetricFamilySmoothOn (I := I) (M := P.M)
      (RealTimeInterval.openInterval a b t₀ ht₀)
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M)
          (RealTimeInterval.openInterval a b t₀ ht₀)).family := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  have hgram : ∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × P.M => chartGramMatrix (I := I) (co.gInf p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j p hp
    obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ hp.1
    have htn : p.1 ∈ Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
        (RealTimeInterval.openWindowRight b t₀ n) := Icc_mem_nhds_iff.mp hn
    have hlocal := hgramWin n x₀ i j p ⟨htn, hp.2⟩
    have hnhds : Set.Ioo (RealTimeInterval.openWindowLeft a t₀ n)
          (RealTimeInterval.openWindowRight b t₀ n) ×ˢ
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 p :=
      prod_mem_nhds (Ioo_mem_nhds htn.1 htn.2)
        ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hp.2)
    exact (hlocal.contMDiffAt hnhds).contMDiffWithinAt
  have hcontTensor : Tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2
      (Set.Ioo a b) (fun t x => metricTensorField (I := I) (co.gInf t) x) := by
    apply metricTensorCont_of_chartGram (I := I) (K := Set.Ioo a b) co.gInf
    intro x₀ i j
    have hincl : ContinuousOn
        (fun q : {t : ℝ // t ∈ Set.Ioo a b} × P.M => ((q.1 : ℝ), q.2))
        {q : {t : ℝ // t ∈ Set.Ioo a b} × P.M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    exact (hgram x₀ i j).continuousOn.comp hincl (fun q hq => ⟨q.1.2, hq⟩)
  refine ⟨?_, ?_, hcontTensor, ?_⟩
  · intro x X Y
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun t : ℝ => (t, x)) (Set.Ioo a b) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hψ' : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun t : ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
          ((co.gInf t).inner x)) (Set.Ioo a b) :=
      (metricCLMSection_Ioo (I := I) co.gInf a b hgram).comp
        hcurve (fun t ht => ⟨ht, Set.mem_univ _⟩)
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x X)
        (Set.Ioo a b) := contMDiffOn_const
    have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x Y)
        (Set.Ioo a b) := contMDiffOn_const
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := P.M)) (E₂ := TangentSpace I (M := P.M))
      (E₃ := Bundle.Trivial P.M ℝ) (b := fun _ : ℝ => x)
      (ψ := fun t : ℝ => (co.gInf t).inner x)
      (v := fun _ : ℝ => X) (w := fun _ : ℝ => Y) hψ' hv hw
    have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (co.gInf t).inner x X Y) (Set.Ioo a b) := by
      intro t ht
      have hpt := happ t ht
      rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
      exact hpt.2
    exact hscalar.contDiffOn
  · intro x X Y
    have hbase : ContinuousOn
        (fun s : ℝ => metricTensorField (I := I) (co.gInf s) x (vec2 X Y))
        (Set.Ioo a b) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hcontTensor.eval_continuous (P := {s : ℝ // s ∈ Set.Ioo a b})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun p => p.2) continuous_const
        (v := fun i _ => vec2 X Y i) (fun _ => continuous_const)
    refine hbase.congr (fun s _ => ?_)
    simp [metricTensorField_apply, vec2]
  · intro Idx _ frame u hframe i j
    exact metricFrameComp_Ioo (I := I) co.gInf a b hgram frame hframe i j

variable [I.Boundaryless]

/-- The fixed-window analytic theorem supplies the open-interval metric
regularity package on the one subsequence carried by `OpenConvOut`. -/
theorem smoothMetric_of_conv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    MetricFamilySmoothOn (I := I) (M := P.M)
      (RealTimeInterval.openInterval a b t₀ ht₀)
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M)
          (RealTimeInterval.openInterval a b t₀ ht₀)).family := by
  apply OpenConvOut.smoothMetric (Φ := Φ) ht₀ co
  intro n
  apply ConvOut.gramSmooth (Φ := Φ) (co := OpenConvOut.at_window Φ co n)
  intro t ht
  have htOpen := RealTimeInterval.openWindow_subset ht₀ n ht
  simpa only [hD, RealTimeInterval.openInterval] using htOpen

end OpenConvOut

end OpenInterval

end HCGCompactness
end DifferentialGeometry
