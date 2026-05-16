import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.Bootstrap

/-!
# The iterated tensor-component interior elliptic a-priori estimate

The headline of the interior elliptic-regularity bootstrap for tensor weak
solutions: a quantitative interior a-priori estimate at arbitrary order. For a
smooth compactly supported `(r, s)`-tensor section `T` satisfying the global
`H¹` weak equation of the connection Laplacian with smooth source `F`, the
`W^{2k+2,2}` Sobolev norm of each chart component of `T` is bounded by the
`W^{2k,2}` norms of the chart components of `F` and the `W^{1,2}` norms of the
chart components of `T`, with a constant uniform in `T` and `F`.

The per-step regularity boost `tensorComponent_aPriori_succ_sum` raises the
solution's Sobolev order by one, dropping it onto the source two orders below
and onto the solution one order below. The headline iterates this: the outer
induction on `k` applies the per-step boost twice — at orders `2k+1` and `2k+2`
— absorbing the lower-order solution norm from the inductive hypothesis and the
source norm from the per-step boost itself, with the source order monotonically
controlled by the highest order appearing.

## Main results

* `tensorComponent_aPriori_estimate` — for fixed geometric data there is a
  constant `C ≥ 0`, uniform in the tensor sections, with
  `wkpNorm (2k+2) 2 (tensorComponentEuclid g r s T α P₀) Ω'' ≤
    ENNReal.ofReal C ·
      (∑_Q wkpNorm (2k) 2 (tensorComponentEuclid g r s F α Q) Ω'' +
        ∑_P wkpNorm 1 2 (tensorComponentEuclid g r s T α P) Ω'')`.

* `tensorComponent_aPriori_estimate_all` — the form packaged over all component
  multi-indices `P₀`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory Topology Function
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

Match the convention in the surrounding tensor-regularity files: install the
Borel σ-algebras locally, without leaking global instances onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Headline

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The local dimension of the chart, as a natural number. -/
local notation "dimE" => Module.finrank ℝ E

/-! ### A monotone-substitution combinator for the outer induction

The inductive step of the headline substitutes the inductive hypothesis into the
per-step regularity boost. The combinator below isolates that single
substitution: given a low-order bound `S ≤ ofReal c · (BF_p + L)` and a per-step
boost `S' ≤ ofReal a · (BF_{p'} + S)` with `p ≤ p'` (so `BF_p ≤ BF_{p'}` by
monotonicity of the source norm in its order), the conclusion
`S' ≤ ofReal (a · (1 + c)) · (BF_{p'} + L)` follows by absorbing `BF_p` into
`BF_{p'}` and `BF_{p'}` into `BF_{p'} + L`. -/

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)] in
/-- The monotone-substitution step: chain a low-order bound and a per-step boost
into a single bound at the higher order. -/
private lemma chain_step_le
    {S S' BFp BFp' L : ℝ≥0∞} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hBF_mono : BFp ≤ BFp')
    (hlow : S ≤ ENNReal.ofReal c * (BFp + L))
    (hstep : S' ≤ ENNReal.ofReal a * (BFp' + S)) :
    S' ≤ ENNReal.ofReal (a * (1 + c)) * (BFp' + L) := by
  -- `S ≤ ofReal c · (BFp' + L)` by monotonicity in the source order.
  have hlow' : S ≤ ENNReal.ofReal c * (BFp' + L) :=
    hlow.trans (mul_le_mul_of_nonneg_left
      (add_le_add hBF_mono le_rfl) (zero_le _))
  -- `BFp' + S ≤ (1 + ofReal c) · (BFp' + L)`.
  have hsum : BFp' + S ≤ (1 + ENNReal.ofReal c) * (BFp' + L) := by
    rw [add_mul, one_mul]
    exact add_le_add (le_add_right le_rfl) hlow'
  -- Chain and collect the constant.
  refine hstep.trans ?_
  refine (mul_le_mul_of_nonneg_left hsum (zero_le _)).trans (le_of_eq ?_)
  rw [← mul_assoc,
    show (1 : ℝ≥0∞) + ENNReal.ofReal c = ENNReal.ofReal (1 + c) from by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hc, ENNReal.ofReal_one],
    ← ENNReal.ofReal_mul ha]

/-! ### Monotonicity of the source-component sum in the Sobolev order

The sum, over component multi-indices, of the `W^{n,2}` norms of the chart
components of the source is monotone in `n`: a higher Sobolev order gives a
larger norm. -/

/-- The source-component sum is monotone in the Sobolev order. -/
private lemma sum_componentNorm_mono_order
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (F : SmoothCcTensor g r s)
    (α : M) {Ω'' : Set EuclN} {n n' : ℕ} (hn : n ≤ n') :
    (∑ Q : CompIdx E r s, wkpNorm (d := dimE) n 2
        (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') ≤
      ∑ Q : CompIdx E r s, wkpNorm (d := dimE) n' 2
        (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'' :=
  Finset.sum_le_sum (fun _Q _ => wkpNorm_mono_order (d := dimE) hn _ _)

/-! ### The iterated interior elliptic a-priori estimate

The headline. The outer induction on `k`: the base case `k = 0` is the per-step
boost at order `0`; the inductive step applies the per-step boost at orders
`2k+1` and `2k+2`, substituting the inductive hypothesis via `chain_step_le`. -/

set_option maxHeartbeats 3200000 in
/-- **Iterated interior elliptic a-priori estimate for a chart component.**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless) smooth
manifold `M`, let `α : M` be a chart center, `(r, s)` tensor ranks, `k` an
iteration count, `P₀` a component multi-index, `K ⊆ chartTargetEuclid α` a
compact set, and `Ω''` a precompact open subdomain of the chart target with
`K ⊆ Ω''`.

There is a constant `C ≥ 0`, depending only on that data — uniform in the tensor
sections — such that for **every** pair of chart-supported smooth compactly
supported `(r, s)`-tensor sections `T` (the solution) and `F` (the source) whose
chart components are supported in `K`, and such that the global `H¹` weak
equation `∫_M ⟨∇T, ∇v⟩ dμ_g = ⟨F, v⟩_{L²}` of the connection Laplacian holds for
every smooth compactly-supported test section,

```
wkpNorm (2k+2) 2 (tensorComponentEuclid g r s T α P₀) Ω'' ≤
  ENNReal.ofReal C ·
    (∑_Q wkpNorm (2k) 2 (tensorComponentEuclid g r s F α Q) Ω'' +
      ∑_P wkpNorm 1 2 (tensorComponentEuclid g r s T α P) Ω'').
```

The constant `C` is quantified before `T` and `F`: it is uniform in the
solution and the source. The hypothesis `K ⊆ Ω''` is genuinely used — the
interior-`H²` engine's data is the global integral, while the right-hand side
uses `Ω''`-restricted Sobolev norms; they agree because every relevant function
is supported in `K ⊆ Ω''`. -/
theorem tensorComponent_aPriori_estimate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (k : ℕ) (P₀ : CompIdx E r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_target : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      wkpNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              wkpNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              wkpNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  -- The headline is proved by establishing the order-`(2k+2)` bound on the
  -- *full component tuple*, then extracting the single `P₀` summand.
  suffices h_tuple : ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      (∑ P : CompIdx E r s,
        wkpNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              wkpNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              wkpNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') by
    obtain ⟨C, hC_nn, hC⟩ := h_tuple
    refine ⟨C, hC_nn, fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
    -- The single-`P₀` norm is one summand of the full-tuple sum.
    exact (Finset.single_le_sum
      (f := fun P : CompIdx E r s => wkpNorm (d := dimE) (2 * k + 2) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
      (fun P _ => zero_le _) (Finset.mem_univ P₀)).trans
        (hC T F hT_supp hF_supp hT_K hF_K hweak)
  -- The outer induction on `k`.
  induction k with
  | zero =>
      -- Base case: the per-step boost on the full component tuple at order `0`.
      obtain ⟨C, hC_nn, hC⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          0 hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      refine ⟨C, hC_nn, fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
      have h := hC T F hT_supp hF_supp hT_K hF_K hweak
      simpa using h
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      -- The per-step boost at order `2k+1`.
      obtain ⟨A, hA_nn, hA⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          (2 * k + 1) hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      -- The per-step boost at order `2k+2`.
      obtain ⟨B, hB_nn, hB⟩ :=
        tensorComponent_aPriori_succ_sum (I := I) (M := M) g r s α hK hK_target
          (2 * k + 2) hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
      -- The aggregate constant for order `2(k+1)+2 = 2k+4`.
      refine ⟨B * (1 + A * (1 + Ck)), by positivity,
        fun T F hT_supp hF_supp hT_K hF_K hweak => ?_⟩
      -- Abbreviations for the component sums.
      set L : ℝ≥0∞ := ∑ P : CompIdx E r s, wkpNorm (d := dimE) 1 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' with hL_def
      -- The inductive hypothesis at order `2k+2`.
      have h_ih := hCk T F hT_supp hF_supp hT_K hF_K hweak
      -- The per-step boost at order `2k+1`, giving the order-`2k+3` bound.
      have h_step1 := hA T F hT_supp hF_supp hT_K hF_K hweak
      -- The per-step boost at order `2k+2`, giving the order-`2k+4` bound.
      have h_step2 := hB T F hT_supp hF_supp hT_K hF_K hweak
      -- Substitute the inductive hypothesis into the order-`2k+1` boost.
      -- `∑_P wkpNorm (2k+3) T ≤ ofReal (A·(1+Ck)) · (∑_Q wkpNorm (2k+1) F + L)`.
      have h_23 :
          (∑ P : CompIdx E r s, wkpNorm (d := dimE) (2 * k + 1 + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
          ENNReal.ofReal (A * (1 + Ck)) *
            ((∑ Q : CompIdx E r s, wkpNorm (d := dimE) (2 * k + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              L) :=
        chain_step_le hA_nn hCk_nn
          (sum_componentNorm_mono_order (I := I) (M := M) g r s F α
            (Ω'' := Ω'') (by omega : 2 * k ≤ 2 * k + 1))
          h_ih h_step1
      -- Substitute that into the order-`2k+2` boost.
      -- `∑_P wkpNorm (2k+4) T ≤ ofReal (B·(1+A·(1+Ck))) · (∑_Q wkpNorm (2k+2) F + L)`.
      have h_24 :
          (∑ P : CompIdx E r s, wkpNorm (d := dimE) (2 * k + 2 + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
          ENNReal.ofReal (B * (1 + A * (1 + Ck))) *
            ((∑ Q : CompIdx E r s, wkpNorm (d := dimE) (2 * k + 2) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              L) :=
        chain_step_le hB_nn (by positivity)
          (sum_componentNorm_mono_order (I := I) (M := M) g r s F α
            (Ω'' := Ω'') (by omega : 2 * k + 1 ≤ 2 * k + 2))
          h_23 h_step2
      -- Re-index `2k+2+2 = 2(k+1)+2` and `2k+2 = 2(k+1)`.
      have h_lhs : 2 * k + 2 + 2 = 2 * (k + 1) + 2 := by ring
      have h_rhs : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [h_lhs, h_rhs] at h_24
      exact h_24

/-- **Iterated interior elliptic a-priori estimate, packaged over all component
multi-indices.** For fixed geometric data there is a constant `C ≥ 0`, uniform
in the tensor sections and in the component multi-index, such that for every
component multi-index `P₀` and every pair of chart-supported smooth compactly
supported tensor sections `T` (solution) and `F` (source) satisfying the global
`H¹` weak equation, the order-`(2k+2)` Sobolev norm of the chart component
`tensorComponentEuclid g r s T α P₀` over the precompact subdomain `Ω''` is
controlled by the order-`(2k)` source-component norms and the order-`1`
solution-component norms.

The single constant `C` is obtained as the largest of the per-component-index
constants supplied by `tensorComponent_aPriori_estimate`. -/
theorem tensorComponent_aPriori_estimate_all
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (k : ℕ)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_target : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P₀ : CompIdx E r s) (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      wkpNorm (d := dimE) (2 * k + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              wkpNorm (d := dimE) (2 * k) 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              wkpNorm (d := dimE) 1 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  -- The per-component-index constant from the headline.
  have h_per : ∀ P₀ : CompIdx E r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T F : SmoothCcTensor g r s),
        tsupport T.toFun ⊆ (chartAt H α).source →
        tsupport F.toFun ⊆ (chartAt H α).source →
        (∀ P : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
        (∀ Q : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
        (∀ v : SmoothCcTensor g r s,
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
        wkpNorm (d := dimE) (2 * k + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
          ENNReal.ofReal C *
            ((∑ Q : CompIdx E r s,
                wkpNorm (d := dimE) (2 * k) 2
                  (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              ∑ P : CompIdx E r s,
                wkpNorm (d := dimE) 1 2
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') :=
    fun P₀ => tensorComponent_aPriori_estimate (I := I) (M := M) g r s α hK
      hK_target k P₀ hΩ''_open hΩ''_compact_closure hΩ''_target hK_Ω''
  choose Cf hCf_nn hCf using h_per
  -- A canonical component multi-index, used as the nonemptiness witness.
  have hCI_ne : (Finset.univ : Finset (CompIdx E r s)).Nonempty :=
    ⟨Classical.arbitrary (CompIdx E r s), Finset.mem_univ _⟩
  -- The aggregate constant: the largest per-component-index constant.
  refine ⟨(Finset.univ : Finset (CompIdx E r s)).sup' hCI_ne Cf, ?_, ?_⟩
  · exact le_trans (hCf_nn (Classical.arbitrary (CompIdx E r s)))
      (Finset.le_sup' Cf (Finset.mem_univ _))
  · intro P₀ T F hT_supp hF_supp hT_K hF_K hweak
    -- The per-`P₀` bound, lifted to the aggregate constant.
    refine (hCf P₀ T F hT_supp hF_supp hT_K hF_K hweak).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (Finset.le_sup' Cf (Finset.mem_univ P₀)))
      (zero_le _)

end Headline

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
