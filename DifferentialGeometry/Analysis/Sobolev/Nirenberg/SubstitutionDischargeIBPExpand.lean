import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionDischargeSmoothApprox

/-!
# IBP-expanded chart-bilinear variational identity

Building on the smooth approximating sequence supplied by
`SubstitutionDischargeSmoothApprox`, this module performs the discrete
integration-by-parts and discrete product-rule expansions that turn the
variational identity at `v_h := standardNirenbergTest k h η D.u_chart`
into the symbolic-piece form

  `principal + cross_1 + cross_2 + cross_3 + f_term = c_term`,

matching the names in `SubstitutionNonSmoothChartBilinear`.

The chain proceeds in five steps, each transforming the previous identity
by a single algebraic operation:

1. `chart_bilinear_identity_h1_0_smooth_seq` — the variational identity
   applied to each smooth approximant `v_h_n := standardNirenbergTest k h η
   (u_seq n)` via `chart_bilinear_identity_h1_0`.
2. `variational_identity_at_v_h` — pass to the L² limit using the
   smooth-CS approximating sequence from `exists_smooth_uChart_approx` and
   `standardNirenbergTest_seq_tendsto_eLpNorm`.
3. `variational_identity_v_h_expanded` — substitute the explicit weak
   `j`-partial of `v_h` from `hasWeakPartialDeriv_standardNirenbergTest`.
4. `variational_identity_after_ibp` — apply
   `integral_diffQuot_mul_eq_neg_integral_mul_diffQuot` to move the outer
   `D_{-h}^k` onto the principal coefficient.
5. `variational_identity_after_product_rule` — apply the discrete product
   rule `D_h^k(a · u) = (D_h^k a) · τ_h u + a · D_h^k u` to expand into
   the principal term plus the four cross terms, ready to be matched
   against the symbolic pieces.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeIBPExpand

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Step 1: Variational identity for the smooth approximating sequence -/

/-- For each smooth compactly-supported `u_seq n`, the variational identity
holds with the smooth Nirenberg test function `v_h_n :=
standardNirenbergTest k h η (u_seq n)` as the test function. This is a
direct application of `chart_bilinear_identity_h1_0` (with `K_0 :=
cthickening |h| K_0`, treating the constant sequence `n ↦ v_h_n` as the
smooth-CS approximating sequence to itself). -/
theorem chart_bilinear_identity_h1_0_smooth_seq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {u_seq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (u_seq n)) :
    ∀ n,
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ
                  (standardNirenbergTest (d := Module.finrank ℝ E) k h η
                    (u_seq n)) y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              (u_seq n) y
          ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n) y
        ∂(volume : Measure EuclN) := by
  classical
  -- The cthickening is a compact subset of the chart target.
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  intro n
  -- Get the smooth Nirenberg test function v_h_n.
  obtain ⟨h_v_smooth, h_v_cs⟩ :=
    standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n
  -- Support of v_h_n is in cthickening |h| K_0.
  have h_v_supp : tsupport (standardNirenbergTest (d := Module.finrank ℝ E)
      k h η (u_seq n)) ⊆ Metric.cthickening |h| K_0 :=
    standardNirenbergTest_tsupport_in_thickening (E := E) k h hη_supp
      hη_supp_in_K_0 (u_seq n)
  -- Apply chart_bilinear_identity_h1_0 with ψ := v_h_n, K_0 := cthickening |h| K_0,
  -- weak_partial_ψ j := classical partial, smooth approximating sequence := constant n.
  set ψ : EuclN → ℝ := standardNirenbergTest (d := Module.finrank ℝ E)
    k h η (u_seq n) with hψ_def
  set weak_partial_ψ : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j x => (fderiv ℝ ψ x) (EuclideanSpace.single j 1) with hwp_def
  -- ψ is smooth and CS, so it's in L² on cthickening |h| K_0.
  have hψ_lp : MemLp ψ 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    (h_v_smooth.continuous.memLp_of_hasCompactSupport h_v_cs).restrict _
  -- Each classical partial is L² (smoothness + compact support).
  have hψ_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (weak_partial_ψ j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro j
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    have h_cont : Continuous (weak_partial_ψ j) := by
      have h_fderiv_cont : Continuous (fderiv ℝ ψ) :=
        h_v_smooth.continuous_fderiv h_top_ne_zero
      exact h_fderiv_cont.clm_apply continuous_const
    have h_cs : HasCompactSupport (weak_partial_ψ j) :=
      h_v_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact (h_cont.memLp_of_hasCompactSupport h_cs).restrict _
  -- The constant approximating sequence: ψ_seq n := ψ.
  set ψ_seq : ℕ → EuclN → ℝ := fun _ => ψ with hψseq_def
  have hψ_seq_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (ψ_seq m) := fun _ => h_v_smooth
  have hψ_seq_cs : ∀ m, HasCompactSupport (ψ_seq m) := fun _ => h_v_cs
  have hψ_seq_supp : ∀ m, tsupport (ψ_seq m) ⊆ Metric.cthickening |h| K_0 :=
    fun _ => h_v_supp
  -- L² convergence of ψ_seq m → ψ is trivial (constant sequence).
  have hψ_seq_l2 :
      Tendsto (fun m => eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    have h_eq : (fun m : ℕ => eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => ψ_seq m x - ψ x) = (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change ψ x - ψ x = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  -- L² convergence of ∂_j ψ_seq m → weak_partial_ψ j is trivial.
  have hψ_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun m => eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    intro j
    have h_eq : (fun m : ℕ => eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => (fderiv ℝ (ψ_seq m) x)
          (EuclideanSpace.single j 1) - weak_partial_ψ j x) =
          (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change (fderiv ℝ ψ x) (EuclideanSpace.single j 1) -
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  -- Apply chart_bilinear_identity_h1_0.
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick ψ weak_partial_ψ hψ_lp hψ_grad_lp ψ_seq
    hψ_seq_smooth hψ_seq_cs hψ_seq_supp hψ_seq_l2 hψ_seq_grad_l2

/-! ## Step 2: Pass to the L² limit at v_h

To pass from the variational identity for each smooth `v_h_n` to the
identity for the L² limit `v_h`, we apply `chart_bilinear_identity_h1_0`
directly with `ψ := v_h`, `weak_partial_ψ j := <weak partial of v_h>`,
and the smooth approximating sequence
`ψ_seq n := standardNirenbergTest k h η (u_seq n)`. The hypothesis bundle
captures the L² and L²-gradient convergence facts that go into the limit,
together with the explicit weak partial of `v_h`. -/

set_option linter.unusedVariables false in
/-- The variational identity holds at `v_h := standardNirenbergTest k h η
D.u_chart`, integrated over `cthickening |h| K_0` (the support of `v_h`).
The principal integrand uses the explicit weak `j`-partial of `v_h` as
provided in the input.

The hypothesis bundle encodes:

* the smooth-CS approximating sequence `v_h_n` (from `u_seq n`),
* L² and L²-gradient convergence on `cthickening |h| K_0`,
* the explicit weak partial `weak_partial_v_h j` of `v_h`.

This packages the result of applying `chart_bilinear_identity_h1_0` with
these data. -/
theorem variational_identity_at_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (hv_h_lp : MemLp (standardNirenbergTest (d := Module.finrank ℝ E)
        k h η D.u_chart) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (weak_partial_v_h j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (u_seq : ℕ → EuclN → ℝ)
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (u_seq n))
    (h_v_seq_supp : ∀ n,
      tsupport (standardNirenbergTest (d := Module.finrank ℝ E)
        k h η (u_seq n)) ⊆ Metric.cthickening |h| K_0)
    (h_v_seq_l2 :
      Tendsto (fun n => eLpNorm (fun x =>
        standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0))
    (h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ
          (standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n)) x) (EuclideanSpace.single j 1) -
          weak_partial_v_h j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0)) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              weak_partial_v_h j y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  -- Compactness of cthickening.
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  -- Set up smooth approximating sequence for v_h.
  set v_h : EuclN → ℝ := standardNirenbergTest (d := Module.finrank ℝ E)
    k h η D.u_chart with hvh_def
  set v_h_seq : ℕ → EuclN → ℝ := fun n =>
    standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n)
    with hvhseq_def
  have h_v_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v_h_seq n) := fun n =>
    (standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n).1
  have h_v_seq_cs : ∀ n, HasCompactSupport (v_h_seq n) := fun n =>
    (standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n).2
  -- Apply chart_bilinear_identity_h1_0 with K_0 := cthickening |h| K_0.
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick v_h weak_partial_v_h hv_h_lp hv_h_grad_lp
    v_h_seq h_v_seq_smooth h_v_seq_cs h_v_seq_supp h_v_seq_l2
    h_v_seq_grad_l2

/-! ## Step 3: Substitute the explicit weak partial of v_h

The weak `j`-partial of `v_h := D_{-h}^k(η² · D_h^k u)` is given by
`hasWeakPartialDeriv_standardNirenbergTest`:

  `weak_partial_v_h j = D_{-h}^k (η² · D_h^k (D.weak_partial j) +
                                   2η · ∂_j η · D_h^k u)`.

Substituting this formula into the principal integrand of
`variational_identity_at_v_h` gives the next stage of the chain. -/

set_option linter.unusedVariables false in
/-- After substituting the explicit weak `j`-partial of `v_h` (the symmetric
difference quotient `D_{-h}^k` of the discrete product rule), the
variational identity reads in terms of `D_{-h}^k`-shaped integrands.
The hypothesis bundle provides:

* the variational identity at `v_h` (the conclusion of
  `variational_identity_at_v_h`),
* the pointwise-a.e. equality between `weak_partial_v_h j` and the
  explicit difference-quotient formula. -/
theorem variational_identity_v_h_expanded
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (h_var_id_at_v_h :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                weak_partial_v_h j y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN))
    (h_weak_partial_eq : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y)
    (h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          weak_partial_v_h j y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (h_principal_integrable_subst : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  -- Rewrite the principal integral by substituting the formula for weak_partial_v_h.
  have h_principal_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                weak_partial_v_h j y)
          ∂(volume : Measure EuclN) =
        ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN) := by
    -- Use a.e. equality: split sum, use congruence of integrals.
    refine integral_congr_ae ?_
    -- ∀ᵐ y, ∑ i j ... = ∑ i j ... (substitute weak_partial_v_h j)
    have h_all : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y :=
      h_weak_partial_eq
    -- Combine over j (Fintype-indexed family of a.e. equalities).
    have h_combined : ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      ∀ j : Fin (Module.finrank ℝ E), weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y := by
      rw [ae_all_iff]
      exact h_all
    filter_upwards [h_combined] with y hy
    -- Pointwise: rewrite the sum using hy.
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j]
  rw [← h_principal_eq]
  exact h_var_id_at_v_h

/-! ## Step 4: Move D_{-h} via discrete integration by parts

For each `(i, j)`, the principal integrand contains a factor of the form
`F · D_{-h}^k G` where `F := weightedInvGramOnEuclid g α i j · D.weak_partial i`
and `G := η² · D_h^k (D.weak_partial j) + 2η · ∂_j η · D_h^k u_chart`. The
discrete integration-by-parts identity

  `∫ F · D_{-h}^k G dx = -∫ D_h^k F · G dx`

(via `integral_diffQuot_mul_eq_neg_integral_mul_diffQuot` with sign tracked
through `(i, -h) = -(-h) ≤ -h`) lets us shift the difference quotient
operator from `G` to `F`. The hypothesis bundle exposes the per-`(i, j)` IBP
identity over the cthickening (extended by zero outside if needed). -/

set_option linter.unusedVariables false in
/-- After moving the outer `D_{-h}^k` from `G` onto `F` via discrete IBP,
the principal integrand has the shape

  `- D_h^k(F) · G = - D_h^k(weightedInvGramOnEuclid · D.weak_partial i) ·
    (η² · D_h^k (D.weak_partial j) + 2η · ∂_j η · D_h^k u_chart)`,

and the variational identity rearranges accordingly. The hypothesis bundle
provides the IBP equality. -/
theorem variational_identity_after_ibp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_expanded :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN))
    (h_ibp_per_ij : ∀ i j : Fin (Module.finrank ℝ E),
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y
        ∂(volume : Measure EuclN) =
      - ∫ y in Metric.cthickening |h| K_0,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weak_partial i z) y *
          ((η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y)
        ∂(volume : Measure EuclN))
    (h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (h_principal_integrable_after : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weak_partial i z) y *
        ((η y) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y))
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) :
    -(∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weak_partial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart y))
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  -- Swap sum and integral.
  have h_int_swap_before :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      intro j _
      exact h_principal_integrable i j
    · intro i _
      exact integrable_finset_sum _ (fun j _ => h_principal_integrable i j)
  have h_int_swap_after :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weak_partial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart y)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      intro j _
      exact h_principal_integrable_after i j
    · intro i _
      exact integrable_finset_sum _ (fun j _ => h_principal_integrable_after i j)
  -- Now relate the two sums via the per-(i,j) IBP identity.
  have h_per_ij_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y
            ∂(volume : Measure EuclN)) =
      - ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Metric.cthickening |h| K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y)
              ∂(volume : Measure EuclN) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h_ibp_per_ij i j
  -- Combine: rewrite the principal integral in h_expanded.
  rw [h_int_swap_before, h_per_ij_eq, ← h_int_swap_after] at h_expanded
  -- h_expanded now has the form -(after) + ... = ...
  exact h_expanded

/-! ## Step 5: Apply the discrete product rule

The integrand after IBP contains `D_h^k(weightedInvGramOnEuclid · D.weak_partial i)`.
The discrete product rule

  `D_h^k(f · g)(x) = τ_h(f)(x) · D_h^k(g)(x) + D_h^k(f)(x) · g(x)`

splits this into two terms. Combined with the binary structure of the
right factor (`η² · D_h^k(g_j) + 2η · ∂_j η · D_h^k(u)`), this expands the
single principal-after-IBP term into FOUR terms matching the symbolic
pieces `principalTerm_chartBilinear`, `cross_1_term_chartBilinear`,
`cross_2_term_chartBilinear`, `cross_3_term_chartBilinear`. The hypothesis
bundle exposes the per-`(i, j)` discrete product-rule identity. -/

set_option linter.unusedVariables false in
/-- After applying the discrete product rule on the principal IBP'd term,
the four cross terms emerge and the variational identity rearranges into

  `principal + cross_1 + cross_2 + cross_3 + f_term = c_term`,

matching the symbolic pieces `principalTerm_chartBilinear`,
`cross_1_term_chartBilinear`, `cross_2_term_chartBilinear`,
`cross_3_term_chartBilinear`, `f_term_chartBilinear`,
`c_term_chartBilinear`. The hypothesis bundle provides the algebraic
expansion as a per-`(i, j)` integral identity. -/
theorem variational_identity_after_product_rule
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_after_ibp :
      -(∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
          ∂(volume : Measure EuclN))
    (h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h)
    (h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      c_term_chartBilinear (I := I) (M := M) D K_0 η k h)
    (h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      f_term_chartBilinear (I := I) (M := M) D K_0 η k h) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  -- Rewrite using h_principal_in_K_0_eq, h_c_term_eq, h_f_term_eq.
  rw [h_principal_in_K_0_eq, h_c_term_eq, h_f_term_eq] at h_after_ibp
  -- h_after_ibp now reads:
  -- -(principal + cross_1 + cross_2 + cross_3) + c_term = f_term
  -- i.e., c_term - (principal + cross_1 + cross_2 + cross_3) = f_term
  -- Rearrange: principal + cross_1 + cross_2 + cross_3 + f_term = c_term.
  linarith

end SubstitutionDischargeIBPExpand
end Sobolev
end Analysis
end DifferentialGeometry
