import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.CutoffChartComponentWkpNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# Quantitative iterated-Sobolev norm bounds for the eigenvector partition-of-unity
chart components

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, this file is the
*explicit-norm* twin of two qualitative partition-of-unity regularity lemmas for
the connection-Laplacian eigenvector's chart components.

Where `eigenvectorVec_pou_memWkp` records only that the partition-of-unity
Euclidean chart component of the eigenvector vector
`tensorResolventEigenbasisVec h_atlas i` is `W^{N,2}`-regular, and
`eigenvectorCovGrad_pou_memWkp` records only that the partition-of-unity chart
component of the section-level covariant gradient
`tensorCovGradL2Compl g r s (eigenvectorResolvent …)` is `W^{K,2}`-regular, the
present file produces explicit nonnegative constants and norm inequalities.

## The bounds

* The eigenvector chart component equals `μ⁻¹` times the chart component of the
  `L²`-coercion of the eigenvector resolvent; the iterated Sobolev norm is
  scalar-homogeneous, so its order-`N` norm is `‖μ⁻¹‖` times the order-`N` norm
  of the resolvent-coercion chart component — recorded as a single-constant
  inequality `eigenvectorVec_pou_wkpNorm_le`.

* The committed identity `eigenvectorCovGrad_pou_chartComponent_ae_eq` decomposes
  the `μ⁻¹`-rescaled covariant-gradient chart component into a weak chart partial,
  a partition-of-unity Leibniz cross-term limit, and a Christoffel-correction
  limit. Each of the three is bounded — through `wkpNorm_chosenWeakPartial_le_wkpNorm_succ`,
  the quantitative cutoff bridge `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`,
  the quantitative Leibniz bound `wkpNorm_smul_smooth_bounded_le`, and a
  quantitative "smooth coefficient × kernel-vanishing factor" closure — by a
  constant times the sum, over the chart centre `β` adjoined to the transport
  chart centres of `β` and over the component multi-indices, of the order-`(K+1)`
  norms of the resolvent-coercion partition-of-unity components. Collecting the
  per-term constants and rescaling by `μ` gives the single global constant of
  `eigenvectorCovGrad_pou_wkpNorm_le`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The triangle inequality for `wkpNorm` under subtraction

The iterated-Sobolev API ships the triangle inequality `wkpNorm_add_le` for
addition; the subtraction analogue is recorded here. The order-`k` norm is
invariant under negation (`wkpNorm_const_smul` with `c = -1`, whose `ℝ≥0∞`-norm
is `1`), so `u − v = u + (−v)` and `wkpNorm_add_le` deliver it. -/

private lemma wkpNorm_sub_le
    {d : ℕ} [NeZero d] {k : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k 2 u Ω) (hv : MemWkp (d := d) k 2 v Ω) :
    wkpNorm (d := d) k 2 (fun y => u y - v y) Ω ≤
      wkpNorm (d := d) k 2 u Ω + wkpNorm (d := d) k 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := d) k 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := d) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := d) (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : wkpNorm (d := d) k 2 (fun y => - v y) Ω =
      wkpNorm (d := d) k 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := d) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

/-! ## A finite-sum closure for `MemWkp K 2`

The Christoffel-correction limit is a finite sum over component multi-indices;
the helper below propagates `MemWkp K 2` through a finite sum indexed by an
arbitrary `Finset`. -/

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompleteSpace E]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum
    {α : M} {K : ℕ} {ι : Type*} (T : Finset ι)
    {F : ι → EuclN → ℝ}
    (hF : ∀ i ∈ T, MemWkp (d := Module.finrank ℝ E) K 2 (F i)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ T, F i y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i T hi ih =>
      have hi_mem : MemWkp (d := Module.finrank ℝ E) K 2 (F i)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hF i (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i T, F j y) =
          (fun y => F i y + ∑ j ∈ T, F j y) := by
        funext y; rw [Finset.sum_insert hi]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi_mem hsum

/-! ## The quantitative smooth-coefficient `wkpNorm` bound with ae-vanishing

Given a coefficient smooth on the open chart target, a factor in `MemWkp K 2` on
the chart target that vanishes almost everywhere off the compact
partition-of-unity kernel, the product `coef · factor` lies in `MemWkp K 2` on
the chart target and its order-`K` Sobolev norm is bounded by an explicit
constant times the order-`K` norm of the factor.

The proof cuts the coefficient off to a globally smooth compactly supported
representative `χ · coef` (smooth cutoff `χ` equal to `1` on a closed thickening
of the kernel, supported in the chart target). Its iterated derivatives up to
order `K` are uniformly bounded, so the global-smoothness Leibniz bound
`wkpNorm_smul_smooth_bounded_le` applies. The cut-off product `(χ · coef) ·
factor` agrees almost everywhere with `coef · factor` on `volume.restrict` of the
chart target — on the thickening `χ = 1`; off the kernel the factor ae-vanishes —
so `wkpNorm` and `MemWkp` transfer.

This is the quantitative companion of the qualitative `memWkp_coef_mul_factor`. -/

private lemma wkpNorm_coef_mul_factor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            wkpNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hKα_compact : IsCompact Kα := chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : Kα ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  -- A smooth cutoff `χ` equal to `1` on `cthickening δ Kα`, supported in `Ω`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ω`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- Uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- `(χ · coef) · factor ∈ MemWkp K 2`, via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  -- The quantitative Leibniz bound for the cutoff product `χ · coef`.
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  -- `(χ · coef) · factor =ᵃᵉ coef · factor` on `volume.restrict Ω`.
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  -- The factor ae-vanishes off `Kα` against `volume.restrict Ω` (the chart `L²`
  -- measure is, definitionally, `volume.restrict Ω`).
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kα → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    -- On `Cδ ∩ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy.2
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    -- On `Ω \ Cδ ⊆ Ω \ Kα`: the factor ae-vanishes, so both products ae-vanish.
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
          (volume : Measure EuclN).restrict Ω :=
        Measure.restrict_mono Set.diff_subset le_rfl
      have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          factor y = 0 := by
        have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            y ∉ Kα → factor y = 0 :=
          (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
        have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
        filter_upwards [h_lift, h_off] with y hy hy_mem
        exact hy (fun hyK => hy_mem.2 (hKα_in_Cδ hyK))
      filter_upwards [h_factor_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the ae-equality.
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt hKc_pos, ?_⟩
  -- Transfer the `wkpNorm` bound through the ae-equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

/-! ## The eigenvector chart component as a rescaled resolvent chart component

The regularity input is phrased for the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i)` of the
`H¹`-completion resolvent. The canonical eigenvector chart component references
the eigenvector vector `tensorResolventEigenbasisVec h_atlas i` itself. The two
differ by the nonzero scalar `μ⁻¹` (`eigenvector_chartComponent_eq`); `MemWkp` is
scalar-invariant and `wkpNorm` is scalar-homogeneous. -/

omit [CompleteSpace E] in
/-- The partition-of-unity Euclidean chart component of the eigenvector vector
`tensorResolventEigenbasisVec h_atlas i` is `MemWkp N 2` on a chart target, and
its order-`N` iterated Sobolev norm is `‖μ⁻¹‖` times that of the resolvent-coercion
chart component, given the `MemWkp N 2` regularity of the latter. -/
private lemma eigenvectorVec_pou_memWkp_and_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s)
    (h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      wkpNorm (d := Module.finrank ℝ E) N 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          wkpNorm (d := Module.finrank ℝ E) N 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq`). Pass to `coeFn` and rescale.
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_atlas i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  -- `MemWkp` is scalar-invariant: transfer through the a.e. equality.
  have h_mem : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
      (MemWkp.const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)
  refine ⟨h_mem, ?_⟩
  -- `wkpNorm` is scalar-homogeneous: transfer through the a.e. equality, then
  -- apply `wkpNorm_const_smul`.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω =
      wkpNorm (d := Module.finrank ℝ E) N 2
        (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  rw [h_norm_eq,
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹]
  refine le_of_eq ?_
  rw [← ofReal_norm]

/-! ## Headline 1 — the quantitative eigenvector chart-component norm bound -/

omit [CompleteSpace E] in
/-- **Quantitative iterated Sobolev norm bound for the eigenvector
partition-of-unity chart component.** For a closed Riemannian manifold `(M, g)`,
ranks `(r, s)`, an eigenbasis index `i`, an iteration order `N`, a chart centre
`β` and a component multi-index `Q`, if every partition-of-unity Euclidean chart
component of the `L²`-coercion of the eigenvector resolvent
`eigenvectorResolvent g r s h_atlas i` is iterated Sobolev regular of order `N`
(`W^{N,2}`), then there is a nonnegative constant `C` for which the order-`N`
iterated Euclidean Sobolev norm of the partition-of-unity Euclidean chart
`Q`-component of the eigenvector vector `tensorResolventEigenbasisVec h_atlas i`
is bounded by `C` times the order-`N` norm of the corresponding resolvent-coercion
chart component. The eigenvector chart component is `μ⁻¹` times the
resolvent-coercion chart component, and `wkpNorm` is scalar-homogeneous; the
constant `‖μ⁻¹‖` absorbs the resolvent-eigenvalue rescale. -/
theorem eigenvectorVec_pou_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) N 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal C *
          wkpNorm (d := Module.finrank ℝ E) N 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  refine ⟨‖(i.fst.val)⁻¹‖, norm_nonneg _, ?_⟩
  exact (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
    g r s h_atlas i N β Q (h_pou β Q)).2

/-! ## Quantitative bounds for the three covariant-gradient limit terms

The three named limit objects of the committed identity
`eigenvectorCovGrad_pou_chartComponent_ae_eq` are bounded — in `MemWkp` and in
`wkpNorm` — by a constant times an aggregate built from the order-`(K+1)`
iterated Sobolev norms of the resolvent-coercion partition-of-unity chart
components.

The aggregate `covGradAggregate β` is the sum of the order-`(K+1)`
chart-component norms at the chart centre `β` itself and the double sum of those
norms over the transport chart centres of `β` and the component multi-indices.
This two-part form avoids a `Finset.insert`, which would require decidable
equality on the manifold. -/

section CovGradTerms

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)

/-- Abbreviation: the order-`(K+1)` iterated Sobolev norm of the
resolvent-coercion partition-of-unity Euclidean chart `Q`-component at a chart
centre `β'`. -/
private def chartCompNorm (β' : M) (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β')

/-- Abbreviation: the order-`(K+1)` resolvent-coercion aggregate — the sum of the
chart-component norms at the chart centre `β` itself and the double sum over the
transport chart centres of `β`. -/
private def covGradAggregate (β : M) : ℝ≥0∞ :=
  (∑ Q : TensorCompIdx (E := E) r s,
      chartCompNorm (I := I) (M := M) g r s h_atlas i K β Q)
    + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartCompNorm (I := I) (M := M) g r s h_atlas i K β' Q

/-- A single resolvent-coercion order-`(K+1)` chart-component norm at the chart
centre `β` itself is dominated by the aggregate. -/
private lemma chartCompNorm_center_le_covGradAggregate
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    chartCompNorm (I := I) (M := M) g r s h_atlas i K β Q
      ≤ covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
  classical
  refine le_trans ?_ le_self_add
  exact Finset.single_le_sum
    (f := fun Q' : TensorCompIdx (E := E) r s =>
      chartCompNorm (I := I) (M := M) g r s h_atlas i K β Q')
    (fun _ _ => zero_le _) (Finset.mem_univ Q)

/-- A single resolvent-coercion order-`(K+1)` chart-component norm at a transport
chart centre `β' ∈ transportChartCenters β` is dominated by the aggregate. -/
private lemma chartCompNorm_transport_le_covGradAggregate
    {β β' : M} (hβ' : β' ∈ transportChartCenters (I := I) (M := M) β)
    (Q : TensorCompIdx (E := E) r s) :
    chartCompNorm (I := I) (M := M) g r s h_atlas i K β' Q
      ≤ covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
  classical
  refine le_trans ?_ le_add_self
  refine le_trans ?_
    (Finset.single_le_sum
      (f := fun β'' : M =>
        ∑ Q' : TensorCompIdx (E := E) r s,
          chartCompNorm (I := I) (M := M) g r s h_atlas i K β'' Q')
      (fun _ _ => zero_le _) hβ')
  exact Finset.single_le_sum
    (f := fun Q' : TensorCompIdx (E := E) r s =>
      chartCompNorm (I := I) (M := M) g r s h_atlas i K β' Q')
    (fun _ _ => zero_le _) (Finset.mem_univ Q)

/-- **The principal weak-partial term is `W^{K,2}` with an aggregate norm bound.**
The established weak chart partial `eigenvectorChartWeakPartial` of the
eigenvector chart component is a genuine weak partial of that chart component;
since the chart component is `W^{K+1,2}`, the weak partial is `W^{K,2}` and its
order-`K` norm is bounded — through `wkpNorm_chosenWeakPartial_le_wkpNorm_succ` —
by the order-`(K+1)` norm of the eigenvector chart component, hence by `‖μ⁻¹‖`
times the aggregate. -/
private lemma eigenvectorChartWeakPartial_memWkp_and_wkpNorm_le
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The eigenvector chart component is `W^{K+1,2}`, with a norm bound by
  -- `‖μ⁻¹‖` times the resolvent-coercion order-`(K+1)` norm.
  obtain ⟨hu, hu_norm⟩ := eigenvectorVec_pou_memWkp_and_wkpNorm_le
    (I := I) (M := M) g r s h_atlas i (K + 1) β P (h_pou_phi β P)
  -- `eigenvectorChartWeakPartial` is a genuine weak `k`-th partial of that chart
  -- component (the committed headline).
  have hg_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i β P k
  -- `eigenvectorChartWeakPartial` is locally `L²` on the chart target.
  have hg_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k)
      ((volume : Measure EuclN).restrict Ω) := by
    have h_memLp : MemLp (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s h_atlas i β P k) 2
        ((volume : Measure EuclN).restrict Ω) := by
      rw [eigenvectorChartWeakPartial]
      exact Lp.memLp _
    exact h_memLp.locallyIntegrable (by norm_num)
  -- `u ∈ W^{1,2}(Ω)`, so its chosen weak `k`-th partial is a genuine weak `k`-th
  -- partial of `u` and lies in `L²(Ω)`.
  have hu_W1 : DeGiorgi.MemW1p 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem (d := Module.finrank ℝ E) hu_W1 k
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem (d := Module.finrank ℝ E)
      hu_W1 k).locallyIntegrable (by norm_num)
  -- Uniqueness of weak partials: the weak partial and the chosen partial agree
  -- almost everywhere.
  have h_ae : eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq (d := Module.finrank ℝ E) hΩ_open
      hg_weak h_chosen_weak hg_loc h_chosen_loc
  -- The chosen partial of a `W^{K+1,2}` function is `W^{K,2}`.
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω) Ω :=
    hu.chosenWeakPartial_mem k
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i β P k) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr h_chosen_memWkp
  refine ⟨h_memWkp, ‖(i.fst.val)⁻¹‖, norm_nonneg _, ?_⟩
  -- Transfer the `wkpNorm` along the a.e. equality, then apply the chosen-weak-
  -- partial order-drop bound and the eigenvector rescale.
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω) Ω
        ≤ wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := Module.finrank ℝ E) K
        hΩ_open _ k
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := hu_norm
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          covGradAggregate (I := I) (M := M) g r s h_atlas i K β :=
      mul_le_mul_of_nonneg_left
        (chartCompNorm_center_le_covGradAggregate (I := I) (M := M)
          g r s h_atlas i K β P) (zero_le _)

/-- **The Leibniz cross-term limit is `W^{K,2}` with an aggregate norm bound.**
By definition `covGradPouLeibnizCrossLimit` is a globally `C^∞`, compactly
supported multiplier times the cutoff Euclidean chart component of the
eigenvector. The cutoff component norm is bounded — through the quantitative
cutoff bridge `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou`, fed the order-`K`
eigenvector chart-component regularity — by a constant times the order-`K` sum of
the transport components, hence (via the eigenvector rescale and order
monotonicity) by a constant times the aggregate; the multiplier preserves the
bound through `wkpNorm_smul_smooth_bounded_le`. -/
private lemma covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (covGradPouLeibnizCrossLimit (I := I) (M := M) g r s h_atlas i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (covGradPouLeibnizCrossLimit (I := I) (M := M) g r s h_atlas i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The order-`K` eigenvector chart components are `W^{K,2}` (resolvent rescale).
  have h_eigen_K : ∀ (β' : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β' Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β') := by
    intro β' Q
    exact (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K β' Q
      ((h_pou_phi β' Q).le_of_le (Nat.le_succ K))).1
  -- The chart-pushed partition-of-unity weight is globally `C^∞` and compactly
  -- supported (its closed manifold support sits inside the chart source).
  have hpou_supp : tsupport
      ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β
  have hpou_pushed_smooth : ContDiff ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M)
      (chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯).contMDiff hpou_supp
  have hpou_pushed_cs : HasCompactSupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hpou_supp
  -- The cross-term multiplier — the `k`-th chart-Euclidean partial — is globally
  -- `C^∞` and compactly supported.
  have hmult_smooth : ContDiff ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    euclidPartial_contDiff (E := E) hpou_pushed_smooth k
  have hmult_smooth' : ContDiff ℝ (⊤ : ℕ∞)
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    hmult_smooth
  have hmult_cs : HasCompactSupport
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
    apply HasCompactSupport.of_support_subset_isCompact hpou_pushed_cs
    intro y hy
    by_contra hy_off
    exact hy (by
      have h := euclidPartial_def (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
      have hopen : IsOpen ((tsupport
          (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have hevt : (chartPushedRaw I β
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy_off)
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [h, hevt.fderiv_eq]
      simp)
  -- A uniform bound on the multiplier's iterated derivatives up to order `K`.
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hmult_smooth' hmult_cs K
  -- The cutoff Euclidean chart component of the eigenvector is `W^{K,2}`, by the
  -- qualitative cutoff ↔ partition-of-unity bridge.
  have hcutoff_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P K
      (fun β' Q => h_eigen_K β' Q)
  -- The quantitative cutoff bridge: order-`K` norm of the cutoff component is
  -- bounded by a constant times the order-`K` transport sum.
  obtain ⟨Ccut, hCcut_nn, hCcut_bd⟩ :=
    wkpNorm_tensorL2ChartComponentCutoff_le_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P K
      (fun β' Q => h_eigen_K β' Q)
  -- The quantitative Leibniz bound for the smooth multiplier.
  obtain ⟨Kmul, hKmul_pos, hKmul_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hmult_smooth'
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  -- The product `multiplier · cutoff component` is `W^{K,2}`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M) g r s h_atlas i β P k) Ω := by
    have h_prod : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hmult_smooth'
        (fun j _hj y _hy => hC₀_bd y j _hj) hcutoff_memWkp
    change MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
    exact h_prod
  -- Each order-`K` transport component norm is bounded — through the eigenvector
  -- rescale — by `‖μ⁻¹‖` times the corresponding aggregate term.
  have h_transport_le : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
      ∀ Q : TensorCompIdx (E := E) r s,
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β' Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β')
        ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
    intro β' hβ' Q
    refine le_trans (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K β' Q
      ((h_pou_phi β' Q).le_of_le (Nat.le_succ K))).2 ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    refine le_trans (wkpNorm_mono_order (d := Module.finrank ℝ E)
      (Nat.le_succ K) _ _) ?_
    exact chartCompNorm_transport_le_covGradAggregate (I := I) (M := M)
      g r s h_atlas i K hβ' Q
  -- Sum the per-transport bounds: the order-`K` transport double sum is bounded
  -- by `(card · ‖μ⁻¹‖)` times the aggregate.
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s h_atlas i K β
    with hSaggr_def
  have h_double_le :
      (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β' Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β'))
        ≤ (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ _Q : TensorCompIdx (E := E) r s,
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
    Finset.sum_le_sum (fun β' hβ' =>
      Finset.sum_le_sum (fun Q _ => h_transport_le β' hβ' Q))
  have h_double_const :
      (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr := by
    have h_sum : (∑ _β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ _Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr)
        = (((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr))) := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        nsmul_eq_mul]
    rw [h_sum]
    rw [show ENNReal.ofReal
          (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
              ‖(i.fst.val)⁻¹‖))
        = ((transportChartCenters (I := I) (M := M) β).card : ℝ≥0∞) *
            ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ≥0∞) *
              ENNReal.ofReal ‖(i.fst.val)⁻¹‖) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]]
    ring
  -- Assemble: the cutoff order-`K` norm is bounded by a constant times the
  -- aggregate.
  have h_cutoff_le : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal Ccut *
        (ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)) * Saggr) := by
    refine le_trans hCcut_bd ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    rw [← h_double_const]
    exact h_double_le
  -- Carry the multiplier and collect the constant.
  refine ⟨h_prod_memWkp,
    Kmul * (Ccut *
      (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
        ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
          ‖(i.fst.val)⁻¹‖))),
    by positivity, ?_⟩
  -- `covGradPouLeibnizCrossLimit` is, definitionally, `multiplier · cutoff`.
  have h_unfold : wkpNorm (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M) g r s h_atlas i β P k) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    rfl
  rw [h_unfold]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          euclidPartial (E := E) k
              (chartPushedRaw I β
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
        ≤ ENNReal.ofReal Kmul *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                  β P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      hKmul_bd hcutoff_memWkp
    _ ≤ ENNReal.ofReal Kmul *
          (ENNReal.ofReal Ccut *
            (ENNReal.ofReal
                (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                  ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                    ‖(i.fst.val)⁻¹‖)) * Saggr)) :=
      mul_le_mul_of_nonneg_left h_cutoff_le (zero_le _)
    _ = ENNReal.ofReal
          (Kmul * (Ccut *
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
                ‖(i.fst.val)⁻¹‖)))) * Saggr := by
      rw [ENNReal.ofReal_mul (le_of_lt hKmul_pos),
        ENNReal.ofReal_mul hCcut_nn]
      ring

/-- **The Christoffel-correction limit is `W^{K,2}` with an aggregate norm
bound.** By definition `covGradChristoffelLimit` is a finite sum, over component
multi-indices, of an indicator-cut chart-target-`C^∞` coefficient times an
eigenvector chart component. The coefficient is `C^∞` on the chart target, and
the chart component is `W^{K,2}` and vanishes almost everywhere off the
partition-of-unity kernel — so each summand is `W^{K,2}` with norm bounded
(through `wkpNorm_coef_mul_factor_le` and the eigenvector rescale) by a constant
times the aggregate; a finite sum of such bounds is again of this form. -/
private lemma covGradChristoffelLimit_memWkp_and_wkpNorm_le
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (covGradChristoffelLimit (I := I) (M := M) g r s h_atlas i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M) g r s h_atlas i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s h_atlas i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s h_atlas i K β
    with hSaggr_def
  -- The summand family of `covGradChristoffelLimit`.
  set F : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) β)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s β k P.1 p.1 P.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
          EuclN → ℝ) y with hF_def
  -- Each summand `p` is `W^{K,2}`, with norm bounded by a constant times the
  -- aggregate.
  have h_summand : ∀ p : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          wkpNorm (d := Module.finrank ℝ E) K 2 (F p) Ω
            ≤ ENNReal.ofReal C * Saggr := by
    intro p
    -- The eigenvector chart `p`-component is `W^{K,2}`, with norm `≤ ‖μ⁻¹‖`
    -- times the aggregate (the `p`-component at `β` is an aggregate term).
    obtain ⟨hfactor_memWkp, hfactor_norm⟩ :=
      eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
        g r s h_atlas i K β p ((h_pou_phi β p).le_of_le (Nat.le_succ K))
    have hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
        y ∉ chartPouKernel (I := I) (M := M) β →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
            EuclN → ℝ) y = 0 :=
      tensorL2ChartComponent_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p
    -- "Smooth coefficient × kernel-vanishing factor": the product without the
    -- indicator is `W^{K,2}`, with norm bounded by a constant times the factor
    -- norm.
    obtain ⟨h_no_indicator_memWkp, Ccoef, hCcoef_nn, hCcoef_bd⟩ :=
      wkpNorm_coef_mul_factor_le (I := I) (M := M) β K
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s β k P.1 p.1 P.2 p.2)
        hfactor_memWkp hfactor_ae_zero
    -- The indicator-cut product agrees with the indicator-free product almost
    -- everywhere.
    have h_ae : (fun y =>
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
              EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω] (F p) := by
      have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          y ∉ chartPouKernel (I := I) (M := M) β →
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
              EuclN → ℝ) y = 0 := hfactor_ae_zero
      filter_upwards [hfactor_ae_zero'] with y hy
      show covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
              EuclN → ℝ) y = F p y
      simp only [hF_def]
      by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) β
      · rw [Set.indicator_of_mem hyK]
      · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
    have hF_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      (MemWkp_congr_ae (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_no_indicator_memWkp
    refine ⟨hF_memWkp, Ccoef * ‖(i.fst.val)⁻¹‖,
      mul_nonneg hCcoef_nn (norm_nonneg _), ?_⟩
    -- Transfer the `wkpNorm` along the a.e. equality, then chain the bounds.
    rw [← wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae]
    calc
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            covDerivLowerOrderCoeff (I := I) (M := M)
                g r s β k P.1 p.1 P.2 p.2 y *
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β p :
                EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal Ccoef *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β) := hCcoef_bd
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              wkpNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) :=
        mul_le_mul_of_nonneg_left hfactor_norm (zero_le _)
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              chartCompNorm (I := I) (M := M) g r s h_atlas i K β p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (wkpNorm_mono_order (d := Module.finrank ℝ E)
              (Nat.le_succ K) _ _) (zero_le _)) (zero_le _)
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (chartCompNorm_center_le_covGradAggregate (I := I) (M := M)
              g r s h_atlas i K β p) (zero_le _)) (zero_le _)
      _ = ENNReal.ofReal (Ccoef * ‖(i.fst.val)⁻¹‖) * Saggr := by
        rw [ENNReal.ofReal_mul hCcoef_nn]; ring
  -- A finite sum of the per-summand bounds.
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω :=
    memWkp_finset_sum (I := I) (M := M) Finset.univ
      (fun p _ => (h_summand p).1)
  have h_christoffel_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M) g r s h_atlas i β P k) Ω := by
    have h_unfold : (covGradChristoffelLimit (I := I) (M := M)
        g r s h_atlas i β P k) =
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) := rfl
    rw [h_unfold]
    exact h_sum_memWkp
  -- The aggregate constant: sum the per-summand constants.
  choose Cf hCf_nn hCf_bd using fun p => (h_summand p).2
  refine ⟨h_christoffel_memWkp,
    ∑ p : TensorCompIdx (E := E) r s, Cf p,
    Finset.sum_nonneg (fun p _ => hCf_nn p), ?_⟩
  -- `covGradChristoffelLimit` is, definitionally, the finite sum `∑ p F p`.
  have h_unfold : wkpNorm (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M) g r s h_atlas i β P k) Ω =
      wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω := rfl
  rw [h_unfold]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω
        ≤ ∑ p : TensorCompIdx (E := E) r s,
            wkpNorm (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      wkpNorm_sum_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open Finset.univ F
        (fun p _ => (h_summand p).1)
    _ ≤ ∑ p : TensorCompIdx (E := E) r s, ENNReal.ofReal (Cf p) * Saggr :=
      Finset.sum_le_sum (fun p _ => hCf_bd p)
    _ = (∑ p : TensorCompIdx (E := E) r s, ENNReal.ofReal (Cf p)) * Saggr := by
      rw [← Finset.sum_mul]
    _ = ENNReal.ofReal (∑ p : TensorCompIdx (E := E) r s, Cf p) * Saggr := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => hCf_nn p)]

end CovGradTerms

/-! ## Headline 2 — the quantitative covariant-gradient chart-component norm bound

The committed identity `eigenvectorCovGrad_pou_chartComponent_ae_eq` expresses the
`μ⁻¹`-rescaled covariant-gradient chart component as the three-term sum
`principal − cross + Christoffel`. Each of the three is `W^{K,2}` with norm
bounded by a constant times the aggregate; `wkpNorm` is invariant under
almost-everywhere equality, subadditive over the three terms, and homogeneous
under the `μ`-rescale. -/

/-- **Quantitative iterated Sobolev norm bound for the covariant-gradient
partition-of-unity chart component.** For a closed Riemannian manifold `(M, g)`,
ranks `(r, s)`, an eigenbasis index `i`, an iteration order `K`, a chart centre
`β` and an `(r, s + 1)`-component multi-index `Q'`, if every partition-of-unity
Euclidean chart component of the `L²`-coercion of the eigenvector resolvent
`eigenvectorResolvent g r s h_atlas i` is iterated Sobolev regular of order
`K + 1` (`W^{K+1,2}`), then there is a nonnegative constant `C` for which the
order-`K` iterated Euclidean Sobolev norm of the partition-of-unity Euclidean
chart `Q'`-component of the section-level covariant gradient
`tensorCovGradL2Compl g r s` of that resolvent is bounded by `C` times the
aggregate built from the order-`(K+1)` norms of the resolvent-coercion
partition-of-unity chart components — the sum of those norms at the chart centre
`β` itself together with the double sum over the transport chart centres of `β`
and the component multi-indices.

The committed identity `eigenvectorCovGrad_pou_chartComponent_ae_eq` decomposes
the `μ⁻¹`-rescaled covariant-gradient chart component into a weak chart partial,
a partition-of-unity Leibniz cross-term limit, and a Christoffel-correction
limit; each of the three is bounded by a constant times that aggregate, and the
constant `C` collects the per-term constants together with the
resolvent-eigenvalue rescale `‖μ‖`. -/
theorem eigenvectorCovGrad_pou_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2Compl (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal C *
          ((∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s h_atlas i))
                        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set P : TensorCompIdx (E := E) r s := (Q'.1, Matrix.vecTail Q'.2) with hP_def
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s h_atlas i K β
    with hSaggr_def
  -- The three named limit terms: each `W^{K,2}` with an aggregate norm bound.
  obtain ⟨h1_mem, C1, hC1_nn, hC1_bd⟩ :=
    eigenvectorChartWeakPartial_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K h_pou_phi β P (Q'.2 0)
  obtain ⟨h2_mem, C2, hC2_nn, hC2_bd⟩ :=
    covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K h_pou_phi β P (Q'.2 0)
  obtain ⟨h3_mem, C3, hC3_nn, hC3_bd⟩ :=
    covGradChristoffelLimit_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s h_atlas i K h_pou_phi β P (Q'.2 0)
  -- The three-term sum `principal − cross + Christoffel` is `W^{K,2}`, with norm
  -- bounded by `(C1 + C2 + C3)` times the aggregate.
  have h_sub_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h1_mem h2_mem
  have h_sum_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem
  have h_sum_norm_le : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y) Ω
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Saggr := by
    have h_tri : wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0) y) Ω
        ≤ (wkpNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartWeakPartial (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0)) Ω
            + wkpNorm (d := Module.finrank ℝ E) K 2
                (covGradPouLeibnizCrossLimit (I := I) (M := M)
                  g r s h_atlas i β P (Q'.2 0)) Ω)
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (covGradChristoffelLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0)) Ω :=
      le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem)
        (add_le_add
          (wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open h1_mem h2_mem)
          (le_refl (wkpNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0)) Ω)))
    refine le_trans h_tri ?_
    have h_each : (wkpNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0)) Ω
          + wkpNorm (d := Module.finrank ℝ E) K 2
              (covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0)) Ω)
        + wkpNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0)) Ω
        ≤ (ENNReal.ofReal C1 * Saggr + ENNReal.ofReal C2 * Saggr)
          + ENNReal.ofReal C3 * Saggr :=
      add_le_add (add_le_add hC1_bd hC2_bd) hC3_bd
    refine le_trans h_each (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) hC3_nn,
      ENNReal.ofReal_add hC1_nn hC2_nn]
    ring
  -- The committed identity: the `μ⁻¹`-rescaled chart component agrees almost
  -- everywhere with the three-term sum.
  have h_ae := eigenvectorCovGrad_pou_chartComponent_ae_eq (I := I) (M := M)
    g r s h_atlas i β Q'
  have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q')
  -- `μ⁻¹` times the chart-component coercion agrees a.e. with the three-term sum.
  have h_scaled_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y) := by
    have h_combined : (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s h_atlas i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s h_atlas i β P (Q'.2 0) y) := by
      filter_upwards [h_smul, h_ae] with y hy_smul hy_ae
      rw [← hy_ae, hy_smul, Pi.smul_apply, smul_eq_mul]
    exact h_combined
  -- The `μ⁻¹`-scaled chart component is `W^{K,2}` with norm `≤ (C1+C2+C3)`
  -- times the aggregate.
  have h_scaled_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae).mpr h_sum_mem
  have h_scaled_norm : wkpNorm (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Saggr := by
    rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae]
    exact h_sum_norm_le
  -- Rescale by `μ`: `wkpNorm` is scalar-homogeneous, so the chart component norm
  -- is `‖μ‖` times the `μ⁻¹`-scaled norm.
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_chart_eq_scaled : (fun y => ((tensorL2ChartComponent (I := I) (M := M)
        g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) =
      (fun y => i.fst.val * ((i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) := by
    funext y
    rw [mul_inv_cancel_left₀ hμ_ne]
  refine ⟨‖i.fst.val‖ * (C1 + C2 + C3),
    mul_nonneg (norm_nonneg _) (by positivity), ?_⟩
  rw [show ((∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')) = Saggr from rfl]
  rw [h_chart_eq_scaled]
  calc
    wkpNorm (d := Module.finrank ℝ E) K 2
        (fun y => i.fst.val * ((i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) Ω
        = ‖i.fst.val‖ₑ *
            wkpNorm (d := Module.finrank ℝ E) K 2
              (fun y => (i.fst.val)⁻¹ *
                ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      wkpNorm_const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_mem i.fst.val
    _ ≤ ‖i.fst.val‖ₑ * (ENNReal.ofReal (C1 + C2 + C3) * Saggr) :=
      mul_le_mul_of_nonneg_left h_scaled_norm (zero_le _)
    _ = ENNReal.ofReal (‖i.fst.val‖ * (C1 + C2 + C3)) * Saggr := by
      rw [← mul_assoc, ← ofReal_norm (x := i.fst.val),
        ← ENNReal.ofReal_mul (norm_nonneg _)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
