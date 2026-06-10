import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder

/-! # The sharp-order `C²` Sobolev embedding of the covariant 2-jet sum

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **sharp-order** intrinsic `H^m ↪ C²` Sobolev
embedding for smooth compactly-supported `(0,2)`-tensors, stated on the iterated covariant-gradient
2-jet sum `iteratedCovGradJetSum g₀ S x = ∑_{j ≤ 2} ‖(∇^j S)(x)‖_{g₀}`
(`RealizedJet2CovGradBound.lean`):

  `iteratedCovGradJetSum g₀ S x ≤ C · ‖S.toHs m‖`   whenever `2 * m > dim M + 4`.

The on-disk embedding `iteratedCovGradJetSum_le_toHs` is the **even-order** variant: its Sobolev
order is forced to the doubled form `2k` with the (non-sharp) threshold `2k > dim M + 4` on the
order itself, so it cannot serve a supercritical order-`a` budget with `2a > dim M + 4` (there `a`
itself, which may be odd and well below `dim M + 4`, is the available Sobolev order).  The
sharp-order refinement proved here is the classical embedding at its true threshold
`m > dim M / 2 + 2` (`⟺ 2m > dim M + 4`), at an arbitrary (in particular odd) order `m`.

On top of the sharp-order embedding the file proves outright:

* `realizeSymm_iteratedCovGradJetSum_le` — the symmetric realization `realizeSymmCcTensor` does not
  increase the covariant 2-jet sum (constant `1`; the slot swap is a parallel fibre isometry,
  `flipCcTensor_iteratedCovGrad_norm_eq`);
* `exists_realizedJetSum_le_toHs_sharpOrder` — the sharp-order `C²` control of the **realized**
  perturbation `realizeSymmCcTensor g₀ S` by the order-`m` Sobolev norm of the *unrealized* `S`;
* `riemannianFiberNormSq_le_sq_iteratedCovGradJetSum` — the order-`0` extraction: the intrinsic
  squared fibre norm of the tensor value is at most the squared 2-jet sum, so the embedding yields
  pointwise `C⁰` sup control `rfns(S)(x) ≤ (C · ‖S.toHs m‖)²` of the form the integrated
  Gagliardo–Nirenberg two-arm product engine consumes as its `Λ²` sup hypotheses.

The sharp-order embedding `exists_iteratedCovGradJetSum_le_toHs_sharpOrder` is proved here outright
from the order-sharp tensor `C⁰` embedding `tensorC0_embedding_sharpOrder` (the partition-of-unity
manifold assembly run at the genuine order `N`, threshold `dim M < 2 N`, via the order-agnostic
local Euclidean `L²` pointwise embedding `smooth_localBall_L2_pointwise_embedding`) composed with
the per-degree covariant order-dropping bound `iteratedCovGrad_toHs_norm_le`: for each covariant
degree `j ≤ 2` the higher-valence `∇^j S` is `C⁰`-controlled at its natural order `m - j` and the
order-drop returns the budget to `‖S.toHs m‖` (since `(m - j) + j = m`). -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section SharpOrderC0

open scoped ENNReal NNReal
open MeasureTheory Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Per-component pointwise bound (ball-uniform), sharp order.**  The order-sharp
analogue of `rawPullCenter_le_hsNorm`: it runs the Euclidean local-ball `L²` pointwise
embedding at the *true* Sobolev order `N` (threshold `dim M < 2 N`), matched against the
`H^N` Hilbert–Schmidt blocks, so the bound is by `‖T.toHs N‖` at an arbitrary (in
particular odd) order `N`. -/
private theorem rawPullCenter_le_toHs_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (N : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * N)
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {y₀ : EuclN} {R c : ℝ} (hR : 0 < R) (hc_pos : 0 < c)
    (hball : Metric.closedBall y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ (T' : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball y₀ (R / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cα * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ := by
  classical
  obtain ⟨Cloc, hCloc_nn, hCloc⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.smooth_localBall_L2_pointwise_embedding
      (d := Module.finrank ℝ E) (K := N) hk (x₀ := y₀) (R := R) hR
  set A : ℝ := Real.sqrt (((Module.finrank ℝ E) ^ (2 * N) : ℕ) * c⁻¹) with hA_def
  have hA_nn : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨Cloc * ((2 * N + 1 : ℕ) * A), by positivity, ?_⟩
  intro T' y₁ hy₁
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨ftil, hftil_smooth, hftil_eq⟩ :=
    exists_global_smooth_eqOn_ball_of_rawPull (I := I) (M := M) g r s T' α IJ.1 IJ.2 hball
  have hy₁_cb : y₁ ∈ Metric.closedBall y₀ R :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall hy₁
  have h_loc := hCloc (f := ftil) hftil_smooth y₁ hy₁
  have hftil_y0 : ftil y₁ =
      tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁)) := by
    have := hftil_eq hy₁_cb
    simpa [Function.comp_apply] using this
  have hball_open : Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (Metric.ball_subset_closedBall).trans hball
  have h_eqOn_ball : Set.EqOn ftil
      (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) (Metric.ball y₀ R) :=
    hftil_eq.mono Metric.ball_subset_closedBall
  have h_eLp_eq : ∀ j,
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) =
        eLpNorm (fun z => ‖iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    intro j
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall (fun z hz => ?_))
    have hball_nhd : Metric.ball y₀ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have h_ev : ftil =ᶠ[nhds z]
        (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) :=
      Filter.eventuallyEq_of_mem hball_nhd h_eqOn_ball
    have h_iter_eq := (h_ev.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [h_iter_eq]
  have h_per_order : ∀ j ∈ Finset.range (2 * N + 1),
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal ≤ A * hsn := by
    intro j hj
    rw [h_eLp_eq j]
    set X : ℝ≥0∞ := eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z‖) 2
      ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) with hX_def
    have hX_ne_top : X ≠ ⊤ := by
      rw [hX_def, ← h_eLp_eq j]
      exact smooth_eLpNorm_iteratedFDeriv_ball_ne_top (j := j) hftil_smooth
    have h_key := eLpNorm_sq_iteratedFDeriv_le_hsBlock (I := I) (M := M)
      g r s T' α IJ j hc_pos hball_open hρ_lb
    rw [← hX_def] at h_key
    have h_blk_le := hsBlock_le_hsNorm_sq (I := I) (M := M) g N T' α IJ j hj
    have hcard_nn : (0 : ℝ) ≤ ((Module.finrank ℝ E) ^ (2 * N) : ℕ) := by positivity
    have h_X_sq_le :
        X ^ 2 ≤ ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (tensorPouSobolevHsNorm (I := I) (M := M) g N T') ^ 2 :=
      h_key.trans (mul_le_mul_of_nonneg_left h_blk_le (zero_le _))
    have h_hsn_ne_top : (tensorPouSobolevHsNorm (I := I) (M := M) g N T') ≠ ⊤ :=
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g N T').ne
    have h_rhs_ne_top :
        ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (tensorPouSobolevHsNorm (I := I) (M := M) g N T') ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top h_hsn_ne_top)
    have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_X_sq_le
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by positivity), ENNReal.toReal_pow] at h_toReal
    have h_hsn_eq : (tensorPouSobolevHsNorm (I := I) (M := M) g N T').toReal = hsn := by
      rw [hhsn_def, tensorPouSobolevHilbert_norm_eq]
    rw [h_hsn_eq] at h_toReal
    have hX_toReal_nn : 0 ≤ X.toReal := ENNReal.toReal_nonneg
    have h_card_mono : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ ≤ A ^ 2 := by
      rw [hA_def, Real.sq_sqrt (by positivity)]
      have hjle : j ≤ 2 * N := by rw [Finset.mem_range] at hj; omega
      have : ((Module.finrank ℝ E) ^ j : ℕ) ≤ ((Module.finrank ℝ E) ^ (2 * N) : ℕ) :=
        Nat.pow_le_pow_right (NeZero.pos _) hjle
      have hcast : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) ≤
          (((Module.finrank ℝ E) ^ (2 * N) : ℕ) : ℝ) := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcast (by positivity)
    have h_Xsq_le_Asq : X.toReal ^ 2 ≤ (A * hsn) ^ 2 := by
      refine h_toReal.trans ?_
      have hhsn_sq_nn : 0 ≤ hsn ^ 2 := by positivity
      calc (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ * hsn ^ 2
          ≤ A ^ 2 * hsn ^ 2 := mul_le_mul_of_nonneg_right h_card_mono hhsn_sq_nn
        _ = (A * hsn) ^ 2 := by ring
    have hAhsn_nn : 0 ≤ A * hsn := mul_nonneg hA_nn hhsn_nn
    calc X.toReal = Real.sqrt (X.toReal ^ 2) := (Real.sqrt_sq hX_toReal_nn).symm
      _ ≤ Real.sqrt ((A * hsn) ^ 2) := Real.sqrt_le_sqrt h_Xsq_le_Asq
      _ = A * hsn := Real.sqrt_sq hAhsn_nn
  rw [← hftil_y0, ← Real.norm_eq_abs]
  refine h_loc.trans ?_
  have h_sum_le :
      (∑ j ∈ Finset.range (2 * N + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal)
        ≤ ((2 * N + 1 : ℕ) : ℝ) * (A * hsn) := by
    have h_each := Finset.sum_le_sum h_per_order
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_each
    exact h_each
  calc Cloc * (∑ j ∈ Finset.range (2 * N + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal)
      ≤ Cloc * (((2 * N + 1 : ℕ) : ℝ) * (A * hsn)) :=
        mul_le_mul_of_nonneg_left h_sum_le hCloc_nn
    _ = Cloc * (((2 * N + 1 : ℕ) : ℝ) * A) * hsn := by ring

/-- **Uniform per-component bound on a compact chart-image set, sharp order.**  The
order-sharp analogue of `uniformRawPull_le_hsNorm`, built from `rawPullCenter_le_toHs_sharp`
by a Lebesgue-number subcover. -/
private theorem uniformRawPull_le_toHs_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (N : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * N)
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {Kc O : Set EuclN} {c : ℝ} (hc_pos : 0 < c)
    (hKc_compact : IsCompact Kc) (hO_open : IsOpen O)
    (hKcO : Kc ⊆ O) (hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ O,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T' : SmoothCcTensor g r s), ∀ y ∈ Kc,
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
        ≤ D * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ := by
  classical
  rcases Set.eq_empty_or_nonempty Kc with hKc_empty | hKc_ne
  · exact ⟨0, le_refl 0, fun T' y hy => by rw [hKc_empty] at hy; exact absurd hy (Set.notMem_empty y)⟩
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    lebesgue_number_lemma_of_metric (s := Kc) (c := fun _ : Unit => O)
      hKc_compact (fun _ => hO_open) (by intro x hx; exact Set.mem_iUnion.mpr ⟨(), hKcO hx⟩)
  have hδ_sub : ∀ y ∈ Kc, Metric.ball y δ ⊆ O := by
    intro y hy
    obtain ⟨_, hsub⟩ := hδ_ball y hy
    exact hsub
  have hδ2_pos : 0 < δ / 2 := by linarith
  have h_center : ∀ y : Kc, ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ (T' : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball (y : EuclN) ((δ / 2) / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cy * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ := by
    intro y
    have hhalf_lt : δ / 2 < δ := half_lt_self hδ_pos
    have hhalf_le : δ / 2 ≤ δ := le_of_lt hhalf_lt
    have hcb_sub : Metric.closedBall (y : EuclN) (δ / 2) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
      refine (Metric.closedBall_subset_ball hhalf_lt).trans ?_
      exact (hδ_sub y y.2).trans hO_sub
    have hρ_ball : ∀ z ∈ Metric.ball (y : EuclN) (δ / 2),
        c ≤ (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      have hz' : z ∈ Metric.ball (y : EuclN) δ :=
        Metric.ball_subset_ball hhalf_le hz
      exact hρ_lb z (hδ_sub y y.2 hz')
    obtain ⟨Cy, hCy_nn, hCy⟩ :=
      rawPullCenter_le_toHs_sharp (I := I) (M := M) g r s N hk
        α IJ hδ2_pos hc_pos hcb_sub hρ_ball
    exact ⟨Cy, hCy_nn, hCy⟩
  choose Cfun hCfun_nn hCfun using h_center
  obtain ⟨tcov, htcov⟩ :=
    hKc_compact.elim_finite_subcover
      (U := fun y : Kc => Metric.ball (y : EuclN) ((δ / 2) / 4))
      (fun y => Metric.isOpen_ball)
      (by
        intro z hz
        refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]; positivity)
  set Dmax : ℝ := (tcov.image Cfun).sup' (by
    rcases hKc_ne with ⟨z, hz⟩
    obtain ⟨y, hy_t, _⟩ := Set.mem_iUnion₂.mp (htcov hz)
    exact Finset.image_nonempty.mpr ⟨y, hy_t⟩) id ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  refine ⟨Dmax, hDmax_nn, ?_⟩
  intro T' y hy
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨yi, hyi_t, hy_in⟩ := Set.mem_iUnion₂.mp (htcov hy)
  have h_bound := hCfun yi T' y hy_in
  have hCyi_le : Cfun yi ≤ Dmax := by
    rw [hDmax_def]
    refine le_sup_of_le_left ?_
    exact Finset.le_sup' id (Finset.mem_image_of_mem Cfun hyi_t)
  calc |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
      ≤ Cfun yi * hsn := h_bound
    _ ≤ Dmax * hsn := mul_le_mul_of_nonneg_right hCyi_le hhsn_nn

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-chart fibre-norm bound, sharp order.**  The order-sharp analogue of
`chartFiberNorm_le_hsNorm_on_superlevel`. -/
private theorem chartFiberNorm_le_toHs_sharp_on_superlevel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (N : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * N)
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ D *
          ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  set Kset : Set M := {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} with hKset_def
  have hρ_cont0 : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    (chartAtlasPOU I M α).contMDiff.continuous
  have hK_compact : IsCompact Kset := by
    have hclosed : IsClosed {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} :=
      isClosed_le continuous_const hρ_cont0
    rw [hKset_def]; exact hclosed.isCompact
  have hK_sub : Kset ⊆ (chartAt H α).source := by
    rw [hKset_def]
    intro x hx
    have hx_pos : (0 : ℝ) < (chartAtlasPOU I M α : M → ℝ) x := lt_of_lt_of_le hc_pos hx
    have hx_supp : x ∈ Function.support (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
      ne_of_gt hx_pos
    have hx_tsupp : x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
      subset_tsupport _ hx_supp
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx_tsupp
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    tensorFiberNorm_sq_le_chartAlphaComponents_on_compact (I := I) (M := M) g r s α
      hK_compact hK_sub
  set Kc : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' Kset) with hKc_def
  have hKc_compact : IsCompact Kc := by
    have h1 : IsCompact ((extChartAt I α) '' Kset) :=
      hK_compact.image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx; rw [extChartAt_source]; exact hK_sub hx))
    exact h1.image (toEuclidean (E := E)).continuous
  set O : Set EuclN :=
    chartTargetEuclid (I := I) (M := M) α ∩
      (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ⁻¹' (Set.Ioi (c / 2))
    with hO_def
  have hO_open : IsOpen O := by
    rw [hO_def]
    have hρ_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x := hρ_cont0
    have hcontOn : ContinuousOn
        (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      hρ_cont.comp_continuousOn'
        (DifferentialGeometry.Analysis.Sobolev.Chart.continuousOn_symm_toEuclideanSymm
          (I := I) (M := M) α)
    exact hcontOn.isOpen_inter_preimage
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
      isOpen_Ioi
  have hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α := by
    rw [hO_def]; exact Set.inter_subset_left
  have hx_ext_src : ∀ x ∈ Kset, x ∈ (extChartAt I α).source := by
    intro x hx; rw [extChartAt_source]; exact hK_sub hx
  have hpull_eq : ∀ x ∈ Kset,
      (extChartAt I α).symm ((toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) x))) = x := by
    intro x hx
    rw [(toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I α).left_inv (hx_ext_src x hx)
  have hKcO : Kc ⊆ O := by
    intro y hy
    rw [hKc_def] at hy
    obtain ⟨z, ⟨x, hx_K, hxz⟩, hzy⟩ := hy
    have hy_eq : y = (toEuclidean (E := E)) ((extChartAt I α) x) := by rw [hxz]; exact hzy.symm
    have hpull : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = x := by
      rw [hy_eq]; exact hpull_eq x hx_K
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_eq]
      exact ⟨(extChartAt I α) x, (extChartAt I α).map_source (hx_ext_src x hx_K), rfl⟩
    refine ⟨hy_target, ?_⟩
    have hgoal : c / 2 < (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      rw [hpull]
      have hx_ge : c ≤ (chartAtlasPOU I M α : M → ℝ) x := hx_K
      linarith [hc_pos, hx_ge]
    exact hgoal
  have hρ_on_O : ∀ y ∈ O,
      c / 2 ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    intro y hy
    rw [hO_def] at hy
    exact le_of_lt hy.2
  have hc2_pos : 0 < c / 2 := by linarith
  have h_comp : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      ∃ Dij : ℝ, 0 ≤ Dij ∧ ∀ (T' : SmoothCcTensor g r s), ∀ y ∈ Kc,
        |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
          ≤ Dij * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T'‖ := by
    intro IJ
    exact uniformRawPull_le_toHs_sharp (I := I) (M := M) g r s N hk α IJ hc2_pos
      hKc_compact hO_open hKcO hO_sub hρ_on_O
  choose Dfun hDfun_nn hDfun using h_comp
  set Dmax : ℝ := (Finset.univ.sup' (Finset.univ_nonempty) Dfun) ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  set npairs : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hnp_def
  have hnp_nn : 0 ≤ npairs := Nat.cast_nonneg _
  refine ⟨Real.sqrt (C₁ * npairs) * Dmax, by positivity, ?_⟩
  intro T x hx
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  have hx_K : x ∈ Kset := hx
  set yx : EuclN := (toEuclidean (E := E)) ((extChartAt I α) x) with hyx_def
  have hyx_Kc : yx ∈ Kc := by
    rw [hKc_def, hyx_def]
    exact ⟨(extChartAt I α) x, ⟨x, hx_K, rfl⟩, rfl⟩
  have hpull_x : (extChartAt I α).symm ((toEuclidean (E := E)).symm yx) = x := by
    rw [hyx_def]; exact hpull_eq x hx_K
  have h_core := hC₁ T x hx_K
  have h_each : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2 ≤
        (Dmax * hsn) ^ 2 := by
    intro IJ
    have h := hDfun IJ T yx hyx_Kc
    rw [hpull_x] at h
    have hDle : Dfun IJ ≤ Dmax := by
      rw [hDmax_def]
      exact le_sup_of_le_left (Finset.le_sup' Dfun (Finset.mem_univ IJ))
    have h' : |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x|
        ≤ Dmax * hsn :=
      h.trans (mul_le_mul_of_nonneg_right hDle hhsn_nn)
    have habs_nn : 0 ≤ |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| :=
      abs_nonneg _
    have hDhsn_nn : 0 ≤ Dmax * hsn := mul_nonneg hDmax_nn hhsn_nn
    calc (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2
        = |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| ^ 2 := (sq_abs _).symm
      _ ≤ (Dmax * hsn) ^ 2 := by
          exact pow_le_pow_left₀ habs_nn h' 2
  have h_sum_sq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ npairs * (Dmax * hsn) ^ 2 := by
    rw [hnp_def]
    rw [← Fintype.sum_prod_type']
    refine (Finset.sum_le_sum (fun IJ _ => h_each IJ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : ‖T.toSection x‖ ^ 2 ≤ (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
    refine h_core.trans ?_
    calc C₁ * (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ C₁ * (npairs * (Dmax * hsn) ^ 2) :=
          mul_le_mul_of_nonneg_left h_sum_sq (le_of_lt hC₁_pos)
      _ = (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
          have hsq : Real.sqrt (C₁ * npairs) ^ 2 = C₁ * npairs :=
            Real.sq_sqrt (by positivity)
          nlinarith [hsq]
  have hsec_nn : 0 ≤ ‖T.toSection x‖ := norm_nonneg _
  have hconst_nn : 0 ≤ Real.sqrt (C₁ * npairs) * Dmax := by positivity
  have h_rhs_sq : (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 =
      (Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2 := by ring
  rw [h_rhs_sq] at h_sq
  calc ‖T.toSection x‖ = Real.sqrt (‖T.toSection x‖ ^ 2) := (Real.sqrt_sq hsec_nn).symm
    _ ≤ Real.sqrt ((Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt (C₁ * npairs) * Dmax * hsn :=
        Real.sqrt_sq (by positivity)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Tensor Sobolev embedding `H^N ↪ C⁰` (Riemannian fibre norm), at the sharp order.**

For a closed Riemannian manifold and `dim M < 2 N` (the true `C⁰` Sobolev threshold,
at an arbitrary — in particular odd — Sobolev order `N`), the Riemannian bundle-fibre
norm of every smooth compactly-supported `(r, s)`-tensor section at every point is
controlled by a single positive constant times its intrinsic `H^N`-norm.

This is the order-sharp refinement of `tensorPouSobolevHilbert_embedding_Ck_gNorm` (whose
Sobolev order is forced to the doubled `2k`): the partition-of-unity assembly is reproduced
verbatim, but the local Euclidean pointwise embedding is run at the genuine order `N`
(`rawPullCenter_le_toHs_sharp`), so no parity constraint on `N` survives. -/
theorem tensorC0_embedding_sharpOrder
    (g : SmoothRiemannianMetric I M) (r s N : ℕ)
    (h_super : Module.finrank ℝ E < 2 * N) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  have hk : (Module.finrank ℝ E : ℝ) < 2 * N := by exact_mod_cast h_super
  rcases isEmpty_or_nonempty M with hMempty | hMne
  · exact ⟨1, one_pos, fun _T x => (hMempty.false x).elim⟩
  obtain ⟨x₀⟩ := hMne
  set Sf : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hS_ne : Sf.Nonempty := by
    have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x₀
    rw [← hS_def] at hsum
    rcases Finset.eq_empty_or_nonempty Sf with hSe | hSne
    · exfalso; rw [hSe] at hsum; simp at hsum
    · exact hSne
  set Ncov : ℕ := Sf.card with hN_def
  have hN_pos : 0 < Ncov := Finset.card_pos.mpr hS_ne
  have hN_pos_real : (0 : ℝ) < Ncov := by exact_mod_cast hN_pos
  have hcN_pos : (0 : ℝ) < 1 / Ncov := by positivity
  have h_perchart : ∀ α : M, ∃ Dα : ℝ, 0 ≤ Dα ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | (1 / Ncov : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ Dα *
          ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) N T‖ := fun α =>
    chartFiberNorm_le_toHs_sharp_on_superlevel (I := I) (M := M) g r s N hk α hcN_pos
  choose Dfun hDfun_nn hDfun using h_perchart
  set C : ℝ := Sf.sup' hS_ne Dfun + 1 with hC_def
  have hSsup_nn : 0 ≤ Sf.sup' hS_ne Dfun := by
    obtain ⟨β, hβ⟩ := hS_ne
    exact le_trans (hDfun_nn β) (Finset.le_sup' Dfun hβ)
  have hC_pos : 0 < C := by rw [hC_def]; linarith
  refine ⟨C, hC_pos, fun T x => ?_⟩
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  rw [← hS_def] at hsum
  have h_exists_α : ∃ α ∈ Sf, (1 / Ncov : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x := by
    by_contra h_all
    push Not at h_all
    have h_sum_lt : (∑ α ∈ Sf, (chartAtlasPOU I M α : M → ℝ) x) < ∑ _α ∈ Sf, (1 / Ncov : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hS_ne (fun α hα => h_all α hα)
    rw [Finset.sum_const, hsum, nsmul_eq_mul, ← hN_def, mul_one_div,
      div_self hN_pos_real.ne'] at h_sum_lt
    exact lt_irrefl 1 h_sum_lt
  obtain ⟨α, hα_S, hα_ge⟩ := h_exists_α
  have h_bound := hDfun α T x hα_ge
  refine h_bound.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [hC_def]
  have hDα_le : Dfun α ≤ Sf.sup' hS_ne Dfun := Finset.le_sup' Dfun hα_S
  linarith

end SharpOrderC0

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp-order intrinsic `H^m ↪ C²` tensor Sobolev embedding.**  For
`2 * m > dim M + 4` (the sharp `C²` threshold `m > dim M / 2 + 2`, at an arbitrary — in particular
odd — Sobolev order `m`), there is a constant `C > 0` such that for every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ S x ≤ C · ‖S.toHs m‖`.

This is the order-sharp refinement of the proven even-order embedding
`iteratedCovGradJetSum_le_toHs` (whose Sobolev order is forced to the doubled form `2k`): the
classical Sobolev embedding `H^m ↪ C²` on a closed `n`-manifold holds exactly when
`m > n / 2 + 2`, i.e. `2m > n + 4`, with no parity constraint on `m`.

**Proof.**  For each covariant degree `j ∈ {0, 1, 2}` the higher-valence tensor `∇^j S` (a
`(0, 2 + j)`-tensor) is controlled in `C⁰` at its natural order `m - j` by the order-sharp tensor
embedding `tensorC0_embedding_sharpOrder` — whose threshold `dim M < 2 (m - j)` follows from
`2 m > dim M + 4 ≥ dim M + 2 j` (`j ≤ 2`) — and the order-dropping bound
`iteratedCovGrad_toHs_norm_le` returns `‖(∇^j S).toHs (m - j)‖ ≤ C · ‖S.toHs ((m - j) + j)‖`, where
`(m - j) + j = m` exactly (`j ≤ 2 ≤ m`), so no order-monotonicity slack is needed.  Summing the
three per-degree bounds with the finite maximum of the constants gives `C > 0`.

**Non-vacuity.**  `C > 0` is strict, the left side carries the full covariant 2-jet of `S`
(orders `0, 1, 2`), and the right side the genuine order-`m` intrinsic Sobolev norm; a degenerate
`C` is rejected by any `S` with nonvanishing 2-jet. -/
theorem exists_iteratedCovGradJetSum_le_toHs_sharpOrder
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ)
    (h_super : 2 * m > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
        iteratedCovGradJetSum (I := I) g₀ S x ≤
          C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) m S‖ := by
  classical
  have hmge : 2 ≤ m := by omega
  have h_perdeg : ∀ j : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧ (j ≤ 2 →
      ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖) ≤
          Cj * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) m S‖) := by
    intro j
    by_cases hj : j ≤ 2
    · have h_thr : Module.finrank ℝ E < 2 * (m - j) := by omega
      obtain ⟨A, hA_pos, hA⟩ :=
        tensorC0_embedding_sharpOrder (I := I) (M := M) g₀ 0 (2 + j) (m - j) h_thr
      obtain ⟨B, hB_nn, hB⟩ :=
        DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_toHs_norm_le
          (I := I) (M := M) g₀ 0 2 j (m - j)
      refine ⟨A * B, by positivity, fun _ S x => ?_⟩
      have hmj : (m - j) + j = m := by omega
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      have hstepA := hA (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S) x
      have hstepB := hB S
      calc ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖
          ≤ A * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + j) (m - j)
              (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S)‖ := hstepA
        _ ≤ A * (B * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) ((m - j) + j) S‖) :=
            mul_le_mul_of_nonneg_left hstepB hA_pos.le
        _ = A * B * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) m S‖ := by
            rw [hmj]; ring
    · exact ⟨0, le_refl 0, fun h => absurd h hj⟩
  choose Cfun hCfun_nn hCfun using h_perdeg
  set Csum : ℝ := ∑ j ∈ Finset.range 3, Cfun j with hCsum_def
  have hCsum_nn : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hCfun_nn j)
  refine ⟨Csum + 1, by linarith, fun S x => ?_⟩
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) m S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  rw [iteratedCovGradJetSum]
  calc (∑ j ∈ Finset.range 3,
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖))
      ≤ ∑ j ∈ Finset.range 3, Cfun j * N := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
        exact hCfun j hj2 S x
    _ = Csum * N := by rw [hCsum_def, Finset.sum_mul]
    _ ≤ (Csum + 1) * N := by nlinarith [hN_nn, hCsum_nn]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The symmetric realization does not increase the covariant 2-jet sum.**  For every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ iteratedCovGradJetSum g₀ S x`.

Termwise: `realizeSymm S = ½ • S + ½ • flip S` (`realizeSymmCcTensor_eq`), the iterated covariant
gradient is `ℝ`-linear (`iteratedCovGrad_add`, `iteratedCovGrad_smul`), and the slot swap is a
parallel fibre isometry of every iterated covariant gradient
(`flipCcTensor_iteratedCovGrad_norm_eq`), so
`‖∇^j (realizeSymm S)(x)‖ ≤ ½‖∇^j S(x)‖ + ½‖∇^j (flip S)(x)‖ = ‖∇^j S(x)‖`.  Proved outright; no
posit. -/
theorem realizeSymm_iteratedCovGradJetSum_le
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x ≤
      iteratedCovGradJetSum (I := I) g₀ S x := by
  classical
  rw [iteratedCovGradJetSum, iteratedCovGradJetSum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
  have hdecomp :
      iteratedCovGrad (I := I) (M := M) g₀ 0 2 j (realizeSymmCcTensor (I := I) g₀ S) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
            (flipCcTensor (I := I) g₀ S) := by
    rw [realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      MetricRealization.iteratedCovGrad_smul, MetricRealization.iteratedCovGrad_smul]
  rw [hdecomp]
  rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
          (flipCcTensor (I := I) g₀ S)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
          (flipCcTensor (I := I) g₀ S)).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_smul]; rfl]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hflip := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ S j x
  linarith [hflip]

/-- **The sharp-order `C²` control of the realized perturbation by the unrealized Sobolev norm.**
For `2 * a > dim M + 4` there is a constant `C > 0` such that for every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ C · ‖S.toHs a‖`.

Composition of the realization monotonicity `realizeSymm_iteratedCovGradJetSum_le` (constant `1`)
with the sharp-order embedding `exists_iteratedCovGradJetSum_le_toHs_sharpOrder`. -/
theorem exists_realizedJetSum_le_toHs_sharpOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
        iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x ≤
          C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a S‖ := by
  obtain ⟨C, hC_pos, hC⟩ := exists_iteratedCovGradJetSum_le_toHs_sharpOrder (I := I) g₀ a ha
  exact ⟨C, hC_pos, fun S x =>
    le_trans (realizeSymm_iteratedCovGradJetSum_le (I := I) g₀ S x) (hC S x)⟩

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`0` extraction from the covariant 2-jet sum.**  The intrinsic squared fibre norm
of the tensor value is at most the squared 2-jet sum:

  `rfns(S)(x) ≤ (iteratedCovGradJetSum g₀ S x)²`.

The `j = 0` summand of the jet sum is the installed-bundle fibre norm `‖S(x)‖ = √(rfns(S)(x))`,
the remaining summands are nonnegative, and squaring is monotone on nonnegatives.  This converts
the (sharp-order) `C²` embedding into the pointwise `Λ²`-sup hypotheses
`rfns(S)(x) ≤ (C · ‖S.toHs m‖)²` of the integrated Gagliardo–Nirenberg two-arm engine.  Proved
outright; no posit. -/
theorem riemannianFiberNormSq_le_sq_iteratedCovGradJetSum
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x) ≤
      iteratedCovGradJetSum (I := I) g₀ S x ^ 2 := by
  classical
  have hterm_nn : ∀ j : ℕ, 0 ≤
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖) := by
    intro j
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have h0 :
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 0 S).toSection x‖) =
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) := by
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (S.toSection x)]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (S.toSection x)
  have hle : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) ≤
      iteratedCovGradJetSum (I := I) g₀ S x := by
    rw [iteratedCovGradJetSum, ← h0]
    exact Finset.single_le_sum (f := fun j =>
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖))
      (fun j _ => hterm_nn j) (Finset.mem_range.mpr (by omega : (0 : ℕ) < 3))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)
      = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) ^ 2 :=
        (Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _)).symm
    _ ≤ iteratedCovGradJetSum (I := I) g₀ S x ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
