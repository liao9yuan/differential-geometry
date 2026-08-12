import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence









noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction NNReal Topology

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral



theorem fatou_sq_mass {ι : Type*} (S : ℕ → Finset ι)
    (hS : Tendsto S atTop atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, Tendsto (fun N => v N i) atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 :=
    fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finset_sum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤
          ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKN
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact hmono.trans (hbound N)
    exact le_of_tendsto hlim hev
  exact ⟨summable_of_sum_le hnn hpartial, Real.tsum_le_of_sum_le hnn hpartial⟩



private theorem euclidean_weighted_norm_sq {ι : Type*} (K : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ℝ → ι → ℝ) (t : ℝ) :
    ‖(WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * v t i) :
        EuclideanSpace ℝ K)‖ ^ 2 =
      ∑ i : K, w i * (v t i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  rw [mul_pow, Real.sq_sqrt (hw i)]



theorem integral_fatou_sq_mass {ι : Type*}
    (S : ℕ → Finset ι) (hS : Tendsto S atTop atTop)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ℝ → ι → ℝ) (vlim : ℝ → ι → ℝ)
    {T : ℝ}
    (hcont : ∀ N i, ContinuousOn (fun t => v N t i) (Icc (0 : ℝ) T))
    (hconv : ∀ i t, t ∈ Icc (0 : ℝ) T →
      Tendsto (fun N => v N t i) atTop (𝓝 (vlim t i)))
    (B : ℝ)
    (hbound : ∀ N, ∫ t, ∑ i ∈ S N, w i * (v N t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B) :
    Summable (fun i => w i * ∫ t, (vlim t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T))) ∧
      ∑' i, w i * ∫ t, (vlim t i) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
  have hB : 0 ≤ B := by
    refine (integral_nonneg fun t => ?_).trans (hbound 0)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι,
      ∑ i ∈ K, w i * ∫ t, (vlim t i) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
    intro K
    let fN : ℕ → ℝ → EuclideanSpace ℝ K := fun N t =>
      WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * v N t i)
    let f : ℝ → EuclideanSpace ℝ K := fun t =>
      WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * vlim t i)
    have hfNcont : ∀ N, ContinuousOn (fN N) (Icc (0 : ℝ) T) := by
      intro N
      apply (PiLp.continuous_toLp 2 _).comp_continuousOn
      rw [continuousOn_pi]
      exact fun i => continuousOn_const.mul (hcont N i)
    have hfNmeas : ∀ N,
        AEStronglyMeasurable (fN N) (volume.restrict (Icc (0 : ℝ) T)) := by
      intro N
      exact (hfNcont N).aestronglyMeasurable measurableSet_Icc
    have hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        Tendsto (fun N => fN N t) atTop (𝓝 (f t)) := by
      filter_upwards [ae_restrict_mem (μ := volume)
        (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) T))] with t ht
      apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
      rw [tendsto_pi_nhds]
      exact fun i => tendsto_const_nhds.mul (hconv i t ht)
    have hfmeas : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) T)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hfNmeas hlim
    have hfNmem : ∀ N, MemLp (fN N) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
      intro N
      rw [memLp_two_iff_integrable_sq_norm (hfNmeas N)]
      exact ((hfNcont N).norm.pow 2).integrableOn_Icc
    have hevent : ∀ᶠ N in atTop, K ⊆ S N := hS.eventually_ge_atTop K
    have heLp : ∀ᶠ N in atTop,
        eLpNorm (fN N) 2 (volume.restrict (Icc (0 : ℝ) T)) ≤
          ENNReal.ofReal (Real.sqrt B) := by
      filter_upwards [hevent] with N hKN
      have hpartialN : ∫ t, ‖fN N t‖ ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
        have hleft : ∫ t, ‖fN N t‖ ^ 2 ∂(volume.restrict (Icc (0 : ℝ) T)) =
            ∫ t, ∑ i ∈ K, w i * (v N t i) ^ 2
              ∂(volume.restrict (Icc (0 : ℝ) T)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            calc
              ‖fN N t‖ ^ 2 = ∑ i : K, w i * (v N t i) ^ 2 :=
                euclidean_weighted_norm_sq K w hw (v N) t
              _ = ∑ i ∈ K, w i * (v N t i) ^ 2 :=
                (Finset.sum_subtype K (fun _ => Iff.rfl)
                  (fun i => w i * (v N t i) ^ 2)).symm
        rw [hleft]
        refine (integral_mono_ae ?_ ?_ ?_).trans (hbound N)
        · exact (continuousOn_finset_sum K fun i _ =>
            (continuousOn_const.mul ((hcont N i).pow 2))).integrableOn_Icc
        · exact (continuousOn_finset_sum (S N) fun i _ =>
            (continuousOn_const.mul ((hcont N i).pow 2))).integrableOn_Icc
        · exact Filter.Eventually.of_forall fun t =>
            Finset.sum_le_sum_of_subset_of_nonneg hKN
              (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      rw [(hfNmem N).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      norm_num [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hpartialN
    have hflp : eLpNorm f 2 (volume.restrict (Icc (0 : ℝ) T)) ≤
        ENNReal.ofReal (Real.sqrt B) :=
      Lp.eLpNorm_le_of_ae_tendsto heLp hfNmeas hlim
    have hfmem : MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)) := by
      refine ⟨hfmeas, ?_⟩
      exact hflp.trans_lt (by simp)
    have hnormint : ∫ t, ‖f t‖ ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
      rw [(hfmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num))] at hflp
      norm_num [← Real.sqrt_eq_rpow] at hflp
      have hsqrt : Real.sqrt (∫ t, ‖f t‖ ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T))) ≤ Real.sqrt B := by
        exact hflp
      exact (Real.sqrt_le_sqrt_iff hB).mp hsqrt
    calc
      ∑ i ∈ K, w i * ∫ t, (vlim t i) ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) =
          ∑ i ∈ K, ∫ t, w i * (vlim t i) ^ 2
            ∂(volume.restrict (Icc (0 : ℝ) T)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_const_mul]
      _ = ∫ t, ∑ i ∈ K, w i * (vlim t i) ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        rw [integral_finset_sum K]
        intro i hi
        have hiLp : MemLp (fun t => f t ⟨i, hi⟩) 2
            (volume.restrict (Icc (0 : ℝ) T)) := by
          apply MemLp.of_le hfmem
          · exact (EuclideanSpace.proj ⟨i, hi⟩).continuous.comp_aestronglyMeasurable hfmem.1
          · exact Filter.Eventually.of_forall fun t => PiLp.norm_apply_le (f t) ⟨i, hi⟩
        refine hiLp.integrable_sq.congr (Filter.Eventually.of_forall fun t => ?_)
        dsimp [f]
        rw [mul_pow, Real.sq_sqrt (hw i)]
      _ = ∫ t, ‖f t‖ ^ 2 ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          calc
            ∑ i ∈ K, w i * (vlim t i) ^ 2 =
                ∑ i : K, w i * (vlim t i) ^ 2 :=
              Finset.sum_subtype K (fun _ => Iff.rfl)
                (fun i => w i * (vlim t i) ^ 2)
            _ = ‖f t‖ ^ 2 := (euclidean_weighted_norm_sq K w hw vlim t).symm
      _ ≤ B := hnormint
  have hnn : ∀ i, 0 ≤ w i * ∫ t, (vlim t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    intro i
    exact mul_nonneg (hw i) (integral_nonneg fun _ => sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hpartial, Real.tsum_le_of_sum_le hnn hpartial⟩



theorem right_lipschitz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {a b : ℝ} {K : ℝ≥0}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ (K : ℝ)) :
    LipschitzOnWith K f (Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
  rcases le_total x y with hxy | hyx
  · have hcont : ContinuousOn f (Icc x y) := by
      refine hf.mono (fun z hz => ?_)
      exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    have hderiv : ∀ z ∈ Ico x y, HasDerivWithinAt f (f' z) (Ici z) z := by
      intro z hz
      exact hf' z ⟨hx.1.trans hz.1, hz.2.trans_le hy.2⟩
    have hnorm : ∀ z ∈ Ico x y, ‖f' z‖ ≤ (K : ℝ) := by
      intro z hz
      exact hbound z ⟨hx.1.trans hz.1, hz.2.trans_le hy.2⟩
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      hcont hderiv hnorm y (right_mem_Icc.2 hxy)
    simpa only [dist_eq_norm, norm_sub_rev, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.2 hxy), neg_sub] using hseg
  · have hcont : ContinuousOn f (Icc y x) := by
      refine hf.mono (fun z hz => ?_)
      exact ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩
    have hderiv : ∀ z ∈ Ico y x, HasDerivWithinAt f (f' z) (Ici z) z := by
      intro z hz
      exact hf' z ⟨hy.1.trans hz.1, hz.2.trans_le hx.2⟩
    have hnorm : ∀ z ∈ Ico y x, ‖f' z‖ ≤ (K : ℝ) := by
      intro z hz
      exact hbound z ⟨hy.1.trans hz.1, hz.2.trans_le hx.2⟩
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      hcont hderiv hnorm x (right_mem_Icc.2 hyx)
    simpa only [dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 hyx)] using hseg



theorem galerkin_subseq {ι : Type*} [Countable ι] {τ : ℝ} (hτ : 0 ≤ τ)
    (u : ℕ → ℝ → ι → ℝ) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (L : ι → ℝ≥0)
    (hbd : ∀ N t, t ∈ Icc (0 : ℝ) τ → ∀ i, |u N t i| ≤ C i)
    (hlip : ∀ N i, LipschitzOnWith (L i) (fun t => u N t i) (Icc (0 : ℝ) τ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ ulim : ℝ → ι → ℝ,
        (∀ i, Continuous (fun t => ulim t i)) ∧
          ∀ i, TendstoUniformlyOn (fun n t => u (φ n) t i)
            (fun t => ulim t i) atTop (Icc (0 : ℝ) τ) := by
  classical
  let J : Set ℝ := Icc (0 : ℝ) τ
  letI : CompactSpace J := isCompact_iff_compactSpace.mp (by
    simpa only [J] using (isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)))
  let f : ι → ℕ → (J →ᵇ ℝ) := fun i N =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t : J => u N t i, by
        simpa only [J] using (hlip N i).to_restrict.continuous⟩
  have hvalues (i : ι) : ∀ (g : J →ᵇ ℝ) (t : J),
      g ∈ range (f i) → g t ∈ Icc (-C i) (C i) := by
    rintro g t ⟨N, rfl⟩
    have hu := hbd N (t : ℝ) (by simpa only [J] using t.2) i
    have hu' : |u N (t : ℝ) i| ≤ max (C i) 0 := hu.trans (le_max_left _ _)
    simpa only [f, BoundedContinuousFunction.mkOfCompact_apply,
      max_eq_left (hC i)] using abs_le.mp hu'
  have hequicont (i : ι) :
      Equicontinuous ((↑) : (range (f i)) → J → ℝ) := by
    refine Metric.equicontinuous_of_continuity_modulus
      (fun s => (L i : ℝ) * s) ?_ _ ?_
    · have ht : Tendsto (fun s : ℝ => (L i : ℝ) * s) (𝓝 0)
          (𝓝 ((L i : ℝ) * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa only [mul_zero] using ht
    · rintro x y ⟨g, hg⟩
      rcases hg with ⟨N, rfl⟩
      have hdist := (hlip N i).to_restrict.dist_le_mul x y
      simpa only [f, BoundedContinuousFunction.mkOfCompact_apply,
        Set.restrict_apply] using hdist
  let K : ι → Set (J →ᵇ ℝ) := fun i => closure (range (f i))
  have hK (i : ι) : IsCompact (K i) := by
    simpa only [K] using
      BoundedContinuousFunction.arzela_ascoli (Icc (-C i) (C i)) isCompact_Icc
        (range (f i)) (hvalues i) (hequicont i)
  let F : ℕ → (∀ i, J →ᵇ ℝ) := fun N i => f i N
  have hF (N : ℕ) : F N ∈ Set.pi univ K := by
    intro i _
    change f i N ∈ closure (range (f i))
    exact subset_closure (mem_range_self N)
  have hprod : IsCompact (Set.pi univ K) := isCompact_univ_pi hK
  obtain ⟨g, _, φ, hφ, hg⟩ := hprod.tendsto_subseq hF
  let ulim : ℝ → ι → ℝ := fun t i => IccExtend hτ (fun x : J => g i x) t
  refine ⟨φ, hφ, ulim, ?_, ?_⟩
  · intro i
    simpa only [ulim, J] using (g i).continuous.Icc_extend'
  · intro i
    have hcoord : Tendsto (fun n => f i (φ n)) atTop (𝓝 (g i)) := by
      rw [tendsto_pi_nhds] at hg
      simpa only [Function.comp_apply, F] using hg i
    have hunif : TendstoUniformly (fun (n : ℕ) (t : J) => u (φ n) t i)
        (fun t : J => g i t) atTop := by
      have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcoord
      simpa only [f, BoundedContinuousFunction.mkOfCompact_apply] using h
    rw [tendstoUniformlyOn_iff_restrict]
    convert hunif using 1
    funext t
    change ulim (t : ℝ) i = g i t
    exact IccExtend_val hτ (fun x : J => g i x) t

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
