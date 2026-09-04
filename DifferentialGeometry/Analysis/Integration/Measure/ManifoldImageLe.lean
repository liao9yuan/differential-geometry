import DifferentialGeometry.Analysis.Integration.Measure.JacobianImageLe
import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The Riemannian Gram-Jacobian density of a map from the model vector space
to a manifold. -/
def mapJacDensity (g : SmoothRiemannianMetric I M) (f : E → M) (x : E) : ℝ :=
  Real.sqrt (Matrix.of fun i j =>
    g.inner (f x)
      (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
      (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j))).det

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma mfderiv_basis
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i) =
      ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
            (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
        chartBasisVecFiber (I := I) y₀ k (f x) := by
  have hy_chart : f x ∈ (chartAt H y₀).source := by
    simpa only [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hy
  have hchart : MDifferentiableAt I (modelWithCornersSelf ℝ E) (extChartAt I y₀) (f x) :=
    mdifferentiableAt_extChartAt (I := I) (x := y₀) (y := f x) hy_chart
  have hchain :
      fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x =
        (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I y₀) (f x)).comp
          (mfderiv (modelWithCornersSelf ℝ E) I f x) := by
    have hchain' := mfderiv_comp (I := (modelWithCornersSelf ℝ E)) (I' := I) (I'' := (modelWithCornersSelf ℝ E))
      (g := extChartAt I y₀) (f := f) (x := x) hchart hf
    simpa only [Function.comp_def, mfderiv_eq_fderiv] using hchain'
  let T₀ : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) y₀
  apply (T₀.continuousLinearEquivAt ℝ (f x) hy).injective
  have hrepr :
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x) ((chartModelBasis E) i) =
        ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
          (chartModelBasis E) k := by
    simpa only [LinearMap.toMatrix_apply] using
      (((chartModelBasis E).sum_repr
        ((fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x)
          ((chartModelBasis E) i))).symm)
  calc
    T₀.continuousLinearEquivAt ℝ (f x) hy
        (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
        = (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x)
            ((chartModelBasis E) i) := by
          rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) T₀ hy]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (x₀ := y₀) (x := f x) hy_chart]
          rw [hchain]
          rfl
    _ = ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
          (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
            (chartModelBasis E) k := hrepr
    _ = T₀.continuousLinearEquivAt ℝ (f x) hy
          (∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
            chartBasisVecFiber (I := I) y₀ k (f x)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_smul]
          have hbasis :
              chartBasisVecFiber (I := I) y₀ k (f x) =
                (T₀.continuousLinearEquivAt ℝ (f x) hy).symm
                  ((chartModelBasis E) k) := by
            rfl
          rw [hbasis, ContinuousLinearEquiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma mapGram_det
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    (Matrix.of fun i j =>
        g.inner (f x)
          (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
          (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j))).det =
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det ^ 2 *
        (chartGramMatrix g y₀ (f x)).det := by
  let J : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap
  have hmul :
      (Matrix.of fun i j =>
          g.inner (f x)
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j))) =
        Jᵀ * chartGramMatrix g y₀ (f x) * J := by
    ext i j
    have hsum :
        g.inner (f x)
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j)) =
          ∑ k, ∑ l, J k i * J l j * chartGramMatrix g y₀ (f x) k l := by
      rw [mfderiv_basis (I := I) f hf y₀ hy i,
        mfderiv_basis (I := I) f hf y₀ hy j]
      have hL :
          g.inner (f x)
              (∑ k, J k i • chartBasisVecFiber (I := I) y₀ k (f x)) =
            ∑ k, J k i •
              g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [map_smul]
      rw [hL, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.smul_apply]
      have hR :
          g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x))
              (∑ l, J l j • chartBasisVecFiber (I := I) y₀ l (f x)) =
            ∑ l, J l j *
              g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x))
                (chartBasisVecFiber (I := I) y₀ l (f x)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [map_smul, smul_eq_mul]
      rw [hR, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [chartGramMatrix_apply]
      ring
    rw [Matrix.of_apply, hsum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hmul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hJ : J.det =
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det := by
    dsimp only [J]
    rw [LinearMap.det_toMatrix]
  rw [hJ]
  ring

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma mapJac_eq_chart
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    mapJacDensity (I := I) g f x =
      chartDensity g y₀ (f x) *
        |(fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det| := by
  rw [mapJacDensity, mapGram_det (I := I) g f hf y₀ hy]
  unfold chartDensity
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M]
  [SigmaCompactSpace M] in
private lemma mapChart_contDiffOn
    {f : E → M} {U s : Set E} (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (hsU : s ⊆ U) (y₀ : M) (hs_chart : ∀ x ∈ s, f x ∈ (chartAt H y₀).source) :
    ContDiffOn ℝ 1 (fun x : E => extChartAt I y₀ (f x)) s := by
  have hf' : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f s := hf.mono hsU
  have hchart : ContMDiffOn I (modelWithCornersSelf ℝ E) 1 (extChartAt I y₀) (chartAt H y₀).source :=
    contMDiffOn_extChartAt (I := I) (x := y₀) (n := 1)
  have hcomp : ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) 1
      ((extChartAt I y₀) ∘ f) s :=
    hchart.comp hf' (fun x hx => hs_chart x hx)
  exact contMDiffOn_iff_contDiffOn.mp
    (by simpa only [Function.comp_apply] using hcomp)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma mapJac_contOn_chart
    (g : SmoothRiemannianMetric I M) {f : E → M} {U s : Set E}
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U) (hsU : s ⊆ U)
    (hs_open : IsOpen s) (y₀ : M)
    (hs_chart : ∀ x ∈ s,
      f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    ContinuousOn (mapJacDensity (I := I) g f) s := by
  have hcoord : ContDiffOn ℝ 1 (fun x : E => extChartAt I y₀ (f x)) s :=
    mapChart_contDiffOn (I := I) hf hsU y₀ (fun x hx => by
      simpa only [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hs_chart x hx)
  have hderiv : ContinuousOn
      (fun x : E => fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x) s :=
    hcoord.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hdet : ContinuousOn
      (fun x : E => |(fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det|) s :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hderiv).abs
  have hf_cont : ContinuousOn f s := (hf.mono hsU).continuousOn
  have hdensity : ContinuousOn (fun x => chartDensity g y₀ (f x)) s :=
    (chartDensity_continuousOn (I := I) g y₀).comp hf_cont hs_chart
  refine (hdensity.mul hdet).congr (fun x hx => ?_)
  have hmdiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x :=
    (((hf.mono hsU) x hx).contMDiffAt (hs_open.mem_nhds hx)).mdifferentiableAt
      (by norm_num)
  exact mapJac_eq_chart (I := I) g f hmdiff y₀ (hs_chart x hx)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
/-- The Gram-Jacobian density is continuous on an open set where the map is `C¹`. -/
theorem mapJac_contOn
    (g : SmoothRiemannianMetric I M) {f : E → M} {U : Set E}
    (hU : IsOpen U) (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U) :
    ContinuousOn (mapJacDensity (I := I) g f) U := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_continuousAt]
  intro x
  let y₀ : M := f x
  let V : Set E := U ∩ f ⁻¹' (chartAt H y₀).source
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact hf.continuousOn.isOpen_inter_preimage hU (chartAt H y₀).open_source
  have hVU : V ⊆ U := by
    dsimp only [V]
    exact inter_subset_left
  have hVchart : ∀ z ∈ V,
      f z ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    intro z hz
    simpa only [V, trivializationAt_baseSet_eq_chartAt_source (I := I)] using hz.2
  have hxV : (x : E) ∈ V := by
    exact ⟨x.2, by simpa only [y₀] using mem_chart_source H (f x)⟩
  have hcontV : ContinuousOn (mapJacDensity (I := I) g f) V :=
    mapJac_contOn_chart (I := I) g hf hVU hVopen y₀ hVchart
  exact (hcontV.continuousAt (hVopen.mem_nhds hxV)).comp
    continuous_subtype_val.continuousAt

omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_term_map_le
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (himg : MeasurableSet (f '' K)) (a : M) :
    ((chartLocalMeasure (I := I) g a).withDensity
        (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))) (f '' K) ≤
      ∫⁻ x in K, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x) ∂(modelHaar (E := E)) := by
  classical
  let S : Set M := (chartAt H a).source
  let V : Set E := U ∩ f ⁻¹' S
  let Ka : Set E := K ∩ V
  have hVopen : IsOpen V := by
    dsimp only [V, S]
    exact hf.continuousOn.isOpen_inter_preimage hU (chartAt H a).open_source
  have hVU : V ⊆ U := by
    dsimp only [V]
    exact inter_subset_left
  have hVchart : ∀ x ∈ V, f x ∈ (chartAt H a).source := by
    intro x hx
    exact hx.2
  have hKa : MeasurableSet Ka := hK.inter hVopen.measurableSet
  let fa : E → E := V.piecewise (fun x => extChartAt I a (f x)) 0
  let fa' : E → (E →L[ℝ] E) :=
    fun x => fderiv ℝ (fun z => extChartAt I a (f z)) x
  let Wa : E → ℝ≥0∞ := (extChartAt I a).target.piecewise
    (fun q => ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q) *
      chartAtlasPOU I M a ((extChartAt I a).symm q))) 0
  have hfa : ∀ x ∈ V, fa x = extChartAt I a (f x) := by
    intro x hx
    dsimp only [fa]
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hWa : ∀ q ∈ (extChartAt I a).target,
      Wa q = ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q) *
        chartAtlasPOU I M a ((extChartAt I a).symm q)) := by
    intro q hq
    dsimp only [Wa]
    exact Set.piecewise_eq_of_mem _ _ _ hq
  have hcoord : ContDiffOn ℝ 1 (fun x : E => extChartAt I a (f x)) V :=
    mapChart_contDiffOn (I := I) hf hVU a hVchart
  have hfa_meas : Measurable fa := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn
      hVopen.measurableSet
    exact (continuousOn_extChartAt (I := I) a).comp
      ((hf.mono hVU).continuousOn) (fun x hx => by
        rw [extChartAt_source]
        exact hVchart x hx)
  have htarget_meas : MeasurableSet (extChartAt I a).target :=
    measurableSet_extChartAt_target (I := I) a
  have hsymm : ContinuousOn (extChartAt I a).symm (extChartAt I a).target :=
    continuousOn_extChartAt_symm (I := I) a
  have hsymm_maps : MapsTo (extChartAt I a).symm (extChartAt I a).target S := by
    intro q hq
    dsimp only [S]
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I a).map_target hq
  have hWa_meas : Measurable Wa := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn htarget_meas
    refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ ?_)
    · refine (chartDensity_continuousOn (I := I) g a).comp hsymm (fun q hq => ?_)
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) a]
      exact hsymm_maps hq
    · exact (chartAtlasPOU I M a).contMDiff.continuous.comp_continuousOn hsymm
  have hderiv : ∀ x ∈ Ka, HasFDerivWithinAt fa (fa' x) Ka x := by
    intro x hx
    have hxV : x ∈ V := hx.2
    have hcd : ContDiffAt ℝ 1 (fun z : E => extChartAt I a (f z)) x :=
      (hcoord x hxV).contDiffAt (hVopen.mem_nhds hxV)
    have hfd : HasFDerivAt (fun z : E => extChartAt I a (f z)) (fa' x) x :=
      (hcd.differentiableAt (by norm_num)).hasFDerivAt
    have heq : fa =ᶠ[nhds x] (fun z : E => extChartAt I a (f z)) :=
      eventuallyEq_of_mem (hVopen.mem_nhds hxV) (fun z hz => hfa z hz)
    exact (hfd.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have hpoU_meas : Measurable (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y)) :=
    ENNReal.measurable_ofReal.comp (chartAtlasPOU I M a).contMDiff.continuous.measurable
  have heq : ∀ q ∈ (extChartAt I a).target,
      ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q)) *
          (f '' K).indicator (fun y : M =>
            ENNReal.ofReal (chartAtlasPOU I M a y)) ((extChartAt I a).symm q) =
        (fa '' Ka).indicator Wa q := by
    intro q hq
    by_cases hqimg : q ∈ fa '' Ka
    · have hqmem := hqimg
      obtain ⟨x, hxKa, hxq⟩ := hqimg
      have hxV : x ∈ V := hxKa.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hsymmq : (extChartAt I a).symm q = f x := by
        rw [← hxq, hfax]
        exact (extChartAt I a).left_inv (by rw [extChartAt_source]; exact hfxS)
      have hfximg : f x ∈ f '' K := ⟨x, hxKa.1, rfl⟩
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hsymmq, Set.indicator_of_mem hfximg, Set.indicator_of_mem hqmem,
        hWa q hq, hsymmq]
      exact (ENNReal.ofReal_mul hcdnn).symm
    · rw [Set.indicator_of_notMem hqimg]
      by_contra hne
      refine hqimg ?_
      have hind : (f '' K).indicator (fun y : M =>
          ENNReal.ofReal (chartAtlasPOU I M a y)) ((extChartAt I a).symm q) ≠ 0 :=
        fun hz => hne (by rw [hz, mul_zero])
      have himgmem : (extChartAt I a).symm q ∈ f '' K := by
        by_contra hnot
        exact hind (Set.indicator_of_notMem hnot _)
      have hpou_ne : ENNReal.ofReal
          (chartAtlasPOU I M a ((extChartAt I a).symm q)) ≠ 0 := by
        rwa [Set.indicator_of_mem himgmem] at hind
      have hpou_pos : 0 < chartAtlasPOU I M a ((extChartAt I a).symm q) :=
        ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hpou_ne)
      have hsymmS : (extChartAt I a).symm q ∈ S :=
        (chartAtlasPOU_isSubordinate I M) a
          (subset_tsupport _ (Function.mem_support.mpr hpou_pos.ne'))
      obtain ⟨x, hxK, hfx⟩ := himgmem
      have hxV : x ∈ V := ⟨hKU hxK, by change f x ∈ S; rw [hfx]; exact hsymmS⟩
      refine ⟨x, ⟨hxK, hxV⟩, ?_⟩
      rw [hfa x hxV, hfx]
      exact (extChartAt I a).right_inv hq
  rw [withDensity_apply _ himg,
    chartLocalMeasure_setLintegral_indicator (I := I) g a himg hpoU_meas]
  calc
    ∫⁻ q in (extChartAt I a).target,
        ENNReal.ofReal (chartDensity g a ((extChartAt I a).symm q)) *
          (f '' K).indicator (fun y : M => ENNReal.ofReal (chartAtlasPOU I M a y))
            ((extChartAt I a).symm q) ∂(modelHaar (E := E))
        = ∫⁻ q in (extChartAt I a).target, (fa '' Ka).indicator Wa q
            ∂(modelHaar (E := E)) :=
          setLIntegral_congr_fun htarget_meas heq
    _ ≤ ∫⁻ q, (fa '' Ka).indicator Wa q ∂(modelHaar (E := E)) :=
      setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ q in fa '' Ka, Wa q ∂(modelHaar (E := E)) :=
      lintegral_indicator_le _ _
    _ ≤ ∫⁻ x in Ka, Wa (fa x) * ENNReal.ofReal |(fa' x).det|
        ∂(modelHaar (E := E)) :=
      image_lintegral_le (modelHaar (E := E)) hKa hfa_meas hderiv hWa_meas
    _ = ∫⁻ x in Ka, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x) ∂(modelHaar (E := E)) := by
      refine setLIntegral_congr_fun hKa (fun x hx => ?_)
      have hxV : x ∈ V := hx.2
      have hfxS : f x ∈ S := hxV.2
      have hfax : fa x = extChartAt I a (f x) := hfa x hxV
      have hmap : extChartAt I a (f x) ∈ (extChartAt I a).target :=
        (extChartAt I a).map_source (by rw [extChartAt_source]; exact hfxS)
      have hsymm : (extChartAt I a).symm (extChartAt I a (f x)) = f x :=
        (extChartAt I a).left_inv (by rw [extChartAt_source]; exact hfxS)
      have hWat : Wa (fa x) = ENNReal.ofReal
          (chartDensity g a (f x) * chartAtlasPOU I M a (f x)) := by
        rw [hfax, hWa _ hmap, hsymm]
      have hmdiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x :=
        (((hf.mono hVU) x hxV).contMDiffAt (hVopen.mem_nhds hxV)).mdifferentiableAt
          (by norm_num)
      have hbase : f x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I) a]
        exact hfxS
      have hjac := mapJac_eq_chart (I := I) g f hmdiff a hbase
      have hcdnn : 0 ≤ chartDensity g a (f x) := Real.sqrt_nonneg _
      rw [hWat, ← ENNReal.ofReal_mul (mul_nonneg hcdnn
        ((chartAtlasPOU I M).nonneg a (f x))),
        ← ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg a (f x))]
      dsimp only [fa']
      rw [hjac]
      ring_nf
    _ ≤ ∫⁻ x in K, ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x) ∂(modelHaar (E := E)) :=
      lintegral_mono_set inter_subset_left

omit [NeZero (Module.finrank ℝ E)] in
/-- A `C¹` map on an open neighborhood of a compact set bounds the
Riemannian volume of its image by its Gram-Jacobian integral. No injectivity is
required. -/
theorem riemVol_image_le
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' K) ≤
      ∫⁻ x in K, ENNReal.ofReal (mapJacDensity (I := I) g f x)
        ∂(modelHaar (E := E)) := by
  classical
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hfK : ContinuousOn f K := hf.continuousOn.mono hKU
  have himg : MeasurableSet (f '' K) :=
    (hK.image_of_continuousOn hfK).measurableSet
  have hJacK : ContinuousOn (mapJacDensity (I := I) g f) K :=
    (mapJac_contOn (I := I) g hU hf).mono hKU
  have hsm : ∀ a : M, AEMeasurable (fun x : E =>
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x))
      ((modelHaar (E := E)).restrict K) := by
    intro a
    have hpou : ContinuousOn (fun x : E => chartAtlasPOU I M a (f x)) K :=
      (chartAtlasPOU I M a).contMDiff.continuous.comp_continuousOn hfK
    have hreal : ContinuousOn (fun x : E =>
        chartAtlasPOU I M a (f x) * mapJacDensity (I := I) g f x) K :=
      hpou.mul hJacK
    have hae : AEMeasurable (fun x : E => ENNReal.ofReal
        (chartAtlasPOU I M a (f x) * mapJacDensity (I := I) g f x))
        ((modelHaar (E := E)).restrict K) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hreal.aemeasurable hKmeas))
    refine hae.congr (Filter.Eventually.of_forall (fun x => ?_))
    change ENNReal.ofReal
        (chartAtlasPOU I M a (f x) * mapJacDensity (I := I) g f x) =
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x)
    rw [ENNReal.ofReal_mul ((chartAtlasPOU I M).nonneg a (f x))]
  let T : Set M := {a : M | (Function.support (chartAtlasPOU I M a)).Nonempty}
  have hT_count : T.Countable := countable_nonempty_support_of_pou (I := I) (chartAtlasPOU I M)
  haveI : Countable T := hT_count.to_subtype
  have hsupp : Function.support (fun a : M => ∫⁻ x in K,
      ENNReal.ofReal (chartAtlasPOU I M a (f x)) *
        ENNReal.ofReal (mapJacDensity (I := I) g f x) ∂(modelHaar (E := E))) ⊆ T := by
    intro a ha
    by_contra haT
    refine ha ?_
    have hzero : Function.support (chartAtlasPOU I M a) = ∅ := by
      change ¬ (Function.support (chartAtlasPOU I M a)).Nonempty at haT
      exact Set.not_nonempty_iff_eq_empty.mp haT
    have hpou_zero : ∀ x : E, chartAtlasPOU I M a (f x) = 0 := by
      intro x
      by_contra hne
      have : f x ∈ Function.support (chartAtlasPOU I M a) := hne
      rw [hzero] at this
      exact this
    simp only [hpou_zero, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  have hsupp_pou : ∀ x : E, Function.support (fun a : M =>
      ENNReal.ofReal (chartAtlasPOU I M a (f x))) ⊆ T := by
    intro x a ha
    refine Set.nonempty_iff_ne_empty.mpr ?_
    intro hempty
    have hzero : chartAtlasPOU I M a (f x) = 0 := by
      by_contra hne
      have : f x ∈ Function.support (chartAtlasPOU I M a) := hne
      rw [hempty] at this
      exact this
    simp only [Function.mem_support, ne_eq, hzero, ENNReal.ofReal_zero,
      not_true_eq_false] at ha
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def, Measure.sum_apply _ himg]
  refine le_trans (ENNReal.tsum_le_tsum (fun a =>
    pou_term_map_le (I := I) g hU hKmeas hKU hf himg a)) ?_
  rw [tsum_subtype_eq_of_support_subset hsupp,
    ← lintegral_tsum (fun a : T => hsm a.val)]
  refine le_of_eq (lintegral_congr (fun x => ?_))
  rw [ENNReal.tsum_mul_right]
  have hone : (∑' a : T, ENNReal.ofReal (chartAtlasPOU I M a.val (f x))) = 1 := by
    rw [← tsum_subtype_eq_of_support_subset (hsupp_pou x)]
    exact tsum_ofReal_pou_eq_one (I := I) (chartAtlasPOU I M) (f x)
  rw [hone, one_mul]

end Measure
end Integral
end DifferentialGeometry

end
