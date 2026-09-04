import DifferentialGeometry.Geometry.Geodesic.ChartRegularity
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The tangent-bundle lift of a curve given by its velocity. -/
def velocityLift (gamma : ℝ → M) (t : ℝ) : TangentBundle I M :=
  ⟨gamma t, mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t (1 : ℝ)⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] theorem velocityLift_proj (gamma : ℝ → M) (t : ℝ) :
    (velocityLift (I := I) gamma t).proj = gamma t := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem velocityLift_continuousAt
    {gamma : ℝ → M} {t : ℝ}
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t) :
    ContinuousAt (velocityLift (I := I) gamma) t := by
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hgamma.continuousAt, ?_⟩
  have hcoord := (velocity_coord_diff (I := I) gamma t hgamma).continuousAt
  have hbase : ∀ᶠ s in nhds t,
      gamma s ∈ (trivializationAt E (TangentSpace I) (gamma t)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using
      hgamma.continuousAt.preimage_mem_nhds
        ((chartAt H (gamma t)).open_source.mem_nhds (mem_chart_source H (gamma t)))
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [hbase] with s hs
  have hcoe := (trivializationAt E (TangentSpace I) (gamma t)).coe_linearMapAt_of_mem
    (R := ℝ) hs
  exact (congrFun hcoe (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s (1 : ℝ))).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem hasMFDerivAt_of_chartPush
    [I.Boundaryless]
    {f : ℝ → TangentBundle I M} {t : ℝ} {w : E × E}
    (hcont : ContinuousAt f t)
    (hpush : HasDerivAt (chartPushLift (I := I) f t) w t) :
    HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I.tangent f t
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
  have hpush_mdiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (E × E))
      (chartPushLift (I := I) f t) t :=
    hpush.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hf_mdiff : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I.tangent f t := by
    rw [mdifferentiableAt_iff_target]
    refine ⟨hcont, ?_⟩
    simpa only [chartPushLift, Function.comp_def] using hpush_mdiff
  have hf := hf_mdiff.hasMFDerivAt
  have hchart := (hasMFDerivAt_extChartAt (I := I.tangent)
    (mem_chart_source (ModelProd H E) (f t))).comp t hf
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := I.tangent)
      (mem_chart_source (ModelProd H E) (f t))] at hchart
  have hself : tangentCoordChange I.tangent (f t) (f t) (f t) =
      ContinuousLinearMap.id ℝ (E × E) := by
    apply ContinuousLinearMap.ext
    intro z
    exact tangentCoordChange_self (I := I.tangent) (x := f t) (z := f t) (v := z)
      (mem_extChartAt_source (I := I.tangent) (f t))
  rw [hself] at hchart
  have hchart' : HasMFDerivAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (E × E))
      (extChartAt I.tangent (f t) ∘ f) t (mfderiv (modelWithCornersSelf ℝ ℝ)
        I.tangent f t) := by
    simpa using hchart
  have heq := hchart'.hasFDerivAt.unique hpush.hasFDerivAt
  rw [heq] at hf
  exact hf

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem geoLift_hasMFDerivAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {t : ℝ}
    (hgeo : HasGeodesicEquationAt (I := I) g gamma t)
    (hreg : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I ∞ gamma t) :
    HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I.tangent
      (velocityLift (I := I) gamma) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorField (I := I) g (velocityLift (I := I) gamma t))) := by
  classical
  let y : M := gamma t
  let u : ℝ → E := chartLocalCurve (I := I) gamma t
  let c : ℝ → E × E := fun s => (u s, deriv u s)
  obtain ⟨v, a, hv, _hev, ha, halg⟩ := hgeo
  have hc : HasDerivAt c (v, a) t := by
    simpa only [c] using hv.prodMk ha
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
  have hreg2 : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t :=
    hreg.of_le h2le
  have hreg_ev : ∀ᶠ s in nhds t,
      ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp hreg2
  have hsrc : ∀ᶠ s in nhds t, gamma s ∈ (chartAt H y).source :=
    hreg.continuousAt.preimage_mem_nhds
      ((chartAt H y).open_source.mem_nhds (by simp only [y]; exact mem_chart_source H (gamma t)))
  have hchart_eq : chartPushLift (I := I) (velocityLift (I := I) gamma) t =ᶠ[nhds t] c := by
    filter_upwards [hreg_ev, hsrc] with s hsreg hssrc
    rw [chartPushLift_apply, FiberBundle.extChartAt]
    simp only [PartialEquiv.trans_apply, PartialEquiv.prod_coe, velocityLift_proj]
    change (extChartAt I y
        ((trivializationAt E (TangentSpace I) y (velocityLift (I := I) gamma s)).1),
      (trivializationAt E (TangentSpace I) y (velocityLift (I := I) gamma s)).2) =
        (u s, deriv u s)
    apply Prod.ext
    · change extChartAt I (gamma t) (gamma s) = extChartAt I (gamma t) (gamma s)
      rfl
    · have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
          (I := I) (M := M) (γ := gamma)
          (hsreg.mdifferentiableAt (by simp)) y hssrc
      have hbase : gamma s ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]
        exact hssrc
      have hcoe := (trivializationAt E (TangentSpace I) y).coe_linearMapAt_of_mem
        (R := ℝ) hbase
      rw [show (trivializationAt E (TangentSpace I) y
          (velocityLift (I := I) gamma s)).2 =
          (trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ (gamma s)
            (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s (1 : ℝ)) by
        simpa only [velocityLift] using
          (congrFun hcoe (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s (1 : ℝ))).symm]
      simpa only [c, u, y, chartLocalCurve_def, Function.comp_def,
        fderiv_apply_one_eq_deriv] using hbridge
  have hpush_va : HasDerivAt
      (chartPushLift (I := I) (velocityLift (I := I) gamma) t) (v, a) t :=
    hc.congr_of_eventuallyEq hchart_eq
  have hvel : (velocityLift (I := I) gamma t).snd = v := by
    have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := gamma)
      (hreg.mdifferentiableAt (by simp)) y
      (by simp only [y]; exact mem_chart_source H (gamma t))
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
      (x₀ := y) (x := gamma t)
      (by simp only [y]; exact mem_chart_source H (gamma t))] at hbridge
    simp only [y, mfderiv_extChartAt_self] at hbridge
    change mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t (1 : ℝ) =
      fderiv ℝ (extChartAt I (gamma t) ∘ gamma) t (1 : ℝ) at hbridge
    have hv_deriv : deriv u t = v := by simpa only [u] using hv.deriv
    change mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t (1 : ℝ) = v
    rw [fderiv_apply_one_eq_deriv] at hbridge
    exact hbridge.trans (by simpa only [u, chartLocalCurve_def, Function.comp_def] using hv_deriv)
  have ha_eq : a = -chartChristoffelContraction (I := I) g (gamma t) v v
      (extChartAt I (gamma t) (gamma t)) := eq_neg_of_add_eq_zero_left halg
  have hvf : geodesicVectorField (I := I) g (velocityLift (I := I) gamma t) = (v, a) := by
    rw [geodesicVectorField_def, velocityLift_proj, hvel, ha_eq]
    rfl
  rw [hvf]
  exact hasMFDerivAt_of_chartPush (I := I)
    (velocityLift_continuousAt (I := I) (hgamma := hreg2)) hpush_va

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The velocity lift of a geodesic on an open set follows the global geodesic vector field. -/
theorem geoLift_isIntegralOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J)
    (hgamma : IsGeodesicOn (I := I) g gamma J)
    (hcont : ContinuousOn gamma J) :
    IsMIntegralCurveOn (velocityLift (I := I) gamma)
      (geodesicVectorField (I := I) g) J := by
  intro t ht
  exact (geoLift_hasMFDerivAt (I := I) g (hgamma t ht)
    (isGeodesicOn_contMDiffAt_infty (I := I) g hJ ht hgamma hcont)).hasMFDerivWithinAt

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
