import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.QuadraticBound
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Comparison.Volume.FamilyParamControl
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff Bundle Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
private theorem exists_param_speed
    {D : RealTimeInterval}
    (g : Real → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a b : Real} (hab : a ≤ b) (hK : Set.Icc a b ⊆ D.carrier)
    (Psi : PartialDiffeomorph 𝓘(Real, E) I E M 1)
    {B : Set E} (hB : B ⊆ Psi.source) (hBne : B.Nonempty)
    (hBcompact : IsCompact B) :
    ∃ L : Real, 1 ≤ L ∧
      ∀ t ∈ Set.Icc a b, ∀ w ∈ B, ∀ v : E,
        Real.sqrt
            ((g t).inner (Psi w)
              (mfderiv 𝓘(Real, E) I Psi w v)
              (mfderiv 𝓘(Real, E) I Psi w v)) ≤
          L * ‖v‖ := by
  let T := {t : Real // t ∈ Set.Icc a b}
  let P := T × B
  let U : Set E := Metric.closedBall (0 : E) 1
  let Q := P × U
  let speed : Q → Real := fun q ↦
    Real.sqrt
      ((g q.1.1.1).inner (Psi q.1.2.1)
        (mfderiv 𝓘(Real, E) I Psi q.1.2.1 q.2.1)
        (mfderiv 𝓘(Real, E) I Psi q.1.2.1 q.2.1))
  have htangent : Continuous (fun q : Q ↦
      TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) (Psi q.1.2.1)
        (mfderiv 𝓘(Real, E) I Psi q.1.2.1 q.2.1)) := by
    let lift : Q → TangentBundle 𝓘(Real, E) E :=
      fun q ↦ ⟨q.1.2.1, q.2.1⟩
    have hlift : Continuous lift :=
      (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.continuous.comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
    simpa [lift] using
      (PartialDiffeomorph.mfderiv_cont Psi (by norm_num) lift hlift
        (fun q ↦ hB q.1.2.2))
  have hspeed : Continuous speed := by
    have hquad :=
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn
        (I := I) (M := M) g hG hK
    have hpull : Continuous (fun q : Q ↦
        (q.1.1,
          TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) (Psi q.1.2.1)
            (mfderiv 𝓘(Real, E) I Psi q.1.2.1 q.2.1))) :=
      (continuous_fst.comp continuous_fst).prodMk htangent
    exact Real.continuous_sqrt.comp (hquad.comp hpull)
  letI : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hBcompact
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (by
      simpa [U] using isCompact_closedBall (0 : E) 1)
  have hQne : (Set.univ : Set Q).Nonempty := by
    obtain ⟨w, hw⟩ := hBne
    let q : Q :=
      ((⟨a, Set.left_mem_Icc.mpr hab⟩, ⟨w, hw⟩),
        ⟨0, by simp [U]⟩)
    exact ⟨q, Set.mem_univ q⟩
  obtain ⟨qmax, _hqmax, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Q)).exists_isMaxOn
      hQne hspeed.continuousOn
  let L : Real := max 1 (speed qmax)
  have hL_one : 1 ≤ L := le_max_left _ _
  refine ⟨L, hL_one, ?_⟩
  intro t ht w hw v
  by_cases hv : v = 0
  · subst v
    have hd0 :
        mfderiv 𝓘(Real, E) I Psi w (0 : E) =
          (0 : TangentSpace I (Psi w)) := map_zero _
    rw [hd0]
    simp
  · have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : E := ‖v‖⁻¹ • v
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (ne_of_gt hvnorm_pos)
    have hu_mem : u ∈ U := by
      simp [U, Metric.mem_closedBall, dist_zero_right, hu_norm]
    let q : Q := ((⟨t, ht⟩, ⟨w, hw⟩), ⟨u, hu_mem⟩)
    have hspeed_le : speed q ≤ L :=
      le_trans ((isMaxOn_iff.mp hmax) q (Set.mem_univ q)) (le_max_right _ _)
    have hv_from_u : ‖v‖ • u = v := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvnorm_pos), one_smul]
    have hscale :
        (g t).inner (Psi w)
            (mfderiv 𝓘(Real, E) I Psi w v)
            (mfderiv 𝓘(Real, E) I Psi w v) =
          ‖v‖ ^ 2 *
            (g t).inner (Psi w)
              (mfderiv 𝓘(Real, E) I Psi w u)
              (mfderiv 𝓘(Real, E) I Psi w u) := by
      conv_lhs => rw [← hv_from_u]
      have hdscale :
          mfderiv 𝓘(Real, E) I Psi w (‖v‖ • u) =
            ‖v‖ • mfderiv 𝓘(Real, E) I Psi w u := map_smul _ _ _
      rw [hdscale, metric_smul2]
      ring
    rw [hscale, Real.sqrt_mul (sq_nonneg ‖v‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    have hspeed_le' :
        Real.sqrt
            ((g t).inner (Psi w)
              (mfderiv 𝓘(Real, E) I Psi w u)
              (mfderiv 𝓘(Real, E) I Psi w u)) ≤ L := by
      simpa [speed, q] using hspeed_le
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hspeed_le' (norm_nonneg v))

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
private theorem tensor_eval_cont
    {K : Set Real}
    {A : (t : Real) → (x : M) →
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun s : Real ↦ A s x (vec2 v w)) K := by
  rw [continuousOn_iff_continuous_restrict]
  exact hA.eval_continuous (P := {s : Real // s ∈ K}) (τ := Subtype.val)
    (b := fun _ ↦ x) continuous_subtype_val (fun p ↦ p.2) continuous_const
    (v := fun i _ ↦ vec2 v w i) (fun _ ↦ continuous_const)

private theorem deriv_Ici_start
    {a b : Real} (hab : a < b) (f e : Real → Real)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hecont : ContinuousWithinAt e (Set.Ioi a) a)
    (hint : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ici a) t) :
    HasDerivWithinAt f (e a) (Set.Ici a) a := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ⊆ Set.Ici a := fun _ ht ↦ ht.1.le
  have hwithin : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (e t) (Set.Ioo a b) t :=
    fun t ht ↦ (hint t ht).mono hsub
  have hdiff : DifferentiableOn Real f (Set.Ioo a b) :=
    fun t ht ↦ (hwithin t ht).differentiableWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, deriv f t = e t := by
    intro t ht
    rw [← derivWithin_of_isOpen hopen ht]
    exact (hwithin t ht).derivWithin (hopen.uniqueDiffWithinAt ht)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo a b)
    hdiff ?_ ?_ ?_
  · exact (hcont.continuousWithinAt ⟨le_rfl, hab.le⟩).mono
      Set.Ioo_subset_Icc_self
  · exact Ioo_mem_nhdsGT hab
  · exact hecont.tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab) hderiv).symm

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] in
theorem metricPDE_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular) :
    ∀ t ∈ Set.Icc a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real ↦ (S.base.metric s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (S.base.metric t) x v w)
        (Set.Icc a b) t := by
  have hmetricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun s : Real ↦ (S.base.metric s).inner x v w)
        (Set.Icc a b) := by
    intro x v w
    refine (tensor_eval_cont (I := I) hS.smoothMetric.metricTensor_cont x v w).mono ?_
    exact hslab
  have hricCont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Icc a b) := by
    intro x v w
    have hcont := (tensor_eval_cont (I := I) hS.ricciCont x v w).mono hslab
    refine (hcont.congr fun s _ ↦ ?_).const_mul (-2)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply,
      SolutionFamily.ricciAt]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric s) x v w).symm
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have hecont : ContinuousWithinAt
        (fun s : Real ↦
          (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
        (Set.Ioi a) a := by
      have hmem : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) :=
        Filter.mem_of_superset (Ioo_mem_nhdsGT hab)
          (fun s hs ↦ ⟨hs.1.le, hs.2.le⟩)
      exact ((hricCont x v w).continuousWithinAt ⟨le_rfl, hab.le⟩)
        |>.mono_of_mem_nhdsWithin hmem
    have hint : ∀ s ∈ Set.Ioo a b,
        HasDerivWithinAt
          (fun r : Real ↦ (S.base.metric r).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w)
          (Set.Ici a) s := by
      intro s hs
      let τ : RealTimeInterval.RegularTime D :=
        ⟨s, hreg ⟨hs.1, hs.2.le⟩⟩
      have hraw := metricDerivAt (I := I) S hS τ x v w
      simpa [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
        DifferentialGeometry.ricciCurvatureAt_leviCivita_apply_eq_ricciTensor] using
        hraw.hasDerivWithinAt
    exact (deriv_Ici_start hab _ _ (hmetricCont x v w) hecont hint).mono
      (fun _ hs ↦ hs.1)
  · let τ : RealTimeInterval.RegularTime D :=
      ⟨t, hreg ⟨hat, ht.2⟩⟩
    have hraw := metricDerivAt (I := I) S hS τ x v w
    simpa [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] using hraw.hasDerivWithinAt

theorem exp_bounds_log
    {fa fb R : Real} (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| ≤ R) :
    Real.exp (-R) * fa ≤ fb ∧ fb ≤ Real.exp R * fa := by
  have hlo : -R ≤ Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhi : Real.log fb - Real.log fa ≤ R := (abs_le.mp hlog).2
  constructor
  · have hratio : Real.exp (-R) ≤ fb / fa := by
      apply (Real.le_log_iff_exp_le (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlo
    calc
      Real.exp (-R) * fa ≤ (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio hfa.le
      _ = fb := by field_simp
  · have hratio : fb / fa ≤ Real.exp R := by
      apply (Real.log_le_iff_le_exp (div_pos hfb hfa)).mp
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhi
    calc
      fb = (fb / fa) * fa := by field_simp
      _ ≤ Real.exp R * fa := mul_le_mul_of_nonneg_right hratio hfa.le

omit [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  [IsManifold I 1 M]
  [SigmaCompactSpace M] in
theorem metricEquiv_Icc
    (g : Real → SmoothRiemannianMetric I M)
    {a b K : Real}
    (hpde : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : Real ↦ (g s).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
          (Set.Icc a b) t)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g t) x v v| ≤
          K * (g t).inner x v v) :
    ∀ s ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        Real.exp (-(2 * K * (s - a))) * (g a).inner x v v ≤
            (g s).inner x v v ∧
          (g s).inner x v v ≤
            Real.exp (2 * K * (s - a)) * (g a).inner x v v := by
  intro s hs x v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hpos : ∀ t : Real, 0 < (g t).inner x v v :=
    fun t ↦ (g t).pos x v hv
  have hsub : Set.Icc a s ⊆ Set.Icc a b :=
    fun _ ht ↦ ⟨ht.1, ht.2.trans hs.2⟩
  have hderiv : ∀ t ∈ Set.Icc a s,
      HasDerivWithinAt
        (fun r : Real ↦ Real.log ((g r).inner x v v))
        ((-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v)
        (Set.Icc a s) t := by
    intro t ht
    exact ((hpde t (hsub ht) x v v).mono hsub).log (hpos t).ne'
  have hbound : ∀ t ∈ Set.Icc a s,
      ‖(-2 : Real) * ricciTensor (I := I) (g t) x v v /
          (g t).inner x v v‖ ≤ 2 * K := by
    intro t ht
    have hden := hpos t
    have hricT := hric t (hsub ht) x v
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [abs_mul]
    norm_num
    nlinarith
  have hmvt := (convex_Icc a s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1)
  have hlog :
      |Real.log ((g s).inner x v v) - Real.log ((g a).inner x v v)| ≤
        2 * K * (s - a) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs.1)] at hmvt
    exact hmvt
  exact exp_bounds_log (hpos a) (hpos s) hlog

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M] in
private theorem metric_pair_Icc
    (g : Real → SmoothRiemannianMetric I M)
    {a b K s t : Real}
    (hpde : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun u : Real ↦ (g u).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g r) x v w)
          (Set.Icc a b) r)
    (hric : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g r) x v v| ≤
          K * (g r).inner x v v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x : M) (v : TangentSpace I x) :
    Real.exp (-(2 * K * |s - t|)) * (g t).inner x v v ≤
        (g s).inner x v v ∧
      (g s).inner x v v ≤
        Real.exp (2 * K * |s - t|) * (g t).inner x v v := by
  rcases le_total t s with hts | hst
  · have hsub : Set.Icc t s ⊆ Set.Icc a b := by
      intro r hr
      exact ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
    have hequiv := metricEquiv_Icc (I := I) g
      (fun r hr y w z ↦ (hpde r (hsub hr) y w z).mono hsub)
      (fun r hr y w ↦ hric r (hsub hr) y w)
      s ⟨hts, le_rfl⟩ x v
    simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hequiv
  · have hsub : Set.Icc s t ⊆ Set.Icc a b := by
      intro r hr
      exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    have hequiv := metricEquiv_Icc (I := I) g
      (fun r hr y w z ↦ (hpde r (hsub hr) y w z).mono hsub)
      (fun r hr y w ↦ hric r (hsub hr) y w)
      t ⟨hst, le_rfl⟩ x v
    have hleft :
        Real.exp (-(2 * K * (t - s))) * (g t).inner x v v ≤
          (g s).inner x v v := by
      calc
        Real.exp (-(2 * K * (t - s))) * (g t).inner x v v ≤
            Real.exp (-(2 * K * (t - s))) *
              (Real.exp (2 * K * (t - s)) * (g s).inner x v v) :=
          mul_le_mul_of_nonneg_left hequiv.2 (Real.exp_pos _).le
        _ = (g s).inner x v v := by
          rw [← mul_assoc, ← Real.exp_add]
          simp only [neg_add_cancel, Real.exp_zero, one_mul]
    have hright :
        (g s).inner x v v ≤
          Real.exp (2 * K * (t - s)) * (g t).inner x v v := by
      calc
        (g s).inner x v v =
            Real.exp (2 * K * (t - s)) *
              (Real.exp (-(2 * K * (t - s))) * (g s).inner x v v) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp only [add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (2 * K * (t - s)) * (g t).inner x v v :=
          mul_le_mul_of_nonneg_left hequiv.1 (Real.exp_pos _).le
    simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using
      And.intro hleft hright

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [IsManifold I 1 M]
  [SigmaCompactSpace M] in
/-- A uniform absolute Ricci bound compares intrinsic extended distances at any
two times in the same compact interval. -/
theorem edistEquiv_Icc
    (g : Real → SmoothRiemannianMetric I M)
    {a b K s t : Real}
    (hpde : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun u : Real ↦ (g u).inner x v w)
          ((-2 : Real) * ricciTensor (I := I) (g r) x v w)
          (Set.Icc a b) r)
    (hric : ∀ r ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (g r) x v v| ≤
          K * (g r).inner x v v)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (x y : M) :
    ENNReal.ofReal (Real.exp (-K * |s - t|)) *
          riemannianEDistOf (I := I) (g t) x y ≤
        riemannianEDistOf (I := I) (g s) x y ∧
      riemannianEDistOf (I := I) (g s) x y ≤
        ENNReal.ofReal (Real.exp (K * |s - t|)) *
          riemannianEDistOf (I := I) (g t) x y := by
  have hpair := metric_pair_Icc (I := I) g hpde hric hs ht
  have hsqrt_neg :
      Real.sqrt (Real.exp (-(2 * K * |s - t|))) =
        Real.exp (-K * |s - t|) := by
    calc
      Real.sqrt (Real.exp (-(2 * K * |s - t|))) =
          Real.exp (-(2 * K * |s - t|) / 2) :=
        (Real.exp_half _).symm
      _ = Real.exp (-K * |s - t|) := by
        congr 1
        ring
  have hsqrt_pos :
      Real.sqrt (Real.exp (2 * K * |s - t|)) =
        Real.exp (K * |s - t|) := by
    calc
      Real.sqrt (Real.exp (2 * K * |s - t|)) =
          Real.exp ((2 * K * |s - t|) / 2) :=
        (Real.exp_half _).symm
      _ = Real.exp (K * |s - t|) := by
        congr 1
        ring
  constructor
  · simpa only [hsqrt_neg] using
      le_edistOf_of_quad
        (I := I) (g t) (g s) (Real.exp_pos _)
        (fun z v ↦ (hpair z v).1) x y
  · simpa only [hsqrt_pos] using
      edistOf_le_of_quad
        (I := I) (g t) (g s) (Real.exp_pos _)
        (fun z v ↦ (hpair z v).2) x y

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem edistCont_Icc
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b K : Real} (hab : a < b)
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric t) x v v| ≤
          K * (S.base.metric t).inner x v v)
    (O : M) :
    ContinuousOn
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
  have hpde := metricPDE_Icc (I := I) S hS hab hslab hreg
  intro p hp
  let A : Real × M → Real := fun q ↦ 2 * K * |q.1 - p.1|
  let d₀ : Real × M → ENNReal := fun q ↦
    riemannianEDistOf (I := I) (S.base.metric p.1) O q.2
  have hA : Continuous A :=
    continuous_const.mul (continuous_fst.sub continuous_const).abs
  have hd₀ : Continuous d₀ := by
    have hdist : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O y) := by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist
        (I := I) (S.base.metric p.1) O
    exact hdist.comp continuous_snd
  have hlo : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q)))) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (Real.continuous_exp.comp hA.neg))
  have hhi : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q)))) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (Real.continuous_exp.comp hA))
  have hlo_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q))) * d₀ q) :=
    hlo.ennreal_mul hd₀
      (fun q ↦ Or.inl (ne_of_gt
        (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (Real.exp_pos _)))))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  have hhi_mul : Continuous (fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q))) * d₀ q) :=
    hhi.ennreal_mul hd₀
      (fun q ↦ Or.inl (ne_of_gt
        (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (Real.exp_pos _)))))
      (fun _ ↦ Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (-A q))) * d₀ q)
    (h := fun q : Real × M ↦
      ENNReal.ofReal (Real.sqrt (Real.exp (A q))) * d₀ q)
    ?_ ?_ ?_ ?_
  · simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
      (hlo_mul.tendsto p).mono_left inf_le_left
  · simpa only [A, d₀, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
      (hhi_mul.tendsto p).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hpair := metric_pair_Icc (I := I)
      (fun r ↦ S.base.metric r) hpde hric hq.1 hp.1
    exact le_edistOf_of_quad
      (I := I) (S.base.metric p.1) (S.base.metric q.1)
      (Real.exp_pos _) (fun y v ↦ (hpair y v).1) O q.2
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hpair := metric_pair_Icc (I := I)
      (fun r ↦ S.base.metric r) hpde hric hq.1 hp.1
    exact edistOf_le_of_quad
      (I := I) (S.base.metric p.1) (S.base.metric q.1)
      (Real.exp_pos _) (fun y v ↦ (hpair y v).2) O q.2

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The distance from a fixed center for a smooth Ricci-flow metric is jointly
continuous at that center and every regular time. -/
theorem edistContAt_ctr
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t : Real} (ht : t ∈ D.regular) (O : M) :
    ContinuousAt
      (fun p : Real × M ↦
        riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
      (t, O) := by
  classical
  obtain ⟨a, b, htab, hreg⟩ := D.exists_Icc_regular ht
  have hab : a ≤ b := htab.1.le.trans htab.2.le
  have hK : Set.Icc a b ⊆ D.carrier := hreg.trans D.regular_subset
  let Psi :=
    DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.expMapDiffeo
      (I := I) (S.base.metric t) O
  let R : Real :=
    DifferentialGeometry.Geometry.Riemannian.expMapC2Radius
      (I := I) (S.base.metric t) O / 4
  let B : Set E := Metric.closedBall (0 : E) (2 * R)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact div_pos
      (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (S.base.metric t) O)
      (by norm_num)
  have hB : B ⊆ Psi.source := by
    intro w hw
    apply DifferentialGeometry.Geometry.Riemannian.mem_expMapDiffeo_source_of_norm_lt_radius
        (I := I) (S.base.metric t) O
    have hw_le : ‖w‖ ≤ 2 * R := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hw
    have h2R_lt :
        2 * R <
          DifferentialGeometry.Geometry.Riemannian.expMapC2Radius
            (I := I) (S.base.metric t) O := by
      dsimp [R]
      nlinarith [DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (S.base.metric t) O]
    exact hw_le.trans_lt h2R_lt
  have hBne : B.Nonempty := by
    refine ⟨0, ?_⟩
    simp [B, hR_pos.le]
  have hBcompact : IsCompact B := by
    simpa [B] using isCompact_closedBall (0 : E) (2 * R)
  obtain ⟨L, hL_one, hctrl⟩ :=
    exists_param_speed (I := I) S.family.metric hS.smoothMetric
      hab hK Psi hB hBne hBcompact
  have hL_pos : 0 < L := zero_lt_one.trans_le hL_one
  change Filter.Tendsto
    (fun p : Real × M ↦
      riemannianEDistOf (I := I) (S.base.metric p.1) O p.2)
    (nhds (t, O))
    (nhds (riemannianEDistOf (I := I) (S.base.metric t) O O))
  rw [riemannianEDistOf_self]
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro eps heps
  by_cases hepstop : eps = (⊤ : ENNReal)
  · exact Filter.Eventually.of_forall fun _ ↦ by simp [hepstop]
  have heps_real : 0 < eps.toReal :=
    ENNReal.toReal_pos heps.ne' hepstop
  let delta : Real := min R (eps.toReal / (2 * L))
  have hdelta_pos : 0 < delta := by
    exact lt_min hR_pos (div_pos heps_real (mul_pos (by norm_num) hL_pos))
  have hdelta_R : delta ≤ R := min_le_left _ _
  have hsmall_source : Metric.ball (0 : E) delta ⊆ Psi.source := by
    intro z hz
    apply hB
    have hz_norm : ‖z‖ < delta := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    simp only [B, Metric.mem_closedBall, dist_zero_right]
    linarith
  have hspace_open : IsOpen (Psi '' Metric.ball (0 : E) delta) :=
    Psi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball hsmall_source
  have hO_image : O ∈ Psi '' Metric.ball (0 : E) delta := by
    refine ⟨0, by simpa using hdelta_pos, ?_⟩
    simpa [Psi] using
      (DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.expMapDiffeo_zero
        (I := I) (S.base.metric t) O)
  have htime : Set.Icc a b ∈ nhds t := Icc_mem_nhds htab.1 htab.2
  have hspace : Psi '' Metric.ball (0 : E) delta ∈ nhds O :=
    hspace_open.mem_nhds hO_image
  filter_upwards [prod_mem_nhds htime hspace] with q hq
  obtain ⟨z, hz, hzq⟩ := hq.2
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(S.base.metric q.1).toRiemannianMetric⟩
  have hspd : ∀ w ∈ B, ∀ xi : E,
      ‖mfderiv 𝓘(Real, E) I Psi w xi‖ₑ ≤
        ENNReal.ofReal (L * ‖xi‖) := by
    intro w hw xi
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    change ENNReal.ofReal
        (Real.sqrt
          ((S.base.metric q.1).inner (Psi w)
            (mfderiv 𝓘(Real, E) I Psi w xi)
            (mfderiv 𝓘(Real, E) I Psi w xi))) ≤
      ENNReal.ofReal (L * ‖xi‖)
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [SolutionOn.family_metric] using hctrl q.1 hq.1 w hw xi)
  have hzB : z ∈ B := by
    have hz_norm : ‖z‖ < delta := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    simp only [B, Metric.mem_closedBall, dist_zero_right]
    linarith
  have hzeroB : (0 : E) ∈ B := by
    simp [B, hR_pos.le]
  have hseg : segment Real (0 : E) z ⊆ B :=
    (convex_closedBall (0 : E) (2 * R)).segment_subset hzeroB hzB
  have hdist :=
    DifferentialGeometry.Geometry.Riemannian.param_edist_le
      (I := I) Psi hB hspd hseg
  have hzero : Psi 0 = O := by
    simpa [Psi] using
      (DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.expMapDiffeo_zero
        (I := I) (S.base.metric t) O)
  change Manifold.riemannianEDist I O q.2 ≤ eps
  rw [← hzq, ← hzero]
  refine hdist.trans (le_of_lt ?_)
  have hz_dist : dist (0 : E) z < delta := by
    simpa [Metric.mem_ball, dist_comm] using hz
  have hmul : L * dist (0 : E) z < eps.toReal := by
    calc
      L * dist (0 : E) z < L * delta :=
        mul_lt_mul_of_pos_left hz_dist hL_pos
      _ ≤ L * (eps.toReal / (2 * L)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hL_pos.le
      _ = eps.toReal / 2 := by field_simp
      _ < eps.toReal := by linarith
  exact (ENNReal.ofReal_lt_iff_lt_toReal
    (mul_nonneg hL_pos.le (dist_nonneg : 0 ≤ dist (0 : E) z)) hepstop).2 hmul

omit [NeZero (Module.finrank ℝ E)] in
theorem complete_of_ricBound
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b K : Real}
    (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioc a b ⊆ D.regular)
    (hK : 0 ≤ K)
    (hric : ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : TangentSpace I x,
        |ricciTensor (I := I) (S.base.metric t) x v v| ≤
          K * (S.base.metric t).inner x v v)
    (ha : RiemannianMetricComplete (I := I) (S.base.metric a))
    {s : Real} (hs : s ∈ Set.Icc a b) :
    RiemannianMetricComplete (I := I) (S.base.metric s) := by
  rcases eq_or_lt_of_le hs.1 with rfl | has
  · exact ha
  · have hslab' : Set.Icc a s ⊆ D.carrier :=
      fun _ ht ↦ hslab ⟨ht.1, ht.2.trans hs.2⟩
    have hreg' : Set.Ioc a s ⊆ D.regular :=
      fun _ ht ↦ hreg ⟨ht.1, ht.2.trans hs.2⟩
    have hpde := metricPDE_Icc (I := I) S hS has hslab' hreg'
    have hequiv := metricEquiv_Icc (I := I) (fun t ↦ S.base.metric t) hpde
      (fun t ht x v ↦ hric t ⟨ht.1, ht.2.trans hs.2⟩ x v)
      s ⟨has.le, le_rfl⟩
    have hC : 1 ≤ Real.exp (2 * K * (s - a)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (mul_nonneg (by norm_num) hK) (sub_nonneg.mpr has.le))
    refine RiemannianMetricComplete.of_uniformEquiv ha hC ?_
    intro x v
    simpa only [Real.exp_neg] using hequiv x v

end DifferentialGeometry.PDE.RicciFlow
