import DifferentialGeometry.Analysis.Parabolic.Harnack.LiYau
import DifferentialGeometry.Analysis.Parabolic.Harnack.PathIntegration
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology Bundle

namespace DifferentialGeometry.Analysis.Parabolic.Harnack

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M]

theorem heat_solution_one_point_harnack_of_nonnegative_ricci
    [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) * u b x := by
  classical
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  have hly_all : ∀ t : ℝ, 0 < t →
      liYauQuantity g (fun τ y => Real.log (u τ y)) t x ≤ n / (2 * t) :=
    fun t ht => by
      simpa [n] using liYau_estimate_of_nonnegative_ricci (I := I) (M := M) g hRic u hu hpos hpde ht x
  have hliYau_bound : ∀ t ∈ Set.Icc a b,
      -(n / 2 / t) ≤ deriv (fun s => u s x) t / u t x := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hly := hly_all t htpos
    have hlogderiv : deriv (fun s => Real.log (u s x)) t = deriv (fun s => u s x) t / u t x := by
      have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
        have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
          contMDiff_id.prodMk contMDiff_const
        exact contMDiff_iff_contDiff.mp (hu.comp hc)
      have hder : HasDerivAt (fun s => u s x) (deriv (fun s => u s x) t) t :=
        (ContDiff.differentiable hu_slice (by norm_num) t).hasDerivAt
      exact (hder.log (hpos t x).ne').deriv
    have hq_nonneg_grad : 0 ≤ g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := by
      let v : TangentSpace I x := gradientFun (I := I) g (fun y => Real.log (u t y)) x
      have hvnonneg : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · rw [hv]
          simp
        · exact le_of_lt (g.pos x v hv)
      simpa [v] using hvnonneg
    have hq : liYauQuantity g (fun τ y => Real.log (u τ y)) t x =
        g.inner x (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) -
          deriv (fun s => Real.log (u s x)) t := rfl
    have hstep : -(n / (2 * t)) ≤ deriv (fun s => Real.log (u s x)) t := by
      rw [hq] at hly
      have hgrad_le : 0 ≤ g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) := hq_nonneg_grad
      linarith
    rw [hlogderiv] at hstep
    have hrewrite : n / (2 * t) = n / 2 / t := by
      field_simp [htpos.ne']
    rw [hrewrite] at hstep
    simpa using hstep
  have hu_path_pos : ∀ t ∈ Set.Icc a b, 0 < u t x := fun t ht => hpos t x
  have hderivative_cont : ContinuousOn (fun t : ℝ => deriv (fun s => u s x) t) (Set.Icc a b) := by
    have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
        contMDiff_id.prodMk contMDiff_const
      exact contMDiff_iff_contDiff.mp (hu.comp hc)
    have hder_cont : Continuous (fun t : ℝ => deriv (fun s => u s x) t) :=
      ContDiff.iterate_deriv 1 hu_slice |>.continuous
    exact hder_cont.continuousOn
  have hu_path_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => u s x) (deriv (fun s => u s x) t) t := by
    intro t ht
    have hu_slice : ContDiff ℝ ∞ (fun s => u s x) := by
      have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, x)) :=
        contMDiff_id.prodMk contMDiff_const
      exact contMDiff_iff_contDiff.mp (hu.comp hc)
    exact (ContDiff.differentiable hu_slice (by norm_num) t).hasDerivAt
  have hbridge := harnack_endpoint_of_li_yau_bound
    (V := ℝ) (u := fun t : ℝ => u t x)
    (derivative := fun t : ℝ => deriv (fun s => u s x) t)
    (timePart := fun t : ℝ => deriv (fun s => u s x) t / u t x)
    (gradient := fun _ : ℝ => (0 : ℝ))
    (velocity := fun _ : ℝ => (0 : ℝ))
    (a := a) (b := b) (c := n / 2) (alpha := (1 : ℝ))
    (by norm_num) ha hab hu_path_pos hderivative_cont continuousOn_const
    hu_path_deriv (by intro t ht; simp) (by
      intro t ht
      simpa using hliYau_bound t ht)
  simpa [n] using hbridge

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem metric_inner_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem metric_inner_add_inner_ge_neg_quarter
    (g : SmoothRiemannianMetric I M) (x : M) (p v : TangentSpace I x) :
    -(1 / 4) * g.inner x v v ≤ g.inner x p p + g.inner x p v := by
  let w : TangentSpace I x := p + ((1 / 2 : ℝ)) • v
  have hnonneg : 0 ≤ g.inner x w w := metric_inner_nonneg g x w
  have hsq : g.inner x w w = g.inner x p p + g.inner x p v + (1 / 4) * g.inner x v v := by
    have hlin1 : g.inner x (p + ((1 / 2 : ℝ)) • v) = g.inner x p + ((1 / 2 : ℝ)) • g.inner x v := by
      rw [(g.inner x).map_add]
      congr 1
      exact (g.inner x).map_smul (1 / 2 : ℝ) v
    have ha : (g.inner x p) (p + ((1 / 2 : ℝ)) • v) =
        g.inner x p p + (1 / 2) * g.inner x p v := by
      rw [(g.inner x p).map_add]
      congr 1
      exact ((g.inner x) p).map_smul (1 / 2 : ℝ) v
    have hb : (((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) =
        (1 / 2) * g.inner x v p + (1 / 4) * g.inner x v v := by
      rw [ContinuousLinearMap.smul_apply]
      rw [(g.inner x v).map_add]
      rw [smul_eq_mul, mul_add]
      congr 1
      have hms := ((g.inner x) v).map_smul (1 / 2 : ℝ) v
      rw [hms]
      simp [smul_eq_mul]
      ring
    calc
      g.inner x w w = (g.inner x p + ((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) := by
        rw [← hlin1]
      _ = (g.inner x p) (p + ((1 / 2 : ℝ)) • v) +
          (((1 / 2 : ℝ)) • g.inner x v) (p + ((1 / 2 : ℝ)) • v) := by
        rfl
      _ = (g.inner x p p + (1 / 2) * g.inner x p v) +
          ((1 / 2) * g.inner x v p + (1 / 4) * g.inner x v v) := by
        rw [ha, hb]
      _ = g.inner x p p + g.inner x p v + (1 / 4) * g.inner x v v := by
        rw [g.symm x p v]
        ring
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x y : M) :
    u a x ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
      Real.exp ((riemannianEDist I x y).toReal ^ 2 / (4 * (b - a))) * u b y := by
  classical
  let n : ℝ := (Module.finrank ℝ E : ℝ)
  let d : ℝ := (riemannianEDist I x y).toReal
  have hne_top : riemannianEDist I x y ≠ ⊤ := riemannianEDist_ne_top (I := I) x y
  have hd_nn : 0 ≤ d := ENNReal.toReal_nonneg
  by_cases hd0 : d = 0
  · have hx_eq_y : x = y := by
      have hd0' : riemannianEDist I x y = 0 := by
        have hreal : riemannianEDist I x y = ENNReal.ofReal d := by
          rw [← ENNReal.ofReal_toReal hne_top]
        rw [hreal, hd0, ENNReal.ofReal_zero]
      exact riemannianEDist_eq_zero_imp_eq (I := I) x y hd0'
    subst hx_eq_y
    simpa [n, riemannianEDist_self] using heat_solution_one_point_harnack_of_nonnegative_ricci
      (I := I) (M := M) g hRic u hu hpos hpde ha (le_of_lt hab) x
  · have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd0)
    obtain ⟨v, hv_exp, hv_len⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm x y
    let uvec : TangentSpace I x := d⁻¹ • v
    have hvv_nn : 0 ≤ g.inner x v v := metric_inner_nonneg g x v
    have hvv_sq : g.inner x v v = d ^ 2 := by
      have := congrArg (· ^ 2) hv_len
      simpa [Real.sq_sqrt hvv_nn] using this
    have huu : g.inner x uvec uvec = 1 := by
      have hbil : g.inner x uvec uvec = d⁻¹ * (d⁻¹ * g.inner x v v) := by
        dsimp [uvec]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hbil, hvv_sq]
      field_simp [hd0]
    have hdu : d • uvec = v := by
      dsimp [uvec]
      rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x uvec
    have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x uvec
    have hγd : γ d = y := by
      have hsmul : intrinsicGeodesic (I := I) g hEnorm x (d • uvec) 1 = γ d :=
        intrinsicGeodesic_smul (I := I) g hEnorm x uvec d
      rw [← hsmul, hdu]
      have hexp : expMapIntrinsic (I := I) g hEnorm x v = y := hv_exp
      rw [expMapIntrinsic_def] at hexp
      exact hexp
    have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm x uvec
    have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
      isGeodesic_contMDiff (I := I) g
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x uvec) hγ_cont
    have hγ_speed : ∀ s : ℝ,
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = 1 := by
      intro s
      have hsp := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x uvec s
      simpa [γ] using hsp.trans huu
    let τ : ℝ → M := fun t => γ ((t - a) / (b - a) * d)
    have hba_pos : 0 < b - a := sub_pos.mpr hab
    have hs_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (t - a) / (b - a) * d) := by
      have hs1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (fun t : ℝ => (t - a) * (1 / (b - a)) * d) := by
        simpa [mul_assoc] using
          ((contMDiff_id.sub contMDiff_const).mul (contMDiff_const (c := 1 / (b - a)))).mul
            (contMDiff_const (c := d))
      refine ContMDiff.congr hs1 ?_
      intro t
      simp [div_eq_mul_inv]
    have hτ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ τ := by
      simpa [τ] using hγ_smooth.comp hs_smooth
    have hτa : τ a = x := by
      simp [τ, hγ0]
    have hτb : τ b = y := by
      have hval : (b - a) / (b - a) * d = d := by
        field_simp [ne_of_gt hba_pos]
      simpa [τ, hval] using hγd
    have hτ_speed : ∀ t : ℝ,
        g.inner (τ t) (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)) = (d / (b - a)) ^ 2 := by
      intro t
      have hsderiv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (fun t : ℝ => (t - a) / (b - a) * d) t (1 : ℝ) = d / (b - a) := by
        rw [mfderiv_eq_fderiv]
        have hd : deriv (fun t : ℝ => (t - a) / (b - a) * d) t = d / (b - a) := by
          have h1 : HasDerivAt (fun t : ℝ => t - a) 1 t := by
            simpa using (hasDerivAt_id t).sub_const a
          have h2 : HasDerivAt (fun t : ℝ => (t - a) * (1 / (b - a)))
              (1 * (1 / (b - a))) t := by
            simpa using (h1.mul (hasDerivAt_const t (1 / (b - a))))
          have h3 : HasDerivAt (fun t : ℝ => (t - a) * (1 / (b - a)) * d)
              ((1 * (1 / (b - a))) * d) t := by
            simpa using h2.mul (hasDerivAt_const t d)
          have h4 : HasDerivAt (fun t : ℝ => (t - a) / (b - a) * d) (d / (b - a)) t := by
            simpa [div_eq_mul_inv, mul_assoc, mul_comm] using h3
          exact h4.deriv
        have hf : (fderiv ℝ (fun t : ℝ => (t - a) / (b - a) * d) t) (1 : ℝ) =
            deriv (fun t : ℝ => (t - a) / (b - a) * d) t :=
          fderiv_apply_one_eq_deriv (f := fun t : ℝ => (t - a) / (b - a) * d) (x := t)
        calc
          (fderiv ℝ (fun t : ℝ => (t - a) / (b - a) * d) t) (1 : ℝ)
              = deriv (fun t : ℝ => (t - a) / (b - a) * d) t := hf
          _ = d / (b - a) := hd
      have hcomp := mfderiv_comp_apply
        (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
        (g := γ) (f := fun t : ℝ => (t - a) / (b - a) * d)
        (x := t)
        (hγ_smooth.mdifferentiableAt (x := (t - a) / (b - a) * d) (by norm_num))
        (hs_smooth.mdifferentiableAt (x := t) (by norm_num))
        (1 : ℝ)
      have hc := congrArg (fun c : TangentSpace 𝓘(ℝ, ℝ) ((t - a) / (b - a) * d) =>
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) c) hsderiv
      have hct : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun t : ℝ => (t - a) / (b - a) * d)) t (1 : ℝ) =
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (d / (b - a)) := hcomp.trans hc
      have hchain : mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) =
          (d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ) := by
        have hτe : mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) =
            mfderiv 𝓘(ℝ, ℝ) I (γ ∘ (fun t : ℝ => (t - a) / (b - a) * d)) t (1 : ℝ) := by
          rfl
        rw [hτe, hct]
        have harg : mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (d / (b - a)) =
            (d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ) := by
          have hc1 : (d / (b - a)) = (d / (b - a)) • (1 : ℝ) := by simp
          have hms := (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d)).map_smul
            (d / (b - a)) (1 : ℝ)
          conv_lhs =>
            arg 2
            rw [hc1]
          exact hms
        exact harg
      rw [hchain]
      have hlin2 : g.inner (τ t)
          ((d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ))
          ((d / (b - a)) • mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)) =
          (d / (b - a)) ^ 2 * g.inner (τ t)
            (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)) := by
        let c : ℝ := d / (b - a)
        let w : TangentSpace I (τ t) :=
          mfderiv 𝓘(ℝ, ℝ) I γ ((t - a) / (b - a) * d) (1 : ℝ)
        have hms1 : g.inner (τ t) (c • w) (c • w) =
            c • g.inner (τ t) w (c • w) := by
          have hms := (g.inner (τ t)).map_smul c w
          have happ := congrArg (fun L : TangentSpace I (τ t) →L[ℝ] ℝ => L (c • w)) hms
          simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
        have hms2 : g.inner (τ t) w (c • w) = c • g.inner (τ t) w w := by
          have hms := ((g.inner (τ t)) w).map_smul c w
          simp [smul_eq_mul]
        calc
          g.inner (τ t) (c • w) (c • w)
              = c • g.inner (τ t) w (c • w) := hms1
          _ = c • (c • g.inner (τ t) w w) := by rw [hms2]
          _ = c ^ 2 * g.inner (τ t) w w := by
            simp [smul_eq_mul]
            ring
      rw [hlin2]
      have hτγ : τ t = γ ((t - a) / (b - a) * d) := rfl
      rw [hτγ]
      have hsp := hγ_speed ((t - a) / (b - a) * d)
      rw [hsp]
      ring
    let f : ℝ → M → ℝ := fun s y => Real.log (u s y)
    have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.1 p.2) := by
      simpa [f] using
        DifferentialGeometry.Analysis.Parabolic.Moser.contMDiff_log_of_pos hu hpos
    have hly_all : ∀ (t : ℝ) (z : M), 0 < t →
        liYauQuantity g f t z ≤ n / (2 * t) := by
      intro t z ht
      simpa [n, f] using liYau_estimate_of_nonnegative_ricci
        (I := I) (M := M) g hRic u hu hpos hpde ht z
    let τ' : ℝ → (p : M) → TangentSpace I p :=
      fun t _ => mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)
    have hτ'_def : ∀ t : ℝ, τ' t (τ t) = mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ) := by
      intro t
      rfl
    let timePart : ℝ → ℝ := fun t => deriv (fun s : ℝ => Real.log (u s (τ t))) t
    let gradSq : ℝ → ℝ := fun t =>
      g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
        (gradientFun (I := I) g (f t) (τ t))
    let innerGV : ℝ → ℝ := fun t =>
      g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
        (τ' t (τ t))
    let speedSq : ℝ → ℝ := fun _ => (d / (b - a)) ^ 2
    let derivative : ℝ → ℝ := fun t => deriv (fun s => u s (τ s)) t
    have hhu : ∀ t ∈ Icc a b, 0 < u t (τ t) := fun t ht => hpos t (τ t)
    have hderiv_cont : ContinuousOn derivative (Icc a b) := by
      have huc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => u s (τ s)) :=
        hu.comp (contMDiff_id.prodMk hτ_smooth)
      have hc : Continuous (fun t => deriv (fun s => u s (τ s)) t) :=
        ContDiff.iterate_deriv 1 (contMDiff_iff_contDiff.mp huc) |>.continuous
      exact hc.continuousOn
    have hderiv : ∀ t ∈ Icc a b,
        HasDerivAt (fun s => u s (τ s)) (derivative t) t := by
      intro t ht
      have huc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => u s (τ s)) :=
        hu.comp (contMDiff_id.prodMk hτ_smooth)
      exact (ContDiff.differentiable (contMDiff_iff_contDiff.mp huc) (by norm_num) t).hasDerivAt
    have hpath : ∀ t ∈ Icc a b,
        derivative t / u t (τ t) = timePart t + innerGV t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      have hlog_curve := deriv_along_curve_eq (I := I) (M := M) g
        (F := f) hf hτ_smooth (t := t)
      have hlog_deriv_curve : deriv (fun s => Real.log (u s (τ s))) t =
          deriv (fun s => Real.log (u s (τ t))) t +
            g.inner (τ t) (gradientFun (I := I) g (f t) (τ t))
              (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ)) := by
        simpa [f] using hlog_curve
      have hlog_ratio : deriv (fun s => Real.log (u s (τ s))) t =
          derivative t / u t (τ t) := by
        have huc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => u s (τ s)) :=
          hu.comp (contMDiff_id.prodMk hτ_smooth)
        have hc : ContDiff ℝ ∞ (fun s => u s (τ s)) :=
          contMDiff_iff_contDiff.mp huc
        have hd : HasDerivAt (fun s => u s (τ s)) (derivative t) t :=
          (ContDiff.differentiable hc (by norm_num) t).hasDerivAt
        exact (hd.log (hpos t (τ t)).ne').deriv
      rw [← hlog_ratio]
      rw [hlog_deriv_curve]
    have hliYau : ∀ t ∈ Icc a b,
        -(n / 2 / t) + gradSq t ≤ timePart t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
      have hly := hly_all t (τ t) ht_pos
      have hq_id : liYauQuantity g f t (τ t) = gradSq t - timePart t := rfl
      have hly' : gradSq t - timePart t ≤ n / (2 * t) := by
        rw [hq_id] at hly
        exact hly
      have hn : n / (2 * t) = n / 2 / t := by
        field_simp [ht_pos.ne']
      rw [hn] at hly'
      linarith
    have hquad : ∀ t ∈ Icc a b,
        -(1 / 4) * speedSq t ≤ gradSq t + innerGV t := by
      intro t ht
      have hq := metric_inner_add_inner_ge_neg_quarter g (τ t)
        (gradientFun (I := I) g (f t) (τ t))
        (mfderiv 𝓘(ℝ, ℝ) I τ t (1 : ℝ))
      have hsp := hτ_speed t
      simp [speedSq, gradSq, innerGV, τ', hτ'_def] at hq ⊢
      nlinarith [hq, hsp]
    have hbridge := harnack_endpoint_of_li_yau_bound_abstract
      (u := fun t => u t (τ t))
      (derivative := derivative)
      (timePart := timePart)
      (gradSq := gradSq)
      (innerGV := innerGV)
      (speedSq := speedSq)
      (a := a) (b := b) (c := n / 2) (alpha := (1 : ℝ))
      ha (le_of_lt hab) hhu hderiv_cont (by
        simpa [speedSq] using continuousOn_const) hderiv hpath
      (fun t ht => by simpa using hliYau t ht)
      (fun t ht => by simpa using hquad t ht)
    have hfinal : u a (τ a) ≤ (b / a) ^ (n / 2) *
        Real.exp ((d ^ 2) / (4 * (b - a))) * u b (τ b) := by
      have hintegral : 4⁻¹ * (∫ t in a..b, speedSq t) = d ^ 2 / (4 * (b - a)) := by
        have hc : (∫ t in a..b, (d / (b - a)) ^ 2) = (d / (b - a)) ^ 2 * (b - a) := by
          simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        have hpc : (fun t : ℝ => speedSq t) = fun _ : ℝ => (d / (b - a)) ^ 2 := by
          funext t
          rfl
        rw [hpc, hc]
        norm_num
        field_simp [ne_of_gt hba_pos]
      simpa [hintegral, hτa, hτb] using hbridge
    rw [hτa, hτb] at hfinal
    simpa [n] using hfinal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem heat_solution_harnack_uniform_upper_bound_of_nonnegative_ricci
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle (1 : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRic : ∀ x v, 0 ≤ ricciTensor (I := I) g x v v)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hpde : ∀ t x, deriv (fun s => u s x) t =
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (y₀ : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : M, u a x ≤ C * u b y₀ := by
  classical
  have hfcont : Continuous (fun x : M => riemannianEDist I x y₀) :=
    continuous_riemannianEDist_to (I := I) y₀
  obtain ⟨xmax, _hxm, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
      Set.univ_nonempty hfcont.continuousOn
  let D : ℝ := (riemannianEDist I xmax y₀).toReal
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hbound : ∀ x : M, (riemannianEDist I x y₀).toReal ≤ D := by
    intro x
    have hle : riemannianEDist I x y₀ ≤ riemannianEDist I xmax y₀ :=
      hmax (Set.mem_univ x)
    have hne1 : riemannianEDist I x y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) x y₀
    have hne2 : riemannianEDist I xmax y₀ ≠ ⊤ := riemannianEDist_ne_top (I := I) xmax y₀
    exact (ENNReal.toReal_le_toReal hne1 hne2).mpr hle
  let C : ℝ := (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (D ^ 2 / (4 * (b - a)))
  have hbpos : 0 < b := lt_trans ha hab
  have hba_pos : 0 < b / a := div_pos hbpos ha
  have hA_nonneg : 0 ≤ (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
    exact Real.rpow_nonneg (le_of_lt hba_pos) _
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.rpow_pos_of_pos hba_pos _) (Real.exp_pos _)
  refine ⟨C, hC_pos, ?_⟩
  intro x
  have hxy := heat_solution_harnack_of_nonnegative_ricci
    (I := I) (M := M) g hEnorm hRic u hu hpos hpde ha hab x y₀
  have hdD : (riemannianEDist I x y₀).toReal ^ 2 ≤ D ^ 2 := by
    have hd : 0 ≤ (riemannianEDist I x y₀).toReal := ENNReal.toReal_nonneg
    have hmul := mul_self_le_mul_self hd (hbound x)
    simpa [pow_two] using hmul
  have hexp_le : Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
      Real.exp (D ^ 2 / (4 * (b - a))) := by
    have hba : 0 < b - a := sub_pos.mpr hab
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hdD (by positivity))
  have hprod_le : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) * u b y₀ ≤
      C * u b y₀ := by
    have h1 : (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp ((riemannianEDist I x y₀).toReal ^ 2 / (4 * (b - a))) ≤
        (b / a) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (D ^ 2 / (4 * (b - a))) := by
      exact mul_le_mul_of_nonneg_left hexp_le hA_nonneg
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (hpos b y₀))
    simpa [C] using h2
  linarith

end DifferentialGeometry.Analysis.Parabolic.Harnack

end
