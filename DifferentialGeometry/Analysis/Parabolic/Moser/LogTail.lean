import DifferentialGeometry.Analysis.Parabolic.Moser.Oscillation

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def localizedSuperlevelMass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (level : ℝ) : ℝ :=
  ∫ x in {x : M | level < u.toFun x}, cutoff.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedSublevelMass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (level : ℝ) : ℝ :=
  ∫ x in {x : M | u.toFun x < level}, cutoff.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [I.Boundaryless] in
theorem localized_superlevel_chebyshev_of_center
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : center + r ≤ level) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Deviation (I := I) (M := M) cutoff u center := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let S : Set M := {x : M | level < u.toFun x}
  let oscilland : M → ℝ := fun x =>
    cutoff.toFun x ^ 2 * (u.toFun x - center) ^ 2
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const u.smooth.continuous).measurableSet
  have hweight_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft_int : IntegrableOn (fun x : M => r ^ 2 * cutoff.toFun x ^ 2) S μ :=
    (hweight_int.const_mul (r ^ 2)).integrableOn
  have hoscilland_int : Integrable oscilland μ := by
    exact ((cutoff.smooth.continuous.pow 2).mul
      ((u.smooth.continuous.sub continuous_const).pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : IntegrableOn oscilland S μ := hoscilland_int.integrableOn
  have hpointwise : ∀ x ∈ S,
      r ^ 2 * cutoff.toFun x ^ 2 ≤ oscilland x := by
    intro x hx
    have hdiff : r ≤ u.toFun x - center := by
      change level < u.toFun x at hx
      linarith
    have hsquare : r ^ 2 ≤ (u.toFun x - center) ^ 2 :=
      (sq_le_sq₀ hr (hr.trans hdiff)).2 hdiff
    simpa only [oscilland, mul_comm] using
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg (cutoff.toFun x))
  calc
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level =
        ∫ x in S, r ^ 2 * cutoff.toFun x ^ 2 ∂μ := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ x in S, oscilland x ∂μ :=
      setIntegral_mono_on hleft_int hright_int hS hpointwise
    _ ≤ ∫ x, oscilland x ∂μ :=
      setIntegral_le_integral hoscilland_int
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = localizedL2Deviation (I := I) (M := M) cutoff u center := by
      rfl

omit [I.Boundaryless] in
theorem localized_superlevel_chebyshev
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : localizedAverage (I := I) (M := M) cutoff u + r ≤ level) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Oscillation (I := I) (M := M) cutoff u := by
  exact localized_superlevel_chebyshev_of_center
    (I := I) (M := M) cutoff u
      (localizedAverage (I := I) (M := M) cutoff u) hr hlevel

omit [I.Boundaryless] in
theorem localized_sublevel_chebyshev_of_center
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) (center : ℝ) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ center - r) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Deviation (I := I) (M := M) cutoff u center := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let S : Set M := {x : M | u.toFun x < level}
  let oscilland : M → ℝ := fun x =>
    cutoff.toFun x ^ 2 * (u.toFun x - center) ^ 2
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hS : MeasurableSet S :=
    (isOpen_lt u.smooth.continuous continuous_const).measurableSet
  have hweight_int : Integrable (fun x : M => cutoff.toFun x ^ 2) μ :=
    (cutoff.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft_int : IntegrableOn (fun x : M => r ^ 2 * cutoff.toFun x ^ 2) S μ :=
    (hweight_int.const_mul (r ^ 2)).integrableOn
  have hoscilland_int : Integrable oscilland μ := by
    exact ((cutoff.smooth.continuous.pow 2).mul
      ((u.smooth.continuous.sub continuous_const).pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : IntegrableOn oscilland S μ := hoscilland_int.integrableOn
  have hpointwise : ∀ x ∈ S,
      r ^ 2 * cutoff.toFun x ^ 2 ≤ oscilland x := by
    intro x hx
    have hdiff : r ≤ center - u.toFun x := by
      change u.toFun x < level at hx
      linarith
    have hsquare : r ^ 2 ≤ (center - u.toFun x) ^ 2 :=
      (sq_le_sq₀ hr (hr.trans hdiff)).2 hdiff
    have hsquare' : r ^ 2 ≤ (u.toFun x - center) ^ 2 := by
      nlinarith
    simpa only [oscilland, mul_comm] using
      mul_le_mul_of_nonneg_right hsquare' (sq_nonneg (cutoff.toFun x))
  calc
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level =
        ∫ x in S, r ^ 2 * cutoff.toFun x ^ 2 ∂μ := by
      rw [integral_const_mul]
      rfl
    _ ≤ ∫ x in S, oscilland x ∂μ :=
      setIntegral_mono_on hleft_int hright_int hS hpointwise
    _ ≤ ∫ x, oscilland x ∂μ :=
      setIntegral_le_integral hoscilland_int
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = localizedL2Deviation (I := I) (M := M) cutoff u center := by
      rfl

omit [I.Boundaryless] in
theorem localized_sublevel_chebyshev
    {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) {r level : ℝ}
    (hr : 0 ≤ r)
    (hlevel : level ≤ localizedAverage (I := I) (M := M) cutoff u - r) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) cutoff u level ≤
      localizedL2Oscillation (I := I) (M := M) cutoff u := by
  exact localized_sublevel_chebyshev_of_center
    (I := I) (M := M) cutoff u
      (localizedAverage (I := I) (M := M) cutoff u) hr hlevel

def shiftedLogMass
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) : ℝ :=
  localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
        (contMDiff_log_of_pos hu hpos) t) +
    t * (2 * cutoffDirichletEnergy (I := I) (M := M) cutoff)

def shiftedLogCenter
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) : ℝ :=
  shiftedLogMass (I := I) (M := M) g cutoff u hu hpos t /
    cutoffMass (I := I) (M := M) cutoff

def logCenterDrift
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g) : ℝ :=
  2 * cutoffDirichletEnergy (I := I) (M := M) cutoff /
    cutoffMass (I := I) (M := M) cutoff

omit [I.Boundaryless] [CompactSpace M] in
theorem shifted_log_center_eq
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (t : ℝ) :
    shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos t =
      localizedAverage (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) +
        t * logCenterDrift (I := I) (M := M) g cutoff := by
  unfold shiftedLogCenter shiftedLogMass localizedAverage logCenterDrift
  ring

omit [I.Boundaryless] in
theorem contDiff_shiftedLogCenter
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) :
    ContDiff ℝ ∞
      (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun t =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hshifted_smooth : ContDiff ℝ ∞ (fun t => mass t + t * source) :=
    hmass_smooth.add (contDiff_id.mul contDiff_const)
  simpa only [shiftedLogCenter, shiftedLogMass, mass, source] using
    hshifted_smooth.div_const (cutoffMass (I := I) (M := M) cutoff)

theorem integral_deriv_div_center_gap_sq
    (center : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 1 center)
    {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hmono : MonotoneOn center (Icc a b)) :
    (∫ t in a..b,
        deriv center t / (center b - center t + r) ^ 2) =
      1 / r - 1 / (center b - center a + r) := by
  let gap : ℝ → ℝ := fun t => center b - center t + r
  let reciprocal : ℝ → ℝ := fun t => 1 / gap t
  have hgap_pos : ∀ t ∈ Icc a b, 0 < gap t := by
    intro t ht
    have hle := hmono ht ⟨hab, le_rfl⟩ ht.2
    dsimp only [gap]
    linarith
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt reciprocal (deriv center t / gap t ^ 2) t := by
    intro t ht
    have hcenter_deriv : HasDerivAt center (deriv center t) t :=
      (hsmooth.differentiable (by norm_num) t).hasDerivAt
    have hgap_deriv : HasDerivAt gap (-deriv center t) t := by
      simpa only [gap, Pi.sub_apply, Pi.add_apply, zero_sub] using
        ((hasDerivAt_const t (center b)).sub hcenter_deriv).add_const r
    have hinv := hgap_deriv.inv (hgap_pos t ht).ne'
    simpa only [reciprocal, one_div, neg_neg] using hinv
  have hderiv_cont : ContinuousOn
      (fun t => deriv center t / gap t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hsmooth.continuous_deriv (by norm_num)).continuousOn.div
      (((continuous_const.sub hsmooth.continuous).add continuous_const).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hgap_pos t ht).ne')
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa [uIcc_of_le hab] using ht))
    hderiv_cont.intervalIntegrable
  simpa only [reciprocal, gap, sub_self, zero_add] using hintegral

theorem shifted_log_mass_monotone_on
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ}
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    MonotoneOn (shiftedLogMass (I := I) (M := M) g cutoff u hu hpos)
      (Icc a b) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun t =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  let shifted : ℝ → ℝ := fun t => mass t + t * source
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hshifted_smooth : ContDiff ℝ ∞ shifted :=
    hmass_smooth.add (contDiff_id.mul contDiff_const)
  have hmono : MonotoneOn shifted (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      hshifted_smooth.continuous.continuousOn
      (hshifted_smooth.differentiable (by simp)).differentiableOn
    intro t ht
    have ht' : t ∈ Icc a b := interior_subset ht
    have hdiff := log_energy_differential_of_supersolution
      (I := I) (M := M) g cutoff u hu hpos t (hpde t ht')
    have henergy := localizedDirichletEnergy_nonneg
      (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t)
    have hmass_deriv : HasDerivAt mass (deriv mass t) t :=
      (hmass_smooth.differentiable (by simp) t).hasDerivAt
    have hshifted_deriv : HasDerivAt shifted (deriv mass t + source) t := by
      simpa only [one_mul, id_eq] using
        hmass_deriv.add ((hasDerivAt_id t).mul_const source)
    rw [hshifted_deriv.deriv]
    change (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
      deriv mass t + source at hdiff
    linarith
  simpa only [shiftedLogMass, hlog, mass, source, shifted] using hmono

theorem shifted_log_center_monotone_on
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a b : ℝ}
    (hmass : 0 < cutoffMass (I := I) (M := M) cutoff)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    MonotoneOn (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos)
      (Icc a b) := by
  have hmono := shifted_log_mass_monotone_on
    (I := I) (M := M) g cutoff u hu hpos hpde
  intro s hs t ht hst
  exact (div_le_div_iff_of_pos_right hmass).2 (hmono hs ht hst)

theorem half_localized_dirichlet_energy_le_shifted_log_center_deriv
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    (hmass : 0 < cutoffMass (I := I) (M := M) cutoff)
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t) :
    (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x))
            (contMDiff_log_of_pos hu hpos) t) ≤
      cutoffMass (I := I) (M := M) cutoff *
        deriv (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos) t := by
  let hlog := contMDiff_log_of_pos hu hpos
  let mass : ℝ → ℝ := fun s =>
    localizedIntegral (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s)
  let source := 2 * cutoffDirichletEnergy (I := I) (M := M) cutoff
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using contDiff_localizedIntegral
      (I := I) (M := M) cutoff (fun s x => Real.log (u s x)) hlog
  have hmass_deriv : HasDerivAt mass (deriv mass t) t :=
    (hmass_smooth.differentiable (by simp) t).hasDerivAt
  have hshifted_deriv :
      HasDerivAt (fun s => mass s + s * source) (deriv mass t + source) t := by
    simpa only [one_mul, id_eq] using
      hmass_deriv.add ((hasDerivAt_id t).mul_const source)
  have hcenter_deriv :
      HasDerivAt (shiftedLogCenter (I := I) (M := M) g cutoff u hu hpos)
        ((deriv mass t + source) /
          cutoffMass (I := I) (M := M) cutoff) t := by
    simpa only [shiftedLogCenter, shiftedLogMass, mass, source] using
      hshifted_deriv.div_const (cutoffMass (I := I) (M := M) cutoff)
  have hdiff := log_energy_differential_of_supersolution
    (I := I) (M := M) g cutoff u hu hpos t hpde
  change (1 / 2 : ℝ) *
      localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
    deriv mass t + source at hdiff
  rw [hcenter_deriv.deriv]
  calc
    (1 / 2 : ℝ) *
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => Real.log (u s x)) hlog t) ≤
      deriv mass t + source := hdiff
    _ = cutoffMass (I := I) (M := M) cutoff *
        ((deriv mass t + source) /
          cutoffMass (I := I) (M := M) cutoff) := by
      field_simp [hmass.ne']

theorem early_log_superlevel_tail_with_center_gap_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ s r : ℝ}
    (haτ : a ≤ τ)
    (hs : s ∈ Icc a τ)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s + r) ^ 2 *
        localizedSuperlevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff + r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center := localizedAverage (I := I) (M := M) averagingCutoff w
  let gap := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s + r
  let level := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff + r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : center + gap ≤ level := by
    dsimp only [center, gap, level, w, hlog]
    rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
      u hu hpos s]
    ring_nf
    exact le_rfl
  exact (localized_superlevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hgap hlevel).trans (hP w)

theorem late_log_sublevel_tail_with_center_gap_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b s r : ℝ}
    (hτb : τ ≤ b)
    (hs : s ∈ Icc τ b)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s -
          shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ + r) ^ 2 *
        localizedSublevelMass (I := I) (M := M) deviationCutoff
          (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
            (contMDiff_log_of_pos hu hpos) s)
          (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
            s * logCenterDrift (I := I) (M := M) g averagingCutoff - r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center := localizedAverage (I := I) (M := M) averagingCutoff w
  let gap := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos s -
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ + r
  let level := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
    s * logCenterDrift (I := I) (M := M) g averagingCutoff - r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  have hgap : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have hlevel : level ≤ center - gap := by
    dsimp only [center, gap, level, w, hlog]
    rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
      u hu hpos s]
    ring_nf
    exact le_rfl
  exact (localized_sublevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hgap hlevel).trans (hP w)

theorem early_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ s r : ℝ}
    (haτ : a ≤ τ)
    (hs : s ∈ Icc a τ)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    r ^ 2 * localizedSuperlevelMass (I := I) (M := M) deviationCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          s * logCenterDrift (I := I) (M := M) g averagingCutoff + r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center :=
    localizedAverage (I := I) (M := M) averagingCutoff w
  let level :=
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
      s * logCenterDrift (I := I) (M := M) g averagingCutoff + r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono hs ⟨haτ, le_rfl⟩ hs.2
  rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
    u hu hpos s] at hcenter_mono
  have hlevel : center + r ≤ level := by
    dsimp only [center, level, w, hlog]
    linarith
  exact (localized_superlevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hr hlevel).trans (hP w)

theorem late_log_sublevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b s r : ℝ}
    (hτb : τ ≤ b)
    (hs : s ∈ Icc τ b)
    (hr : 0 ≤ r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    r ^ 2 * localizedSublevelMass (I := I) (M := M) deviationCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
          s * logCenterDrift (I := I) (M := M) g averagingCutoff - r) ≤
      C * localizedDirichletEnergy (I := I) (M := M) averagingCutoff
        (smoothScalarSlice (I := I) g (fun q x => Real.log (u q x))
          (contMDiff_log_of_pos hu hpos) s) := by
  let hlog := contMDiff_log_of_pos hu hpos
  let w := smoothScalarSlice (I := I) g (fun q x => Real.log (u q x)) hlog s
  let center :=
    localizedAverage (I := I) (M := M) averagingCutoff w
  let level :=
    shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ -
      s * logCenterDrift (I := I) (M := M) g averagingCutoff - r
  have hmono := shifted_log_center_monotone_on
    (I := I) (M := M) g averagingCutoff u hu hpos hmass hpde
  have hcenter_mono := hmono ⟨le_rfl, hτb⟩ hs hs.1
  rw [shifted_log_center_eq (I := I) (M := M) g averagingCutoff
    u hu hpos s] at hcenter_mono
  have hlevel : level ≤ center - r := by
    dsimp only [center, level, w, hlog]
    linarith
  exact (localized_sublevel_chebyshev_of_center
    (I := I) (M := M) deviationCutoff w center hr hlevel).trans (hP w)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
