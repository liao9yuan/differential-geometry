import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Analysis.Parabolic.Moser.Sobolev
import DifferentialGeometry.Geometry.Operator.LaplacianBridge


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

def rpowSource (q : ℝ) (u source : ℝ → M → ℝ) : ℝ → M → ℝ :=
  fun t x => q * u t x ^ (q - 1) * source t x

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_rpow_of_pos
    {u : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) (q : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2 ^ q) := by
  intro p
  simpa only [Function.comp_apply] using
    (Real.contDiffAt_rpow_const_of_ne (p := q) (hpos p.1 p.2).ne').comp_contMDiffAt
      (x := p) (hu p)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_rpowSource_of_pos
    {u source : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) (q : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rpowSource q u source p.1 p.2) := by
  exact (contMDiff_const.mul (contMDiff_rpow_of_pos hu hpos (q - 1))).mul hsource

theorem rpow_subsolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} {x : M}
    (hpde :
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x) :
    deriv (fun s => u s x ^ q) t ≤
      Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun t x => u t x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t).smooth x +
        rpowSource q u source t x := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let huq := contMDiff_rpow_of_pos hu hpos q
  let uqt := smoothScalarSlice (I := I) g (fun s y => u s y ^ q) huq t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => u s x ^ q) t =
        q * u t x ^ (q - 1) * deriv (fun s => u s x) t := by
    have h := ((htime.differentiable (by norm_num) t).hasDerivAt.rpow_const (p := q)
      (Or.inl (hpos t x).ne')).deriv
    rw [h]
    ring
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.smooth).mdifferentiable x
  have hlap_raw := laplacian_rpow (I := I)
    (LeviCivita (I := I) g) g q
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g uqt.smooth x =
        (q * u t x ^ (q - 1)) * Δ_g (I := I) g ut.smooth x +
          (q * (q - 1) * u t x ^ (q - 2)) *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    rw [← laplacian_levi_eq (I := I) g uqt.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, uqt, smoothScalarSlice_toFun] using hlap_raw
  have hcoeff : 0 ≤ q * u t x ^ (q - 1) :=
    mul_nonneg (zero_le_one.trans hq) (Real.rpow_nonneg (hpos t x).le _)
  have hgradient :
      0 ≤ (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (zero_le_one.trans hq) (sub_nonneg.mpr hq))
        (Real.rpow_nonneg (hpos t x).le _))
      (metric_inner_self_nonneg (I := I) (M := M) g x _)
  rw [htime_deriv, hlap]
  change q * u t x ^ (q - 1) * deriv (fun s => u s x) t ≤
    q * u t x ^ (q - 1) * Δ_g (I := I) g ut.smooth x +
      (q * (q - 1) * u t x ^ (q - 2)) *
        g.inner x
          (gradientFun (I := I) g ut.toFun x)
          (gradientFun (I := I) g ut.toFun x) +
      q * u t x ^ (q - 1) * source t x
  have hmul := mul_le_mul_of_nonneg_left hpde hcoeff
  nlinarith

variable [SigmaCompactSpace M] [CompactSpace M]

theorem caccioppoli_rpow_of_subsolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
          (contMDiff_rpow_of_pos hu hpos q) t)) (Icc a b))
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x ^ q *
                  rpowSource q u source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let hsourceq := contMDiff_rpowSource_of_pos hu hsource hpos q
  apply caccioppoli_of_subsolution
    (I := I) (M := M) cutoff (fun t x => u t x ^ q)
      (rpowSource q u source) huq hsourceq hab hdweight hweight hweight_nonneg
  · simpa only [huq] using hdirichlet
  · intro t _ x
    exact (Real.rpow_pos_of_pos (hpos t x) q).le
  · intro t ht x
    exact rpow_subsolution (I := I) (M := M) g u source hu hpos hq (hpde t ht x)

theorem rpow_moser_step
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (cutoff outer : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {q : ℝ} (hq : 1 ≤ q)
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A K L : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
          (contMDiff_rpow_of_pos hu hpos q) t)) (Icc a t₁))
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
              (contMDiff_rpow_of_pos hu hpos q) s) +
          weight s *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g (fun r x => u r x ^ q)
                  (contMDiff_rpow_of_pos hu hpos q) s) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u s x ^ q *
                  rpowSource q u source s x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g))) ≤ A)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (houterMass_le :
      (∫ t in t₀..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ q)
            (contMDiff_rpow_of_pos hu hpos q) t)) ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ t in t₀..t₁, ∫ x,
          |cutoff.toFun x * u t x ^ q| ^
            (2 + 4 / (Module.finrank ℝ E : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        C * (((t₁ - t₀ + 1) * A + K * L) ^
          (1 + 2 / (Module.finrank ℝ E : ℝ))) := by
  let huq := contMDiff_rpow_of_pos hu hpos q
  let sourceq := rpowSource q u source
  have hsourceq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => sourceq p.1 p.2) := by
    simpa only [sourceq] using contMDiff_rpowSource_of_pos hu hsource hpos q
  have hpdeq : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x ^ q) t ≤
        Δ_g (I := I) g
            (smoothScalarSlice (I := I) g (fun s x => u s x ^ q) huq t).smooth x +
          sourceq t x := by
    intro t ht x
    simpa only [huq, sourceq] using
      rpow_subsolution (I := I) (M := M) g u source hu hpos hq (hpde t ht x)
  have henergy := caccioppoli_inner_energy_of_subsolution
    (I := I) (M := M) cutoff (fun t x => u t x ^ q) sourceq huq hsourceq
    hat₀ ht₀t₁ hdweight hweight hweight_nonneg hweight_a hweight_inner
    (by simpa only [huq] using hdirichlet)
    (fun t _ x => (Real.rpow_pos_of_pos (hpos t x) q).le)
    hpdeq
    (by simpa only [huq, sourceq] using hrhs_le)
  apply localized_parabolic_sobolev_of_nested_cutoffs
    (I := I) (M := M) g hdim cutoff outer (fun t x => u t x ^ q) huq
    ht₀t₁ hA hK henergy.1
  · exact hdirichlet.mono (fun t ht => ⟨hat₀.trans ht.1, ht.2⟩)
  · exact henergy.2
  · exact hgrad
  · simpa only [huq] using houterMass_le

end DifferentialGeometry.Analysis.Parabolic.Moser

end
