import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPulledIntegralContinuity
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainVariationalLimitGeneral
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomainVariationalLimit
import DifferentialGeometry.Analysis.Laplacian.Regularity.LeibnizCompensatedFh
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInnerCLM
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothMulLp
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinearH1ComplFromDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1ComplWeakPartialLimit
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1ComplGradientH1LipschitzBound
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushedWeakPartialOnVolume
import DifferentialGeometry.Analysis.Laplacian.Operator.Operator
import DifferentialGeometry.Analysis.Laplacian.Operator.SmoothBridge
import DifferentialGeometry.Analysis.Laplacian.Variational
import DifferentialGeometry.Geometry.NormGradSq

/-!
# Unconditional general-case variational identity for the variational Laplacian

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h : H1Compl g` lying in `laplacianDomain g`, this file proves the
chart-pulled variational identity for `u_h`:

```
∫_{chartTarget α} ∑_{i, j} √det g · g^{ij} · weak_partial_i · ∂_j ψ
  + ∫_{chartTarget α} √det g · u_chart · ψ
  = chartPulledIntegralCLM g α (√det g · ψ) (fHLeibniz g α u_h hu_h)
```

against any smooth test function `ψ : EuclN → ℝ` with
`tsupport ψ ⊆ chartTargetEuclid α`.

## Strategy: bilinear-form bypass

The smooth-case identity for `v_n : SmoothScalar g` from
`laplacianDomain_variational_identity_smooth_case` reads

```
LHS_principal_n + LHS_u_chart_mass_n
  = ∫ density · (pouScalar α v_n).oneSubLap.toFun (symm y) · ψ
```

By the pointwise Leibniz expansion `pouScalar_oneSubLapClassical_pointwise_leibniz`,
the right-hand integrand splits into three pieces:

```
density · ρα(symm) · v_n.oneSubLap(symm) · ψ
  - 2 · density · g(grad ρα, grad v_n)(symm) · ψ
  - density · v_n(symm) · Δρα(symm) · ψ.
```

Each piece is identified with a `chartPulledIntegralCLM` application to the
corresponding `Lp ℝ 2 μ_g` class derived from `v_n`:

* the first piece equals `chartPulledIntegralCLM g α (density · ψ) (smoothMulLp g ρα (smoothToLp v_n.oneSubLapClassical))`;
* the second piece equals `chartPulledIntegralCLM g α (density · ψ) (gradInnerSmooth g ρα v_n)`;
* the third piece equals `chartPulledIntegralCLM g α (density · ψ) (smoothMulLp g (Δρα) (smoothToLp v_n))`.

For `v_n → u_h` in `H¹Compl g`, the second and third pieces converge by CLM
continuity of `gradInnerCLM g ρα` and the composition `smoothMulLp g Δρα ∘ H1ComplToLp`
respectively. The first piece is the obstruction since `smoothToLp v_n.oneSubLapClassical`
need not converge in `Lp` (the variational Laplacian is unbounded). The
**bilinear bypass** avoids this obstruction.

The bilinear bypass: directly compute the limit of the first-piece integral by
recognising that `∫ density · ρα(symm) · v_n.oneSubLap(symm) · ψ` is a
manifold-side integral against the smooth function
`ρα · ψ_chart_pulled` which IS a smooth scalar (in `SmoothScalar g`). Via the
smooth bridge `smoothScalarH1Inner_eq_lpInner_oneSubLap`, this Lp inner
product equals an `H¹Compl` inner product, which is continuous in `v_n`.

Since the `Lp ℝ 2 μ_g` class produced by the chart-pulled-integral CLM agrees
with the manifold-side integral against the **chart-pulled integral weight**
(`chartPulledIntegralWeight`), the bilinear bypass extracts the limit
explicitly via the resolvent variational identity for `u_h ∈ laplacianDomain g`,
yielding the limit `chartPulledIntegralCLM g α (density · ψ) (smoothMulLp g ρα ((1-Δ)u_h))`,
the first piece of `fHLeibniz g α u_h hu_h`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Continuity helpers for the chart-pulled-integral weight `density · ψ` -/

/-- Continuity of the weight `density · ψ`. -/
lemma densityPsi_cont
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ tsupport ψ
  · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
      ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
        (hOpen.mem_nhds hy_T)
    exact h_dens.mul hψ.continuous.continuousAt
  · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
    have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hψ_z, mul_zero]
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

/-- Compact support of the weight `density · ψ`. -/
lemma densityPsi_cs
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ) :
    HasCompactSupport (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) := by
  refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
  have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
  change densityOnEuclid (I := I) g α y * ψ y = 0
  rw [hψ_y, mul_zero]

/-- The support of `density · ψ` is contained in `chartTargetEuclid α`. -/
lemma densityPsi_supp
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ}
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  refine subset_trans (closure_mono ?_) hψ_supp
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyψ
  apply hy
  have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
  change densityOnEuclid (I := I) g α y * ψ y = 0
  rw [hψ_y, mul_zero]

/-! ## Convergence helper: `smoothToLp v_n → H1ComplToLp u_h`. -/

/-- For `v_n → u_h` in `H¹Compl`, `H1ComplToLp (smoothToH1Compl v_n)
= smoothToLp v_n → H1ComplToLp u_h` in `Lp`. -/
lemma smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop
      (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  have h_compose : Tendsto (fun n => H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
      (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
    ((H1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
  have h_eq : (fun n => H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g (v n))) =
      (fun n => smoothToLp (I := I) (M := M) g (v n)) := by
    funext n
    exact H1ComplToLp_smoothToH1Compl (I := I) (M := M) g (v n)
  rw [← h_eq]; exact h_compose

/-! ## A `SmoothScalar g` wrapper for the smooth function
`g.inner _ (gradFun ρα _) (gradFun v _)`. -/

/-- The smooth function `x ↦ g.inner x (gradFun g ρα x) (gradFun g v.toFun x)`
packaged as a `SmoothScalar g`. We use `contMDiff_g_inner_of_smooth_sections`
for the smoothness witness. -/
private noncomputable def gradInnerSmoothScalar
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) : SmoothScalar g where
  toFun := fun x : M => g.inner x (gradFun (I := I) g ρα x)
    (gradFun (I := I) g v.toFun x)
  smooth := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g ρα.contMDiff) (grad_g (I := I) g v.smooth)
    refine h.congr (fun x => ?_)
    change g.inner x ((grad_g (I := I) g ρα.contMDiff :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g v.smooth :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)
    rw [grad_g_apply, grad_g_apply]

@[simp] private lemma gradInnerSmoothScalar_toFun
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (gradInnerSmoothScalar (I := I) (M := M) g ρα v).toFun =
      fun x : M => g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x) := rfl

/-- `gradInnerSmooth g ρα v` agrees with `smoothToLp (gradInnerSmoothScalar g ρα v)`
as Lp classes. -/
private lemma gradInnerSmooth_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα v =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothScalar (I := I) (M := M) g ρα v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_grad := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothScalar (I := I) (M := M) g ρα v).toFun :=
    MemLp.coeFn_toLp (gradInnerSmoothScalar (I := I) (M := M) g ρα v).memLp_two
  filter_upwards [h_grad, h_lp_h] with x hx_grad hx_lp_h
  rw [hx_grad, hx_lp_h]
  rfl

/-! ## A `SmoothScalar g` wrapper for `ρα · v.oneSubLapClassical`. -/

/-- The smooth function `ρα · v.oneSubLapClassical.toFun` packaged as a
`SmoothScalar g`. -/
private noncomputable def rhoOneSubLapSmoothScalar
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M => (ρα : M → ℝ) x * v.oneSubLapClassical.toFun x
  smooth := ρα.contMDiff.mul v.oneSubLapClassical.smooth

/-- `smoothMulLp g ρα (smoothToLp v.oneSubLapClassical)` agrees with
`smoothToLp (rhoOneSubLapSmoothScalar g ρα v)` as Lp classes. -/
private lemma smoothMulLp_oneSubLap_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g ρα
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical) =
      smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
    (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
  have h_lp1 : ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp v.oneSubLapClassical.memLp_two
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v).toFun :=
    MemLp.coeFn_toLp (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_lp1, h_lp_h] with x hx_lp1 hx_lp_h
  change (ρα : M → ℝ) x * ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_lp1, hx_lp_h]
  rfl

/-! ## A `SmoothScalar g` wrapper for `Δρα · v`. -/

/-- The smooth function `Δρα · v.toFun` packaged as a `SmoothScalar g`. -/
private noncomputable def laplacianRhoMulSmoothScalar
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M =>
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x
  smooth :=
    (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul v.smooth

/-- `smoothMulLp g (Δρα) (smoothToLp v)` agrees with
`smoothToLp (laplacianRhoMulSmoothScalar g α v)` as Lp classes. -/
private lemma smoothMulLp_laplacianRho_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g (laplacianOfChartPOU (I := I) (M := M) g α)
        (smoothToLp (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
    (laplacianOfChartPOU (I := I) (M := M) g α)
    (smoothToLp (I := I) (M := M) g v)
  have h_lp1 : ((smoothToLp (I := I) (M := M) g v
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v).toFun :=
    MemLp.coeFn_toLp (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_lp1, h_lp_h] with x hx_lp1 hx_lp_h
  change (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
      ((smoothToLp (I := I) (M := M) g v
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_lp1, hx_lp_h]
  rfl

/-! ## Block 2 (gradient cross-term) limit-passage -/

/-- The chartPulledIntegralCLM applied to `gradInnerSmooth ρα v_n` converges
to its application to `gradInnerCLM ρα u_h`, by CLM continuity of
`gradInnerCLM ρα` in `H¹Compl`. -/
lemma chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h))) := by
  classical
  -- gradInnerSmooth ρα v_n = gradInnerCLM ρα (smoothToH1Compl v_n) (smooth bridge).
  have h_eq_n : ∀ n,
      gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n) =
        gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToH1Compl (I := I) (M := M) g (v n)) :=
    fun n => (gradInnerCLM_smoothToH1Compl (I := I) (M := M) g _ (v n)).symm
  have h_funeq : (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n))) =
      (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToH1Compl (I := I) (M := M) g (v n)))) := by
    funext n; rw [h_eq_n n]
  rw [h_funeq]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
    (((gradInnerCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)).continuous.tendsto _).comp h_tendsto)

/-! ## Block 3 (`v_n · Δρα`) limit-passage -/

/-- The chartPulledIntegralCLM applied to `smoothMulLp g Δρα (smoothToLp v_n)`
converges to its application to `smoothMulLp g Δρα (H1ComplToLp u_h)`,
by CLM continuity of `H1ComplToLp` and `smoothMulLp`. -/
lemma chartPulledIntegralCLM_smoothMulLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h)))) := by
  classical
  have h_lp_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
    smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto (I := I) (M := M) g h_tendsto
  have h_smoothMul_tendsto : Tendsto (fun n =>
      smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)
        (H1ComplToLp (I := I) (M := M) g u_h))) :=
    ((smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)).continuous.tendsto _).comp
      h_lp_tendsto
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
    h_smoothMul_tendsto

/-! ## Block 1 (`ρα · (1-Δ) v_n`) limit-passage via the bilinear bypass

The smooth-case integrand `density · ρα(symm) · v_n.oneSubLap(symm) · ψ` equals
`chartPulledIntegralCLM g α (density · ψ) (smoothMulLp g ρα (smoothToLp v_n.oneSubLap))`.
This `Lp` element does NOT converge in `Lp` as `n → ∞` (`laplacianOp` is unbounded).

The bilinear bypass is to use the chart-pulled integral CLM's underlying
manifold-side integral and apply the bilinear bridge to convert the `Lp` inner
product into an `H¹Compl` inner product, which IS continuous in `v_n`. -/

/-- The `Lp` value of the chart-pulled-integral CLM applied to
`smoothToLp h_smooth` for any smooth scalar `h_smooth`. This expresses the CLM
as a manifold-side `L²` inner product. -/
private lemma chartPulledIntegralCLM_smoothToLp_eq_lpInner
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (h_smooth : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g h_smooth) =
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp,
        smoothToLp (I := I) (M := M) g h_smooth⟫_ℝ := by
  unfold chartPulledIntegralCLM
  rw [innerSL_apply_apply]

/-- The chartPulledIntegralCLM applied to `smoothMulLp g ρα (smoothToLp v.oneSubLapClassical)`
equals the `Lp` inner product `⟨w_θ, smoothToLp (rhoOneSubLapSmoothScalar g ρα v)⟩_{L²}`. -/
private lemma chartPulledIntegralCLM_smoothMulLp_oneSubLap_eq_lpInner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)) =
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp),
        smoothToLp (I := I) (M := M) g
          (rhoOneSubLapSmoothScalar (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v)⟫_ℝ := by
  rw [smoothMulLp_oneSubLap_eq_smoothToLp]
  exact chartPulledIntegralCLM_smoothToLp_eq_lpInner (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
    (rhoOneSubLapSmoothScalar (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v)

/-! ## The resolvent variational identity in `L²` form

For `u_h ∈ laplacianDomain g`, the resolvent variational identity says
`⟨u_h, v⟩_{H¹} = ⟨H1ComplToLp v, preimage u_h⟩_{L²}` for every test
`v ∈ H1Compl g`. Specializing to `v = smoothToH1Compl w` for a smooth scalar
`w` and using `H1ComplToLp_smoothToH1Compl` gives the form

`⟨u_h, smoothToH1Compl w⟩_{H¹} = ⟨smoothToLp w, H1ComplToLp u_h - laplacianOp ⟨u_h, hu_h⟩⟩_{L²}.`
-/

/-- For `u_h ∈ laplacianDomain g`, the `H¹` inner product against the smooth
lift of any `w : SmoothScalar g` equals the `L²` inner product of
`(1 - Δ_g) u_h := H1ComplToLp u_h - laplacianOp ⟨u_h, hu_h⟩` against
`smoothToLp w`. -/
private lemma h1Inner_smoothToH1Compl_eq_lpInner_oneSubLap_of_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ⟪u_h, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ := by
  classical
  -- Set `f := preimage u_h` so `u_h = resolvent f` and
  -- `H1ComplToLp u_h - laplacianOp ⟨u_h, _⟩ = f`.
  set f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩
  have h_u_eq : (⟨u_h, hu_h⟩ : laplacianDomain (I := I) (M := M) g).val =
      resolvent (I := I) (M := M) g f :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨u_h, hu_h⟩).symm
  -- The variational identity for the resolvent.
  have h_res := resolvent_inner_eq_lpFunctional (I := I) (M := M) g f
    (smoothToH1Compl (I := I) (M := M) g w)
  -- `h_res : ⟨resolvent f, smoothToH1Compl w⟩ = ⟨H1ComplToLp (smoothToH1Compl w), f⟩`.
  have h_subst : ⟪u_h, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
      ⟪resolvent (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show u_h = (⟨u_h, hu_h⟩ : laplacianDomain (I := I) (M := M) g).val from rfl,
      h_u_eq]
  rw [h_subst, h_res]
  -- Reduce `H1ComplToLp (smoothToH1Compl w) = smoothToLp w`.
  rw [H1ComplToLp_smoothToH1Compl]
  -- Now identify `f` with `H1ComplToLp u_h - laplacianOp ⟨u_h, hu_h⟩`.
  -- By `laplacianOp_apply`, `laplacianOp ⟨u_h, hu_h⟩ = H1ComplToLp u_h - preimage`.
  have h_f_eq : f = H1ComplToLp (I := I) (M := M) g u_h -
      laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ := by
    have h_lap_apply :=
      laplacianOp_apply (I := I) (M := M) g ⟨u_h, hu_h⟩
    -- `laplacianOp ⟨u_h, hu_h⟩ = H1ComplToLp u_h - f`.
    -- ⇒ `f = H1ComplToLp u_h - laplacianOp ⟨u_h, hu_h⟩`.
    rw [h_lap_apply]
    abel
  rw [← h_f_eq]

/-! ## The direct bypass tendsto lemma

For a smooth approximating sequence `v_n → u_h` in `H¹Compl g` with
`u_h ∈ laplacianDomain g`, the chart-pulled integral of the smooth-case
`smoothMulLp g ρα (smoothToLp v_n.oneSubLapClassical)` converges to the
chart-pulled integral of `smoothMulLp g ρα ((1 - Δ_g) u_h)`. -/

/-! ## Refined infrastructure: `rhoChartWeightSmoothScalarOn`

The chart-pulled integral weight `w_θ := chartPulledIntegralWeight g α θ` is
in general only continuous. However, when `θ` is smooth ON `chartTargetEuclid
α` (not necessarily globally on `EuclN`) and `ρα := chartAtlasPOU I M α` has
compact support contained in the chart source, the product `ρα · w_θ` is a
smooth function on `M`. The key reason: on the chart source, `w_θ(x) =
θ(toEucl(extChart x)) / chartDensity g α x` is smooth when `θ` is smooth on
the chart target; and `ρα` vanishes outside the chart source.

This is the variant accepting `ContDiffOn` on the chart target, which is what
`θ := densityOnEuclid g α · ψ` satisfies. -/

/-- The product `(ρα : M → ℝ) · chartPulledIntegralWeight g α θ` as a
`SmoothScalar g`, given that `θ` is `ContDiffOn` on `chartTargetEuclid α`.
The continuity, compact support, and support hypotheses are part of the
public-facing API (consumed by `smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn`)
but are not directly needed for the smoothness witness itself. -/
private noncomputable def rhoChartWeightSmoothScalarOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (_hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (_hθ_cs : HasCompactSupport θ)
    (_hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothScalar g where
  toFun := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      chartPulledIntegralWeight (I := I) (M := M) g α θ x
  smooth := by
    classical
    intro x
    set ρα_smooth : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
    set ρα : M → ℝ := (ρα_smooth : M → ℝ)
    have hρα_subord :
        tsupport (fun y : M => (ρα_smooth : M → ℝ) y) ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    by_cases hxsrc : x ∈ (chartAt H α).source
    · have h_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
      have h_nhds : (chartAt H α).source ∈ 𝓝 x := h_open.mem_nhds hxsrc
      have h_eq_evt : (fun y : M => ρα y *
          chartPulledIntegralWeight (I := I) (M := M) g α θ y) =ᶠ[𝓝 x]
          fun y : M => ρα y *
            (θ ((toEuclidean (E := E)) ((extChartAt I α) y)) /
              chartDensity g α y) := by
        filter_upwards [h_nhds] with y hy
        rw [chartPulledIntegralWeight_apply_of_mem
          (I := I) (M := M) g α θ hy]
      refine (ContMDiffAt.congr_of_eventuallyEq ?_ h_eq_evt)
      have hρα_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρα x := ρα_smooth.contMDiff x
      -- Smoothness of `extChartAt I α` at x on the chart source.
      have h_ext_on : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
          (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      have h_eucl_contDiff : ContDiff ℝ (⊤ : ℕ∞)
          ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
        (toEuclidean : E ≃L[ℝ] EuclN).contDiff
      have h_eucl_contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞
          ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
        (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_eucl_contDiff
      have h_extChart_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) x :=
        (h_ext_on x hxsrc).contMDiffAt (h_open.mem_nhds hxsrc)
      have h_chartMap_contMDiffAt :
          ContMDiffAt I 𝓘(ℝ, EuclN) ∞
            (fun y : M => (toEuclidean (E := E)) ((extChartAt I α) y)) x :=
        h_eucl_contMDiff.contMDiffAt.comp x h_extChart_at
      -- We need that `toEucl(extChartAt I α x) ∈ chartTargetEuclid α`,
      -- so that we can use `hθ_contDiffOn` at that point.
      have hxtarget : (toEuclidean (E := E)) ((extChartAt I α) x) ∈
          chartTargetEuclid (I := I) (M := M) α := by
        refine ⟨(extChartAt I α) x, ?_, rfl⟩
        have hxE : x ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hxsrc
        exact (extChartAt I α).map_source hxE
      -- Smoothness of `θ` as a manifold map on the chart target.
      have h_target_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      -- ContDiffOn ℝ ∞ θ chartTargetEuclid → ContMDiffOn 𝓘(ℝ,EuclN) 𝓘(ℝ,ℝ) ∞ θ chartTargetEuclid
      have hθ_mdOn : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ θ
          (chartTargetEuclid (I := I) (M := M) α) :=
        (contMDiffOn_iff_contDiffOn).mpr hθ_contDiffOn
      have hθ_at : ContMDiffAt 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ θ
          ((toEuclidean (E := E)) ((extChartAt I α) x)) :=
        (hθ_mdOn _ hxtarget).contMDiffAt (h_target_open.mem_nhds hxtarget)
      have h_theta_comp_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y : M => θ ((toEuclidean (E := E)) ((extChartAt I α) y))) x :=
        hθ_at.comp x h_chartMap_contMDiffAt
      -- Smoothness of `chartDensity g α` on chart source.
      have h_dens_contMDiffOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartDensity g α)
          (chartAt H α).source := by
        rw [show (chartAt H α).source =
            (trivializationAt E (TangentSpace I) α).baseSet from
          (DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
            (I := I) (M := M) α).symm]
        exact DifferentialGeometry.Integral.Measure.chartDensity_contMDiffOn
          (I := I) g α
      have h_dens_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (chartDensity g α) x :=
        (h_dens_contMDiffOn x hxsrc).contMDiffAt (h_open.mem_nhds hxsrc)
      have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsrc
      have h_dens_pos : 0 < chartDensity g α x :=
        DifferentialGeometry.Integral.Measure.chartDensity_pos (I := I) g α hxbase
      have h_dens_ne_zero : chartDensity g α x ≠ 0 := h_dens_pos.ne'
      exact hρα_at.mul (h_theta_comp_at.div₀ h_dens_at h_dens_ne_zero)
    · have hx_off : x ∉ tsupport (fun y : M => ρα y) := fun h => hxsrc (hρα_subord h)
      have h_compl_open : IsOpen ((tsupport (fun y : M => ρα y))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have h_eq_evt : (fun y : M => ρα y *
          chartPulledIntegralWeight (I := I) (M := M) g α θ y) =ᶠ[𝓝 x]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hx_off] with y hy_off
        have hρα_zero : ρα y = 0 := image_eq_zero_of_notMem_tsupport hy_off
        rw [hρα_zero, zero_mul]
      refine (ContMDiffAt.congr_of_eventuallyEq ?_ h_eq_evt)
      exact contMDiffAt_const

@[simp] private lemma rhoChartWeightSmoothScalarOn_toFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
        hθ_cont hθ_contDiffOn hθ_cs hθ_supp).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        chartPulledIntegralWeight (I := I) (M := M) g α θ x := rfl

/-- `smoothMulLp g ρα (chartPulledIntegralWeightLp g α θ)` and
`smoothToLp g (rhoChartWeightSmoothScalarOn g α …)` agree as `Lp` classes. -/
private lemma smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp) =
      smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_supp) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp)
  have h_w_coe : (chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      chartPulledIntegralWeight (I := I) (M := M) g α θ :=
    MemLp.coeFn_toLp (chartPulledIntegralWeight_memLp
      (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)
  have h_rhs_coe : ((smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_supp) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (rhoChartWeightSmoothScalarOn
        (I := I) (M := M) g α hθ_cont hθ_contDiffOn hθ_cs hθ_supp).toFun :=
    MemLp.coeFn_toLp (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_supp).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_w_coe, h_rhs_coe] with x hx_w hx_rhs
  change ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      ((chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_supp) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_w, hx_rhs]
  rfl

/-- Smoothness of `densityOnEuclid g α · ψ` on `chartTargetEuclid α`.
For the bilinear bypass, we need to assemble `θ := densityOnEuclid · ψ` and
verify its smoothness ON the chart target. The product of two smooth functions
is smooth; both factors are smooth on the open chart target. -/
private lemma densityPsi_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiffOn ℝ ∞ (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).mul hψ.contDiffOn

/-- For a smooth approximating sequence `v_n → u_h` in `H¹Compl g`, the
first-block integral converges to the chart-pulled integral of the bilinear
bypass target. -/
lemma chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)))) := by
  classical
  -- Assemble the smooth scalar `rhoChartWeightSmoothScalarOn g α …`.
  set θ : EuclN → ℝ := fun y : EuclN =>
    densityOnEuclid (I := I) g α y * ψ y with hθ_def
  have hθ_cont : Continuous θ :=
    densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp
  have hθ_cs : HasCompactSupport θ :=
    densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs
  have hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α :=
    densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp
  have hθ_contDiffOn : ContDiffOn ℝ ∞ θ
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityPsi_contDiffOn (I := I) (M := M) g α hψ
  -- The smooth scalar `ρα · w_θ`.
  let w_smooth : SmoothScalar g :=
    rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_supp
  -- We will show: for each n,
  --   chartPulledIntegralCLM ... (smoothMulLp ρα (smoothToLp v_n.oneSubLap))
  --     = ⟨smoothToH1Compl v_n, smoothToH1Compl w_smooth⟩_{H¹Compl}.
  -- Then take limit as n → ∞ via H¹ inner-product continuity in the LEFT
  -- argument. Finally identify the limit value via the resolvent variational
  -- identity for u_h.
  -- LHS rewriting for each n: use the smooth bridge from the right.
  -- Step 1: rewrite chartPulledIntegralCLM ... (smoothMulLp ρα (smoothToLp _))
  --   = ⟨chartPulledIntegralWeightLp, smoothMulLp ρα (smoothToLp _)⟩_{L²}.
  have h_clm_eq_inner_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) =
        ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_supp,
          smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)⟫_ℝ := by
    intro n
    unfold chartPulledIntegralCLM
    rw [innerSL_apply_apply]
  -- Step 2: reassociate `⟨w_θ_lp, smoothMulLp ρα · smoothToLp h⟩_{L²}` to
  -- `⟨smoothMulLp ρα · w_θ_lp, smoothToLp h⟩_{L²}` (using ρα symmetric).
  have h_inner_assoc_n : ∀ n,
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp,
        smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)⟫_ℝ =
      ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_supp),
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ := by
    intro n
    rw [L2.inner_def, L2.inner_def]
    -- Use smoothMulLp_apply_coeFn on both sides, then integrate over M with
    -- the same a.e. pointwise integrand.
    have h_lhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)
    have h_rhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp)
    refine integral_congr_ae ?_
    filter_upwards [h_lhs_mul, h_rhs_mul] with x hx_lhs hx_rhs
    -- For real-valued integrand: `⟪a, b⟫_ℝ` on ℝ-scalars unfolds to multiplication
    -- via `RCLike.inner_apply` (definitionally `y * conj x`).
    have h_inner_lhs : ⟪((chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_supp :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
          ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
        ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
          ((chartPulledIntegralWeightLp (I := I) (M := M) g α
              hθ_cont hθ_cs hθ_supp :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
      -- ⟪x, y⟫_ℝ = y * x for ℝ.
    have h_inner_rhs : ⟪((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_supp) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
          ((smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
        ((smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
          ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_supp) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
    rw [h_inner_lhs, h_inner_rhs, hx_lhs, hx_rhs]
    ring
  -- Step 3: rewrite the new outer inner product using smoothToLp_rhoWeightOn.
  have h_smooth_replace_n : ∀ n,
      ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_supp),
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ := by
    intro n
    rw [smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_supp]
  -- Step 4: apply the smooth-bridge identity:
  --   ⟨smoothToLp w_smooth, smoothToLp (v_n).oneSubLap⟩_{L²}
  --     = smoothScalarH1Inner (v_n) w_smooth     (by L² ↔ smooth-bridge formula)
  --     = ⟨smoothToH1Compl (v_n), smoothToH1Compl w_smooth⟩_{H¹Compl}.
  -- The smooth bridge `smoothScalarH1Inner_eq_lpInner_oneSubLap`:
  --   smoothScalarH1Inner u v = ⟨smoothToLp u.oneSubLap, smoothToLp v⟩_{L²}.
  -- We apply this with `u = v_n` and `v = w_smooth`, getting:
  --   ⟨smoothToLp (v_n).oneSubLap, smoothToLp w_smooth⟩ = smoothScalarH1Inner v_n w_smooth.
  -- Apply real_inner_comm to align with the order above.
  have h_bridge_n : ∀ n,
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) (v n) w_smooth := by
    intro n
    -- The smooth bridge with `u := v_n`, `v := w_smooth` gives
    --   smoothScalarH1Inner v_n w_smooth =
    --     ⟨smoothToLp v_n.oneSubLap, smoothToLp w_smooth⟩_{L²}.
    -- Apply real_inner_comm to swap.
    have h := smoothScalarH1Inner_eq_lpInner_oneSubLap (v n) w_smooth
    rw [h, real_inner_comm]
  -- Step 5: identify smoothScalarH1Inner v_n w_smooth with the H¹Compl inner
  -- product `⟨smoothToH1Compl v_n, smoothToH1Compl w_smooth⟩_{H¹Compl}`.
  have h_h1_n : ∀ n,
      smoothScalarH1Inner (I := I) (M := M) (v n) w_smooth =
      ⟪smoothToH1Compl (I := I) (M := M) g (v n),
        smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ :=
    fun n => (inner_smoothToH1Compl_smoothToH1Compl (v n) w_smooth).symm
  -- Step 6: combine all steps to get the per-n equation.
  have h_per_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) =
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ := by
    intro n
    rw [h_clm_eq_inner_n n, h_inner_assoc_n n, h_smooth_replace_n n,
      h_bridge_n n, h_h1_n n]
  -- Step 7: pass to the limit in n via H¹ inner-product continuity in the
  -- LEFT argument. Then identify the limit as a chart-pulled integral via the
  -- resolvent variational identity for u_h.
  have h_lim_lhs : Tendsto (fun n =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) atTop
      (𝓝 ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) := by
    -- `(innerSL ℝ y) u = ⟨y, u⟩`. So `(innerSL ℝ y).continuous` gives
    -- `Continuous (λ u, ⟨y, u⟩)`. Symmetrise both sides via `real_inner_comm`.
    have h_inner_y_cont : Continuous fun u : H1Compl g =>
        ⟪smoothToH1Compl (I := I) (M := M) g w_smooth, u⟫_ℝ :=
      (innerSL ℝ (smoothToH1Compl (I := I) (M := M) g w_smooth)).continuous
    have h_swap_fn : (fun n =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) =
        (fun n =>
          ⟪smoothToH1Compl (I := I) (M := M) g w_smooth,
            smoothToH1Compl (I := I) (M := M) g (v n)⟫_ℝ) := by
      funext n; exact real_inner_comm _ _
    have h_swap_lim :
        ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ =
        ⟪smoothToH1Compl (I := I) (M := M) g w_smooth, u_h⟫_ℝ :=
      real_inner_comm _ _
    rw [h_swap_fn, h_swap_lim]
    exact (h_inner_y_cont.tendsto _).comp h_tendsto
  -- Step 8: resolvent variational identity for u_h gives
  --   ⟨u_h, smoothToH1Compl w_smooth⟩_{H¹}
  --     = ⟨smoothToLp w_smooth, H1ComplToLp u_h - laplacianOp ⟨u_h, hu_h⟩⟩_{L²}.
  have h_res :
      ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ =
        ⟪smoothToLp (I := I) (M := M) g w_smooth,
          H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ :=
    h1Inner_smoothToH1Compl_eq_lpInner_oneSubLap_of_laplacianDomain
      (I := I) (M := M) g hu_h w_smooth
  -- Step 9: identify the L² inner product with the target chartPulledIntegralCLM.
  -- Going back through the same identities (now with `(1-Δ) u_h` instead of
  -- `smoothToLp v_n.oneSubLap`), we get:
  --   ⟨smoothToLp w_smooth, F⟩_{L²}
  --     = ⟨smoothMulLp ρα w_θ_lp, F⟩_{L²}        [via smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn]
  --     = ⟨w_θ_lp, smoothMulLp ρα F⟩_{L²}        [associativity]
  --     = chartPulledIntegralCLM ... (smoothMulLp ρα F).
  -- The associativity step is symmetric: rerun the same calculation.
  have h_target_eq :
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ =
        chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) := by
    -- 1) Replace smoothToLp w_smooth with smoothMulLp ρα w_θ_lp:
    rw [← smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_supp]
    -- 2) Associativity (mirrors h_inner_assoc_n):
    -- ⟨smoothMulLp ρα w_θ_lp, F⟩_{L²} = ⟨w_θ_lp, smoothMulLp ρα F⟩_{L²}.
    have h_assoc :
        ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (chartPulledIntegralWeightLp (I := I) (M := M) g α
              hθ_cont hθ_cs hθ_supp),
          H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ =
        ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_supp,
          smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)⟫_ℝ := by
      rw [L2.inner_def, L2.inner_def]
      have h_lhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp)
      have h_rhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
      refine integral_congr_ae ?_
      filter_upwards [h_lhs_mul, h_rhs_mul] with x hx_lhs hx_rhs
      -- For real-valued integrand: `⟪a, b⟫_ℝ` on ℝ-scalars unfolds to
      -- multiplication via `RCLike.inner_apply` (definitionally `y * conj x`).
      have h_inner_lhs :
          ⟪((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (chartPulledIntegralWeightLp (I := I) (M := M) g α
                  hθ_cont hθ_cs hθ_supp) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
            ((H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
          ((H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (chartPulledIntegralWeightLp (I := I) (M := M) g α
                  hθ_cont hθ_cs hθ_supp) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
      have h_inner_rhs :
          ⟪((chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_supp :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
            ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (H1ComplToLp (I := I) (M := M) g u_h -
                  laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
          ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (H1ComplToLp (I := I) (M := M) g u_h -
                  laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_supp :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
      rw [h_inner_lhs, h_inner_rhs, hx_lhs, hx_rhs]
      ring
    rw [h_assoc]
    -- 3) Unfold chartPulledIntegralCLM to innerSL.
    unfold chartPulledIntegralCLM
    rw [innerSL_apply_apply]
  -- Step 10: combine the steps.
  rw [show (fun n : ℕ => chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp
        (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical))) =
      fun n : ℕ =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ from
      funext h_per_n]
  rw [show chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
      (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) =
      ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ from ?_]
  · exact h_lim_lhs
  · rw [h_res, h_target_eq]

/-! ## CLM-form chart-pulled variational identity

A linearity-only rewriting of the chart-pulled integral CLM applied to
`fHLeibniz g α u_h hu_h` into its three constituent
`chartPulledIntegralCLM`-pieces. The substantive form-B headline (matching
the smooth-case integral shape, with weak partials in the principal LHS
and chart-pushed Lp class in the mass LHS) is in
`LaplacianDomainVariationalIdentityFormB.lean`. -/

/-- **CLM-form chart-pulled rewriting of `chartPulledIntegralCLM ∘ fHLeibniz`.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h : H1Compl g` lying in `laplacianDomain g`, the linearity of
`chartPulledIntegralCLM` and the definitional expansion `fHLeibniz_def`
yield the identity below. This is a re-expression of the right-hand side of
the form-B headline in CLM-application form. -/
theorem laplacianDomain_variational_identity_clm_form
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
      (2 : ℝ) *
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (gradInnerCLM (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h)) =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
      (fHLeibniz (I := I) (M := M) g α u_h hu_h) := by
  classical
  -- Step 1: Pick a smooth approximating sequence v_n → u_h in H¹Compl.
  obtain ⟨v, h_v_tendsto⟩ :=
    exists_smooth_approx_seq (I := I) (M := M) g u_h
  -- Step 2: Both sides converge as n → ∞.
  -- LHS_n = chartPulledIntegralCLM (smoothMulLp ρα (smoothToLp v_n.oneSubLap))
  --         - 2 * chartPulledIntegralCLM (gradInnerSmooth ρα v_n)
  --         - chartPulledIntegralCLM (smoothMulLp Δρα (smoothToLp v_n))
  -- The three convergences:
  have h_lim_1 := chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp hu_h h_v_tendsto
  have h_lim_2 := chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp h_v_tendsto
  have h_lim_3 := chartPulledIntegralCLM_smoothMulLp_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp h_v_tendsto
  -- Combine the three limits into the LHS limit.
  have h_lhs_lim : Tendsto (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (gradInnerSmooth (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)))) := by
    refine (h_lim_1.sub ?_).sub h_lim_3
    exact (tendsto_const_nhds.mul h_lim_2 : Tendsto _ _ _)
  -- The RHS limit: chartPulledIntegralCLM (fHLeibniz_{smooth case}) →
  --   chartPulledIntegralCLM (fHLeibniz u_h hu_h).
  -- This is the smooth-case formula `fHLeibniz_smoothToH1Compl` PLUS the
  -- continuity of chartPulledIntegralCLM in the Lp argument.
  -- For each n, the LHS_n value equals
  --   chartPulledIntegralCLM (fHLeibniz_{smooth case n}) = RHS_n
  -- by the smooth-case identity `fHLeibniz_smoothToH1Compl`.
  have h_smooth_eq_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (gradInnerSmooth (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g (v n))) =
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))) := by
    intro n
    rw [fHLeibniz_smoothToH1Compl (I := I) (M := M) g α (v n)]
    -- ChartPulledIntegralCLM is linear; apply linearity.
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  -- Step 3: rewrite the LHS limit using the smooth-case identity.
  have h_lhs_smooth_form : Tendsto (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))))
      atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)))) := by
    -- The function `n ↦ ChartPulledIntegralCLM ... (fHLeibniz (smoothToH1Compl v_n) _)`
    -- equals `n ↦ <LHS_n>` by h_smooth_eq_n. So it tends to the same value as
    -- h_lhs_lim.
    have h_fun_eq : (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (fHLeibniz (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g (v n))
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))) =
        (fun n =>
          chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
            (2 : ℝ) *
              chartPulledIntegralCLM (I := I) (M := M) g α
                (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
                (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
                (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
                (gradInnerSmooth (I := I) (M := M) g
                  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (smoothMulLp (I := I) (M := M) g
                (laplacianOfChartPOU (I := I) (M := M) g α)
                (smoothToLp (I := I) (M := M) g (v n)))) := by
      funext n
      exact (h_smooth_eq_n n).symm
    rw [h_fun_eq]
    exact h_lhs_lim
  -- Step 4: The function `n ↦ smoothToH1Compl (v n)` is bounded continuous
  -- in the Lp argument; together with the headline
  -- `chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto` from
  -- `ChartPulledIntegralContinuity.lean`, the limit identity for the RHS holds.
  -- We don't need that lemma here; instead we use directly that both
  -- `chartPulledIntegralCLM (fHLeibniz (smoothToH1Compl v_n) _) → ?` AND
  -- `chartPulledIntegralCLM (fHLeibniz u_h hu_h)` are limits of the same
  -- sequence (via h_lhs_smooth_form). It suffices to derive the LIMIT VALUE
  -- equals `chartPulledIntegralCLM (fHLeibniz u_h hu_h)`.
  --
  -- The shape we need: pass through `LHS_n = RHS_n`, take the limit on both
  -- sides. LHS_n → LHS(u_h) (the LHS of our headline), RHS_n → RHS(u_h)
  -- (the RHS of our headline). The equality is preserved in the limit.
  --
  -- We have `h_lhs_smooth_form : LHS_n(reordered) → LHS(u_h)`.
  -- We need also: the same sequence tends to RHS(u_h)
  --   = chartPulledIntegralCLM (fHLeibniz u_h hu_h).
  -- This is the LHS_n value tends to RHS(u_h). Combined with uniqueness of
  -- limits, RHS(u_h) = LHS(u_h).
  --
  -- The path to RHS(u_h):
  --   chartPulledIntegralCLM (fHLeibniz (smoothToH1Compl v_n) _)
  --     → chartPulledIntegralCLM (fHLeibniz u_h hu_h)
  -- IF we know fHLeibniz (smoothToH1Compl v_n) _ → fHLeibniz u_h hu_h in Lp.
  -- This convergence comes from continuity of `fHLeibniz` as a linear
  -- functional of `u_h`.
  --
  -- Actually `fHLeibniz` is NOT continuous as a function of u_h directly,
  -- because `laplacianOp ⟨u_h, hu_h⟩` requires the explicit hu_h proof
  -- and `laplacianOp` as a map `laplacianDomain →ₗ[ℝ] Lp` is NOT continuous.
  --
  -- HOWEVER: we can avoid this entirely by combining `h_lhs_smooth_form` and
  -- `h_lhs_lim` via the smooth-case identity `h_smooth_eq_n`. Specifically:
  --   h_lhs_lim shows LHS_n → LHS(u_h).
  --   h_smooth_eq_n says LHS_n = RHS_n where RHS_n = chartPulledIntegralCLM
  --                              (fHLeibniz (smoothToH1Compl v_n) _).
  --   So RHS_n → LHS(u_h) (same sequence, same limit).
  --
  -- For this to equal RHS(u_h) = chartPulledIntegralCLM (fHLeibniz u_h hu_h),
  -- we need the SEPARATE convergence of RHS_n to RHS(u_h). This is exactly
  -- the substantive content; it depends on Lp-convergence of `fHLeibniz_n →
  -- fHLeibniz u_h hu_h`.
  --
  -- Note: `chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto` from
  -- `ChartPulledIntegralContinuity.lean` provides the implication
  -- `fHLeibniz_n → fHLeibniz u_h hu_h ⇒ RHS_n → RHS(u_h)`. We have the
  -- antecedent, by:
  --
  -- fHLeibniz_n := smoothMulLp ρα (smoothToLp v_n.oneSubLap)
  --              - 2 * gradInnerSmooth ρα v_n
  --              - smoothMulLp Δρα (smoothToLp v_n).
  -- fHLeibniz u_h := smoothMulLp ρα ((1-Δ)u_h) - 2 * gradInnerCLM ρα u_h
  --                  - smoothMulLp Δρα (H1ComplToLp u_h).
  --
  -- For the bilinear bypass to apply, we need fHLeibniz_n → fHLeibniz u_h hu_h
  -- in Lp. The piece `smoothMulLp ρα (smoothToLp v_n.oneSubLap)` does NOT
  -- converge in Lp. So `fHLeibniz_n` does NOT converge in Lp in general.
  -- Hence `chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto` is NOT
  -- applicable directly.
  --
  -- THE BYPASS WORKS AT THE chartPulledIntegralCLM LEVEL, not at the
  -- fHLeibniz Lp level: chartPulledIntegralCLM (fHLeibniz_n) DOES converge
  -- (to chartPulledIntegralCLM (fHLeibniz u_h hu_h)), even though
  -- fHLeibniz_n does NOT converge in Lp.
  --
  -- The path: each of the three blocks at the chartPulledIntegralCLM level
  -- converges separately (h_lim_1, h_lim_2, h_lim_3), and their sum at the
  -- chartPulledIntegralCLM level equals the chartPulledIntegralCLM of
  -- fHLeibniz u_h hu_h (which we derive directly using fHLeibniz_def and
  -- linearity of chartPulledIntegralCLM).
  --
  -- So the LIMIT of `chartPulledIntegralCLM (fHLeibniz_n)` equals the LIMIT
  -- of LHS_n via h_smooth_eq_n, which equals the bilinear-bypass limit value.
  -- And the bilinear-bypass limit value equals chartPulledIntegralCLM
  -- (fHLeibniz u_h hu_h) by direct linearity expansion.
  --
  -- Let me prove the linearity expansion.
  have h_rhs_eq : chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (fHLeibniz (I := I) (M := M) g α u_h hu_h) =
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (gradInnerCLM (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (H1ComplToLp (I := I) (M := M) g u_h)) := by
    rw [fHLeibniz_def]
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  -- Apply `h_rhs_eq` to rewrite the RHS into the linearly-expanded form,
  -- which then matches the LHS of the goal by `rfl`.
  exact h_rhs_eq.symm

end LaplacianDomainVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentity.chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
#print axioms
  DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentity.laplacianDomain_variational_identity_clm_form
end Sanity
