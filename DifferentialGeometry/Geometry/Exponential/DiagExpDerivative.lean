import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option linter.unusedSectionVars false

/-!
# Zero-section derivative of the diagonal exponential map

For a smooth Riemannian metric `g` on a boundaryless, complete Riemannian
manifold `M` modelled on a complete inner-product space `E`, the diagonal
intrinsic exponential map

`diagExp g hEnorm u = (u.proj, exp_{u.proj}(u.snd)) : TangentBundle I M → M × M`

is `C∞` at the zero section `⟨p, 0⟩` (`diagExp_contMDiffAt_zero`).  This file
identifies its Fréchet derivative *in charts* at the zero section.  Writing the
map in the tangent-bundle chart at `⟨p, 0⟩` and the product chart at
`diagExp ⟨p, 0⟩ = (p, p)`, the derivative is the unipotent block map

`(δz₁, δz₂) ↦ (δz₁, δz₁ + δz₂)`.

The endpoint partial is the sum of two identity partials:
* the *fibre* partial `∂_v exp_p(v)|₀ = id` (`mfderiv_expMapIntrinsic_at_zero`),
  collapsed to the identity at base `p` by `chartFiberCoord_mk_self`;
* the *base* partial `∂_q exp_q(0)|_p = id`, from `exp_q 0 = q`
  (`expMapIntrinsic_zero`) and chart cancellation.

## Main results

* `diagExp_hasFDerivAt_zero` — the charted `HasFDerivAt` statement with
  derivative `(fst ℝ E E).prod (fst + snd)`.
* `diagExp_hasFDerivAt_zero_unipotent` — the same, packaged through the
  unipotent continuous linear equivalence `(z₁, z₂) ↦ (z₁, z₁ + z₂)`.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section DiagExpDerivative

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The diagonal exponential map written in the tangent-bundle chart at the zero
section and the product chart at `diagExp ⟨p, 0⟩`. -/
private def chartedDiagExp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : E × E → E × E :=
  extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M)) ∘
    diagExp (I := I) g hEnorm ∘
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The base chart point of the zero section. -/
private def diagExpZeroPt (p : M) : E × E :=
  extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
    (⟨p, (0 : E)⟩ : TangentBundle I M)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- `chartedDiagExp g hEnorm p` is `ContDiffAt ℝ n` at the zero-section chart
point, for every finite order `n`. -/
private lemma chartedDiagExp_contDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContDiffAt ℝ (n : ℕ∞) (chartedDiagExp (I := I) g hEnorm p)
      (diagExpZeroPt (I := I) p) := by
  classical
  have hmd := diagExp_contMDiffAt_zero (I := I) g hEnorm p n hn
  rw [contMDiffAt_iff] at hmd
  obtain ⟨_, hcd⟩ := hmd
  have hrange : range (I.tangent) = (univ : Set (E × E)) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange] at hcd
  exact contDiffWithinAt_univ.mp hcd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- `diagExp ⟨p, 0⟩ = (p, p)`: at the zero section the endpoint is `exp_p 0 = p`. -/
private lemma diagExp_zero_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M) = (p, p) := by
  rw [diagExp_apply]
  refine Prod.ext rfl ?_
  change expMapIntrinsic (I := I) g hEnorm p 0 = p
  exact expMapIntrinsic_zero (I := I) g hEnorm p

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The zero-section chart point is `(extChartAt I p p, 0)`. -/
private lemma diagExpZeroPt_eq [T2Space (TangentBundle I M)] (p : M) :
    diagExpZeroPt (I := I) p = ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  rw [diagExpZeroPt]
  rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p
    (p := (⟨p, (0 : E)⟩ : TangentBundle I M)) (by exact mem_chart_source H p)]
  change ((extChartAt I p p, chartFiberCoord (I := I) p (⟨p, (0 : E)⟩ : TangentBundle I M)) : E × E)
    = ((extChartAt I p p, (0 : E)) : E × E)
  rw [chartFiberCoord_self_zero (I := I) p]

/-- **General zero-section fibre coordinate.** For any base point `q` in the
chart-`p` source, the chart-`p` fibre coordinate of the zero vector `⟨q, 0⟩` is
zero. -/
private lemma chartFiberCoord_mk_zero (p q : M)
    (hq : q ∈ (chartAt H p).source) :
    chartFiberCoord (I := I) p (⟨q, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hq_base : q ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  have hzero := (trivializationAt E (TangentSpace I) p).zeroSection ℝ (x := q) hq_base
  have hzero' : (trivializationAt E (TangentSpace I) p)
      (⟨q, (0 : TangentSpace I q)⟩ : TangentBundle I M) = (q, 0) := hzero
  change (trivializationAt E (TangentSpace I) p
      (⟨q, (0 : TangentSpace I q)⟩ : TangentBundle I M)).2 = 0
  rw [hzero']

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Chart inverse of a zero-fibre point lands on the zero section.** For a
chart-target-interior point `z` with `z.2 = 0`, the chart inverse at `⟨p, 0⟩`
returns the zero vector over `(extChartAt I p).symm z.1`. -/
private lemma extChartAt_tangent_zero_symm_zero_fiber
    [T2Space (TangentBundle I M)] (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hz2 : z.2 = 0) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z =
      (⟨(extChartAt I p).symm z.1, (0 : E)⟩ : TangentBundle I M) := by
  classical
  set q : M := (extChartAt I p).symm z.1 with hq_def
  have hz1_target : z.1 ∈ (extChartAt I p).target := interior_subset hz.1
  have hq_src : q ∈ (chartAt H p).source := by
    rw [hq_def, ← extChartAt_source I]; exact (extChartAt I p).map_target hz1_target
  -- chart of the zero section over `q`
  have hchart_zero : extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      (⟨q, (0 : E)⟩ : TangentBundle I M) = z := by
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p
      (p := (⟨q, (0 : E)⟩ : TangentBundle I M)) (by exact hq_src)]
    rw [chartFiberCoord_mk_zero (I := I) p q hq_src]
    have hz1 : extChartAt I p q = z.1 := by
      rw [hq_def, (extChartAt I p).right_inv hz1_target]
    rw [hz1, ← hz2]
  -- invert
  have hsymm := congrArg
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm hchart_zero
  rw [(extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv
    (by rw [extChartAt_source];
        exact (mem_chartAt_modelProd_zero_source_iff (I := I) p _).mpr hq_src)] at hsymm
  rw [← hsymm]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Chart inverse fibre at the base point.** For a chart-target-interior point
`z` whose base component is `extChartAt I p p`, the chart inverse at `⟨p, 0⟩` has
projection `p` and fibre `z.2`. -/
private lemma extChartAt_tangent_zero_symm_at_base
    [T2Space (TangentBundle I M)] (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hz1 : z.1 = extChartAt I p p) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z =
      (⟨p, z.2⟩ : TangentBundle I M) := by
  classical
  set u : TangentBundle I M :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z with hu_def
  have hproj : u.proj = p := by
    rw [hu_def, extChartAt_tangent_zero_symm_proj (I := I) p hz, hz1]
    exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have hsrc : u.proj ∈ (chartAt H p).source := by
    rw [hproj]; exact mem_chart_source H p
  have happly : extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) u = z :=
    extChartAt_tangent_zero_apply_symm (I := I) p hz
  have hpair := extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := u) hsrc
  rw [happly] at hpair
  have hfib : chartFiberCoord (I := I) p u = z.2 := by
    have := congrArg Prod.snd hpair
    exact this.symm
  -- rebuild `u` as `⟨p, z.2⟩` using `chartFiberCoord_mk_self`
  have hu_eq : u = (⟨u.proj, u.snd⟩ : TangentBundle I M) := rfl
  have hmk : chartFiberCoord (I := I) p (⟨p, u.snd⟩ : TangentBundle I M) = u.snd :=
    chartFiberCoord_mk_self (I := I) p u.snd
  have hsnd : u.snd = z.2 := by
    have hfib' : chartFiberCoord (I := I) p (⟨p, u.snd⟩ : TangentBundle I M) = z.2 := by
      rw [← hfib]; congr 1; rw [← hproj]
    rw [← hmk, hfib']
  -- assemble
  calc u = (⟨u.proj, u.snd⟩ : TangentBundle I M) := rfl
    _ = (⟨p, z.2⟩ : TangentBundle I M) := by rw [hproj, hsnd]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The chart-pushed *intrinsic* exponential map at `p` (fixed base). -/
private def chartedExpIntrinsic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : E → E :=
  fun v => extChartAt I p (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The fixed-base intrinsic charted exponential has Fréchet derivative `id` at
`0`.**  Mirrors `LocalDiffeomorphism.chartedExpAt_hasFDerivAt_zero` with the intrinsic
exponential, using `mfderiv_expMapIntrinsic_at_zero`. -/
private lemma chartedExpIntrinsic_hasFDerivAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    HasFDerivAt (chartedExpIntrinsic (I := I) g hEnorm p)
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  classical
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  -- intrinsic exp has manifold derivative `id` at `0`
  have hdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) := by
    by_contra hcon
    have h0 := mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p
    rw [mfderiv_zero_of_not_mdifferentiableAt hcon] at h0
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvz : (0 : E) = v := by simpa using DFunLike.congr_fun h0 v
    exact hv hvz.symm
  have hexp_mfd : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) (ContinuousLinearMap.id ℝ E) := by
    have h := hdiff.hasMFDerivAt
    rwa [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p] at h
  -- extChartAt at the image point `exp_p 0 = p`
  have hpt : (fun v : E => (expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from v) : M)) 0 = p := by
    change expMapIntrinsic (I := I) g hEnorm p 0 = p
    exact expMapIntrinsic_zero (I := I) g hEnorm p
  have hext_hasMFD : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
      (ContinuousLinearMap.id ℝ E) := by
    have hm := ((contMDiffAt_extChartAt (I := I) (x := p) (n := 1)).mdifferentiableAt
      one_ne_zero).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := p)] at hm
    exact hm
  have hext_at_pt : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p)
      ((fun v : E => (expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from v) : M)) 0) (ContinuousLinearMap.id ℝ E) := by
    rw [hpt]; exact hext_hasMFD
  have hcomp_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((extChartAt I p) ∘
        (fun v : E => (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from v) : M)))
      (0 : E) ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)) :=
    hext_at_pt.comp (0 : E) hexp_mfd
  rw [ContinuousLinearMap.id_comp] at hcomp_mfd
  exact hasMFDerivAt_iff_hasFDerivAt.mp hcomp_mfd

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Zero-section derivative of the diagonal exponential, in charts.**  Writing
`diagExp` in the tangent-bundle chart at `⟨p,0⟩` and the product chart at
`diagExp ⟨p,0⟩ = (p,p)`, the Fréchet derivative at the zero-section chart point is
the unipotent block map `(δz₁, δz₂) ↦ (δz₁, δz₁ + δz₂)`.

Proof: the chart-pushed map is `ContDiffAt` (from total-space smoothness
`diagExp_contMDiffAt_zero`), hence has a Fréchet derivative `D`; `D` is identified
as `fst.prod (fst + snd)` from its two partials, each the identity — the base
partial via `exp_q 0 = q`, the fibre partial via the fixed-base
`chartedExpIntrinsic_hasFDerivAt_zero`. -/
theorem diagExp_hasFDerivAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      ((ContinuousLinearMap.fst ℝ E E).prod
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
      (diagExpZeroPt (I := I) p) := by
  classical
  rw [diagExpZeroPt_eq (I := I) p]
  set c : E := extChartAt I p p with hc_def
  -- `c` is in the interior of the chart target (boundaryless)
  have hc_int : c ∈ interior (extChartAt I p).target := by
    rw [hc_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) p ((extChartAt I p).map_source (mem_extChartAt_source (I := I) p))
  -- chartedDiagExp is differentiable at `(c, 0)`
  have hcd := chartedDiagExp_contDiffAt (I := I) g hEnorm p n hn
  rw [diagExpZeroPt_eq (I := I) p] at hcd
  have hD : HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      (fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) ((c, (0 : E)) : E × E))
      ((c, (0 : E)) : E × E) :=
    (hcd.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn)).hasFDerivAt
  set D := fderiv ℝ (chartedDiagExp (I := I) g hEnorm p) ((c, (0 : E)) : E × E) with hD_def
  -- base partial: `chartedDiagExp (z₁, 0) = (z₁, z₁)` near `c`
  have hbase_eq : (fun z₁ : E => chartedDiagExp (I := I) g hEnorm p ((z₁, (0 : E)) : E × E))
      =ᶠ[𝓝 c] (fun z₁ : E => ((z₁, z₁) : E × E)) := by
    filter_upwards [isOpen_interior.mem_nhds hc_int] with z₁ hz₁int
    have hz1t : z₁ ∈ (extChartAt I p).target := interior_subset hz₁int
    have hz : ((z₁, (0 : E)) : E × E) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := ⟨hz₁int, Set.mem_univ _⟩
    have hinner : diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ((z₁, (0 : E)) : E × E))
        = ((extChartAt I p).symm z₁, (extChartAt I p).symm z₁) := by
      rw [extChartAt_tangent_zero_symm_zero_fiber (I := I) p hz rfl, diagExp_apply]
      exact Prod.ext rfl (expMapIntrinsic_zero (I := I) g hEnorm _)
    simp only [chartedDiagExp, Function.comp_apply]
    rw [hinner, diagExp_zero_eq (I := I) g hEnorm p, extChartAt_prod]
    simp only [PartialEquiv.prod_coe]
    rw [(extChartAt I p).right_inv hz1t]
  -- fibre partial: `chartedDiagExp (c, z₂) = (c, chartedExpIntrinsic z₂)`
  have hfiber_eq : (fun z₂ : E => chartedDiagExp (I := I) g hEnorm p ((c, z₂) : E × E))
      =ᶠ[𝓝 (0 : E)] (fun z₂ : E => ((c, chartedExpIntrinsic (I := I) g hEnorm p z₂) : E × E)) := by
    filter_upwards with z₂
    have hz : ((c, z₂) : E × E) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := ⟨hc_int, Set.mem_univ _⟩
    have hinner : diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ((c, z₂) : E × E))
        = (p, expMapIntrinsic (I := I) g hEnorm p z₂) := by
      rw [extChartAt_tangent_zero_symm_at_base (I := I) p hz hc_def, diagExp_apply]
    simp only [chartedDiagExp, Function.comp_apply]
    rw [hinner, diagExp_zero_eq (I := I) g hEnorm p, extChartAt_prod]
    simp only [PartialEquiv.prod_coe]
    exact Prod.ext hc_def.symm rfl
  -- the two partials of `D` are identities
  have hinl : D.comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))
      = (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E) := by
    have haff : HasFDerivAt (fun z₁ : E => ((z₁, (0 : E)) : E × E))
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) c :=
      (hasFDerivAt_id c).prodMk (hasFDerivAt_const (0 : E) c)
    have hc1 := hD.comp c haff
    have hid : HasFDerivAt (fun z₁ : E => ((z₁, z₁) : E × E))
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) c :=
      (hasFDerivAt_id c).prodMk (hasFDerivAt_id c)
    exact (hc1.congr_of_eventuallyEq hbase_eq.symm).unique hid
  have hinr : D.comp ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))
      = (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E) := by
    have haff : HasFDerivAt (fun z₂ : E => ((c, z₂) : E × E))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (0 : E) :=
      (hasFDerivAt_const c (0 : E)).prodMk (hasFDerivAt_id (0 : E))
    have hc2 := hD.comp (0 : E) haff
    have hpair : HasFDerivAt (fun z₂ : E => ((c, chartedExpIntrinsic (I := I) g hEnorm p z₂) : E × E))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (0 : E) :=
      (hasFDerivAt_const c (0 : E)).prodMk (chartedExpIntrinsic_hasFDerivAt_zero (I := I) g hEnorm p)
    exact (hc2.congr_of_eventuallyEq hfiber_eq.symm).unique hpair
  -- assemble `D = fst.prod (fst + snd)`
  have hDL : D = (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    have hsplit : ((a, b) : E × E) =
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) a +
          ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) b := by
      simp
    rw [hsplit, map_add, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      hinl, hinr]
    simp
  rw [← hDL]; exact hD

/-- The unipotent continuous linear equivalence `(z₁, z₂) ↦ (z₁, z₁ + z₂)` on
`E × E`, whose underlying map is the zero-section derivative of `diagExp`. -/
def unipotentCLE : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))
    (by intro z; simp)
    (by intro z; simp)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The zero-section derivative of `diagExp` packaged through the unipotent
continuous linear equivalence — the exact Banach-IFT input. -/
theorem diagExp_hasFDerivAt_zero_unipotent
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (chartedDiagExp (I := I) g hEnorm p)
      (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)) (diagExpZeroPt (I := I) p) :=
  diagExp_hasFDerivAt_zero (I := I) g hEnorm p n hn

/-! ### Banach inverse function theorem: the moving-base inverse section

With the zero-section regularity (`diagExp_contMDiffAt_zero`) and the invertible
derivative (`diagExp_hasFDerivAt_zero_unipotent`) the Banach inverse function
theorem applies to `chartedDiagExp` at the zero-section chart point, producing a
local inverse of `diagExp` near `(p, p)`.  Transported through the tangent-bundle
chart at `⟨p, 0⟩` and the product chart at `(p, p)`, it yields the **moving-base
inverse section** `diagExpInv`, with `diagExp (diagExpInv y) = y` near `(p, p)`.
For `y = (q, pt)` this is the inverse exponential `q ↦ exp_q⁻¹(pt)`. -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- `chartedDiagExp g hEnorm p` is `ContDiffAt ℝ 1` at the zero-section chart
point (the `ContDiffAt` packaged at smoothness level `1`, ready for the IFT). -/
private lemma chartedDiagExp_cdaOne
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContDiffAt ℝ 1 (chartedDiagExp (I := I) g hEnorm p) (diagExpZeroPt (I := I) p) := by
  simpa using chartedDiagExp_contDiffAt (I := I) g hEnorm p 1 le_rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The Banach inverse function theorem applied to `chartedDiagExp` at the
zero-section chart point, with derivative the unipotent block equivalence. -/
private def diagExpIFT
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : OpenPartialHomeomorph (E × E) (E × E) :=
  ContDiffAt.toOpenPartialHomeomorph (𝕂 := ℝ)
    (f := chartedDiagExp (I := I) g hEnorm p)
    (f' := unipotentCLE (E := E))
    (chartedDiagExp_cdaOne (I := I) g hEnorm p)
    (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl)
    one_ne_zero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The IFT homeomorph realises `chartedDiagExp` on its source. -/
private lemma diagExpIFT_coe
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ⇑(diagExpIFT (I := I) g hEnorm p) = chartedDiagExp (I := I) g hEnorm p := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The chart inverse of the zero-section chart point is `⟨p, 0⟩`. -/
private lemma inner_symm_zeroPt
    [T2Space (TangentBundle I M)] (p : M) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (diagExpZeroPt (I := I) p)
      = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  rw [diagExpZeroPt]
  exact (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv
    (mem_extChartAt_source (I := I.tangent) (⟨p, (0 : E)⟩ : TangentBundle I M))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The product chart value at `(p, p)` equals `chartedDiagExp` at the
zero-section chart point. -/
private lemma outer_center
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    extChartAt (I.prod I) (p, p) (p, p) =
      chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p) := by
  change extChartAt (I.prod I) (p, p) (p, p)
    = extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M))
        (diagExp (I := I) g hEnorm
          ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (diagExpZeroPt (I := I) p)))
  rw [inner_symm_zeroPt (I := I) p, diagExp_zero_eq (I := I) g hEnorm p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The moving-base inverse section.**  The local inverse of `diagExp` near the
zero section, transported through the tangent-bundle chart at `⟨p, 0⟩` and the
product chart at `(p, p)`.  Near `(p, p)` it satisfies `diagExp (diagExpInv y) = y`
(`diagExp_diagExpInv`); for `y = (q, pt)` it is the inverse exponential
`q ↦ exp_q⁻¹(pt)`. -/
def diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) : M × M → TangentBundle I M :=
  fun y => (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
    ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) y))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The inverse section sends the diagonal point `(p, p)` to the zero vector
`⟨p, 0⟩`. -/
theorem diagExpInv_center
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    diagExpInv (I := I) g hEnorm p (p, p) = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  change (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p)))
      = (⟨p, (0 : E)⟩ : TangentBundle I M)
  rw [outer_center (I := I) g hEnorm p, ← diagExpIFT_coe (I := I) g hEnorm p,
    (diagExpIFT (I := I) g hEnorm p).left_inv hsrc, inner_symm_zeroPt (I := I) p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The inverse section is `C¹` at the diagonal point `(p, p)`. -/
theorem diagExpInv_contMDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContMDiffAt (I.prod I) I.tangent 1 (diagExpInv (I := I) g hEnorm p) (p, p) := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have hsymm_eq : (diagExpIFT (I := I) g hEnorm p).symm =
      (chartedDiagExp_cdaOne (I := I) g hEnorm p).localInverse
        (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero := rfl
  have hsymm_cd : ContDiffAt ℝ 1 (diagExpIFT (I := I) g hEnorm p).symm
      (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)) := by
    rw [hsymm_eq]
    exact (chartedDiagExp_cdaOne (I := I) g hEnorm p).to_localInverse
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have h_outer : ContMDiffAt (I.prod I) 𝓘(ℝ, E × E) 1
      (extChartAt (I.prod I) (p, p)) (p, p) :=
    contMDiffAt_extChartAt (I := I.prod I) (x := (p, p)) (n := 1)
  have h_mid : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) 1
      (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p)) := by
    rw [outer_center (I := I) g hEnorm p]
    exact contMDiffAt_iff_contDiffAt.mpr hsymm_cd
  have hpt : (diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))
      = diagExpZeroPt (I := I) p := by
    rw [outer_center (I := I) g hEnorm p, ← diagExpIFT_coe (I := I) g hEnorm p]
    exact (diagExpIFT (I := I) g hEnorm p).left_inv hsrc
  have h_inner : ContMDiffAt 𝓘(ℝ, E × E) I.tangent 1
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((diagExpIFT (I := I) g hEnorm p).symm (extChartAt (I.prod I) (p, p) (p, p))) := by
    rw [hpt]
    have hb : range (I.tangent) = (univ : Set (E × E)) :=
      ModelWithCorners.Boundaryless.range_eq_univ
    have hsm := contMDiffWithinAt_extChartAt_symm_range_self (I := I.tangent) (n := 1)
      (⟨p, (0 : E)⟩ : TangentBundle I M)
    rw [hb, contMDiffWithinAt_univ] at hsm
    exact hsm
  exact h_inner.comp (p, p) (h_mid.comp (p, p) h_outer)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The right-inverse property.**  Near `(p, p)`, `diagExp (diagExpInv y) = y`.
For `y = (q, pt)` this says `exp_q (diagExpInv (q, pt)).snd = pt` with projection `q`,
i.e. `diagExpInv (q, pt)` is the inverse exponential `exp_q⁻¹(pt)`. -/
theorem diagExp_diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p),
      diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y := by
  have hsrc : diagExpZeroPt (I := I) p ∈ (diagExpIFT (I := I) g hEnorm p).source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source
      (chartedDiagExp_cdaOne (I := I) g hEnorm p)
      (diagExp_hasFDerivAt_zero_unipotent (I := I) g hEnorm p 1 le_rfl) one_ne_zero
  have htarget : chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p)
      ∈ (diagExpIFT (I := I) g hEnorm p).target := by
    have h := (diagExpIFT (I := I) g hEnorm p).map_source hsrc
    rwa [diagExpIFT_coe (I := I) g hEnorm p] at h
  have hev_ri := (diagExpIFT (I := I) g hEnorm p).eventually_right_inverse htarget
  have htend : Filter.Tendsto (extChartAt (I.prod I) (p, p)) (nhds (p, p))
      (nhds (chartedDiagExp (I := I) g hEnorm p (diagExpZeroPt (I := I) p))) := by
    rw [← outer_center (I := I) g hEnorm p]
    exact (continuousAt_extChartAt (I := I.prod I) (p, p)).tendsto
  have hev1 := htend.eventually hev_ri
  have hev_y : ∀ᶠ y in nhds (p, p), y ∈ (extChartAt (I.prod I) (p, p)).source :=
    extChartAt_source_mem_nhds (I := I.prod I) (p, p)
  have hcont : ContinuousAt
      (fun y => diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)) (p, p) := by
    have h1 : ContinuousAt (diagExpInv (I := I) g hEnorm p) (p, p) :=
      (diagExpInv_contMDiffAt (I := I) g hEnorm p).continuousAt
    have h2 : ContinuousAt (diagExp (I := I) g hEnorm)
        (diagExpInv (I := I) g hEnorm p (p, p)) := by
      rw [diagExpInv_center (I := I) g hEnorm p]
      exact (diagExp_contMDiffAt_zero (I := I) g hEnorm p 1 le_rfl).continuousAt
    exact h2.comp h1
  have hfx : diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p (p, p)) = (p, p) := by
    rw [diagExpInv_center (I := I) g hEnorm p, diagExp_zero_eq (I := I) g hEnorm p]
  have hev_d : ∀ᶠ y in nhds (p, p),
      diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)
        ∈ (extChartAt (I.prod I) (p, p)).source := by
    refine hcont.eventually_mem ?_
    rw [hfx]
    exact extChartAt_source_mem_nhds (I := I.prod I) (p, p)
  filter_upwards [hev1, hev_y, hev_d] with y hy1 hy2 hy3
  have e1 : (diagExpIFT (I := I) g hEnorm p) ((diagExpIFT (I := I) g hEnorm p).symm
      (extChartAt (I.prod I) (p, p) y)) =
      chartedDiagExp (I := I) g hEnorm p ((diagExpIFT (I := I) g hEnorm p).symm
        (extChartAt (I.prod I) (p, p) y)) :=
    congrFun (diagExpIFT_coe (I := I) g hEnorm p) _
  rw [e1] at hy1
  have e2 : chartedDiagExp (I := I) g hEnorm p ((diagExpIFT (I := I) g hEnorm p).symm
      (extChartAt (I.prod I) (p, p) y)) =
      extChartAt (I.prod I) (diagExp (I := I) g hEnorm (⟨p, (0 : E)⟩ : TangentBundle I M))
        (diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y)) := rfl
  rw [e2, diagExp_zero_eq (I := I) g hEnorm p] at hy1
  exact (extChartAt (I.prod I) (p, p)).injOn hy3 hy2 hy1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Near `(p, p)`, the inverse section projects to the base coordinate:
`(diagExpInv (q, pt)).proj = q`. -/
theorem diagExpInv_proj
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p), (diagExpInv (I := I) g hEnorm p y).proj = y.1 := by
  filter_upwards [diagExp_diagExpInv (I := I) g hEnorm p] with y hy
  have h := congrArg Prod.fst hy
  rwa [diagExp_fst] at h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The moving-base inverse exponential identity.**  Near `(p, p)`,
`exp_{(diagExpInv y).proj} (diagExpInv y).snd = y.2`; for `y = (q, pt)` (with
projection `q` by `diagExpInv_proj`) this is `exp_q (exp_q⁻¹ pt) = pt`. -/
theorem expIntr_diagExpInv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∀ᶠ y in nhds (p, p),
      expMapIntrinsic (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y).proj
        (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  filter_upwards [diagExp_diagExpInv (I := I) g hEnorm p] with y hy
  have h := congrArg Prod.snd hy
  rwa [diagExp_snd] at h

end DiagExpDerivative

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
