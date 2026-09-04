import DifferentialGeometry.Geometry.Comparison.CGTPaths
import DifferentialGeometry.Geometry.Comparison.Volume.BishopRawDensity
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoLift
import DifferentialGeometry.Geometry.Exponential.RawFramedLocalDiffeo

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates
open Geodesic
open VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The model-space radial curve with constant germs at both endpoints. -/
noncomputable def rawFlatRay (u : E) (t : Real) : E :=
  Real.smoothTransition (3 * t - 1) • u

omit [FiniteDimensional Real E] in
/-- The flat radial model curve starts at the origin. -/
@[simp] theorem rawFlatRay_zero (u : E) : rawFlatRay u 0 = 0 := by
  rw [rawFlatRay, Real.smoothTransition.zero_of_nonpos (by norm_num), zero_smul]

omit [FiniteDimensional Real E] in
/-- The flat radial model curve reaches its endpoint at time one. -/
@[simp] theorem rawFlatRay_one (u : E) : rawFlatRay u 1 = u := by
  rw [rawFlatRay, Real.smoothTransition.one_of_one_le (by norm_num), one_smul]

omit [FiniteDimensional Real E] in
/-- The flat radial model curve is smooth. -/
theorem rawFlatRay_cd (u : E) : ContDiff Real ∞ (rawFlatRay u) := by
  exact
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const)).smul contDiff_const

omit [FiniteDimensional Real E] in
/-- A flat radial ray stays in any centered ball containing its endpoint. -/
theorem rawFlatRay_mem
    {R : Real} {u : E} (hu : ‖u‖ < R) (t : Real) :
    rawFlatRay u t ∈ Metric.ball (0 : E) R := by
  have hnonneg : 0 ≤ Real.smoothTransition (3 * t - 1) :=
    Real.smoothTransition.nonneg _
  have hone : Real.smoothTransition (3 * t - 1) ≤ 1 :=
    Real.smoothTransition.le_one _
  rw [Metric.mem_ball, dist_zero_right, rawFlatRay, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (mul_le_of_le_one_left (norm_nonneg u) hone).trans_lt hu

omit [I.Boundaryless] in
/-- A full radial-domain premise contains every point of the flat radial ray. -/
theorem rawFlatRay_dom
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p)
    (t : Real) :
    normalFrame (I := I) g p (rawFlatRay u t) ∈ expDomain (I := I) g p := by
  rw [rawFlatRay, map_smul]
  exact hdom _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [I.Boundaryless] in
/-- The flat radial model curve is the canonical lift of its raw framed
exponential image inside every ball containing its endpoint. -/
theorem rawFlatRay_lift
    (g : SmoothRiemannianMetric I M) (p : M)
    {R : Real} {u : E} (hu : ‖u‖ < R) :
    IsLiftOn (framedExpMap (I := I) g p)
      ((framedExpMap (I := I) g p) ∘ rawFlatRay u)
      (Metric.ball (0 : E) R) 0 0 1 (rawFlatRay u) := by
  refine ⟨(rawFlatRay_cd u).continuous.continuousOn, rawFlatRay_zero u, ?_⟩
  intro t _
  exact ⟨rawFlatRay_mem hu t, rfl⟩

section RawPath

variable [T2Space (TangentBundle I M)]

/-- A flat raw-exponential radial image is smooth on the real line. -/
theorem rawFlatImage_cd
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    ContMDiff 𝓘(Real, Real) I ∞
      ((framedExpMap (I := I) g p) ∘ rawFlatRay u) := by
  intro t
  have hray : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (rawFlatRay u) :=
    contMDiff_iff_contDiff.mpr (rawFlatRay_cd u)
  exact
    (framedExp_mdiffAt (I := I) g p (rawFlatRay_dom (I := I) g p u hdom t)).comp
      t hray.contMDiffAt

/-- The flat radial raw-exponential curve as a path, under exactly the radial
time-one domain premise needed for its smoothness. -/
noncomputable def rawFlatPath
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    Path p (framedExpMap (I := I) g p u) where
  toFun t := framedExpMap (I := I) g p (rawFlatRay u t)
  continuous_toFun :=
    (rawFlatImage_cd (I := I) g p u hdom).continuous.comp continuous_subtype_val
  source' := by
    change framedExpMap (I := I) g p (rawFlatRay u (0 : Real)) = p
    rw [rawFlatRay_zero, framedExpMap_apply, map_zero]
    exact expMap_zero (I := I) g p
  target' := by
    change
      framedExpMap (I := I) g p (rawFlatRay u (1 : Real)) =
        framedExpMap (I := I) g p u
    rw [rawFlatRay_one]

/-- The extension of `rawFlatPath` is its raw-exponential radial image. -/
theorem rawFlatPath_ext
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    (rawFlatPath (I := I) g p u hdom).extend =
      (framedExpMap (I := I) g p) ∘ rawFlatRay u := by
  funext t
  change
    (rawFlatPath (I := I) g p u hdom).extend t =
      framedExpMap (I := I) g p (rawFlatRay u t)
  by_cases ht0 : t ≤ 0
  · rw [(rawFlatPath (I := I) g p u hdom).extend_of_le_zero ht0,
      rawFlatRay, Real.smoothTransition.zero_of_nonpos]
    · simp only [zero_smul, framedExpMap_apply, map_zero]
      exact (expMap_zero (I := I) g p).symm
    · linarith
  · have h0t : 0 ≤ t := (not_le.mp ht0).le
    by_cases ht1 : t ≤ 1
    · exact (rawFlatPath (I := I) g p u hdom).extend_apply ⟨h0t, ht1⟩
    · have h1t : 1 ≤ t := (not_le.mp ht1).le
      rw [(rawFlatPath (I := I) g p u hdom).extend_of_one_le h1t,
        rawFlatRay, Real.smoothTransition.one_of_one_le]
      · simp only [one_smul]
      · linarith

/-- The raw radial path is C1 and constant near both endpoints. -/
theorem rawFlatPath_flat
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    IsFlatC1Path (I := I) (rawFlatPath (I := I) g p u hdom) where
  c1 := by
    rw [rawFlatPath_ext]
    exact (rawFlatImage_cd (I := I) g p u hdom).of_le (by norm_num)
  flat_zero := by
    rw [rawFlatPath_ext]
    filter_upwards
      [eventually_lt_nhds (show (0 : Real) < 1 / 3 by norm_num)] with t ht
    change framedExpMap (I := I) g p (rawFlatRay u t) = p
    rw [rawFlatRay, Real.smoothTransition.zero_of_nonpos]
    · simp only [zero_smul, framedExpMap_apply, map_zero]
      exact expMap_zero (I := I) g p
    · linarith
  flat_one := by
    rw [rawFlatPath_ext]
    filter_upwards
      [eventually_gt_nhds (show (2 / 3 : Real) < 1 by norm_num)] with t ht
    change
      framedExpMap (I := I) g p (rawFlatRay u t) =
        framedExpMap (I := I) g p u
    rw [rawFlatRay, Real.smoothTransition.one_of_one_le]
    · simp only [one_smul]
    · linarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A raw framed radial exponential segment has length equal to the norm of
its model-space endpoint. -/
theorem rawRadial_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    Manifold.pathELength I
        ((framedExpMap (I := I) g p) ∘ fun t : Real => t • u) 0 1 =
      ENNReal.ofReal ‖u‖ := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete Real E
  by_cases hdim : Module.finrank Real E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    have hconst :
        (framedExpMap (I := I) g p) ∘ (fun t : Real => t • (0 : E)) =
          fun _ : Real => p := by
      funext t
      simp only [Function.comp_apply, smul_zero, framedExpMap_apply, map_zero]
      exact expMap_zero (I := I) g p
    rw [hconst, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    simp
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let v : TangentSpace I p := normalFrame (I := I) g p u
    let γ : Real → M := radialCurve (I := I) g p v
    have hcurve :
        (framedExpMap (I := I) g p) ∘ (fun t : Real => t • u) = γ := by
      funext t
      simp only [Function.comp_apply, framedExpMap_apply, γ, radialCurve, v,
        map_smul]
      rfl
    have hintegrand : ∀ t ∈ Set.Ioo (0 : Real) 1,
        ‖mfderiv 𝓘(Real, Real) I γ t (1 : Real)‖ₑ = ENNReal.ofReal ‖u‖ := by
      intro t ht
      have hspeed := rawSpeed_sq (I := I) g p v t ht.1.le (fun s hs =>
        hdom s ⟨hs.1, hs.2.trans ht.2.le⟩)
      rw [hEnorm]
      change
        ENNReal.ofReal (Real.sqrt
          (g.inner (γ t)
            (Variation.curveVelocity (I := I) γ t)
            (Variation.curveVelocity (I := I) γ t))) = ENNReal.ofReal ‖u‖
      rw [hspeed]
      exact congrArg ENNReal.ofReal (normalFrame_sqrt (I := I) g p u)
    rw [hcurve, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    calc
      ∫⁻ t in Set.Ioo (0 : Real) 1,
          ‖mfderiv 𝓘(Real, Real) I γ t (1 : Real)‖ₑ =
          ∫⁻ _t in Set.Ioo (0 : Real) 1, ENNReal.ofReal ‖u‖ :=
        MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hintegrand
      _ = ENNReal.ofReal ‖u‖ := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo, sub_zero,
          ENNReal.ofReal_one, mul_one]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The flat radial raw-exponential path has exactly the norm of its endpoint
as its Riemannian length. -/
theorem rawFlatPath_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p u) ∈ expDomain (I := I) g p) :
    pathLen (I := I) (rawFlatPath (I := I) g p u hdom) =
      ENNReal.ofReal ‖u‖ := by
  let γ : Real → M :=
    (framedExpMap (I := I) g p) ∘ fun t : Real => t • u
  let ρ : Real → Real := fun t => Real.smoothTransition (3 * t - 1)
  have hρ_mono : Monotone ρ := by
    apply Real.smoothTransition.monotone.comp
    intro a b hab
    dsimp only [ρ]
    linarith
  have hρ_cd : ContDiff Real ∞ ρ := by
    exact Real.smoothTransition.contDiff.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const)
  have hρ0 : ρ 0 = 0 := by
    dsimp only [ρ]
    rw [Real.smoothTransition.zero_of_nonpos]
    norm_num
  have hρ1 : ρ 1 = 1 := by
    dsimp only [ρ]
    rw [Real.smoothTransition.one_of_one_le]
    norm_num
  have hγC1 : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc 0 1) := by
    intro t ht
    have hline : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s : Real => s • u) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    exact (
      ((framedExp_mdiffAt (I := I) g p
          (by simpa only [map_smul] using hdom t ht)).comp t hline).of_le
        (by decide :
          (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffWithinAt
  rw [pathLen, rawFlatPath_ext]
  change Manifold.pathELength I (γ ∘ ρ) 0 1 = ENNReal.ofReal ‖u‖
  rw [Manifold.pathELength_comp_of_monotoneOn
    (I := I) (γ := γ) (f := ρ) (a := 0) (b := 1)
    zero_le_one (hρ_mono.monotoneOn (s := Set.Icc 0 1))
    (hρ_cd.differentiable (by norm_num)).differentiableOn
    (by simpa only [hρ0, hρ1] using
      hγC1.mdifferentiableOn one_ne_zero)]
  simpa only [hρ0, hρ1, γ] using rawRadial_len (I := I) g hEnorm p u hdom

end RawPath

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
