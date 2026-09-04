import DifferentialGeometry.Geometry.Comparison.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Density
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Tent
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeQuadraticStrong

set_option autoImplicit false

/-!
# Static endpoint Ricci integral estimate

This module supplies the static minimizing-geodesic estimate used by the
changing-distance argument.  It has no Ricci-flow hypothesis; completeness is
used only through the native minimizing-geodesic second-variation producer.
-/

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set intervalIntegral
open scoped Bundle ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private theorem deriv_ae_of_eqOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X] [CompleteSpace X]
    {T : Real} (hT : 0 < T) (u : timeH1 X T) (f : Real → X)
    (hf : ContDiff Real 1 f) (heq : EqOn u.toFun f (Icc (0 : Real) T)) :
    u.deriv =ᵐ[timeMeasure T] deriv f := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : Real) T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hmem] with t hu ht
  have htIcc : t ∈ Icc (0 : Real) T := ⟨ht.1.le, ht.2.le⟩
  have huniq := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt htIcc
  have hfAt : HasDerivAt f (deriv f t) t :=
    ((hf.differentiable (by norm_num)) t).hasDerivAt
  calc
    u.deriv t = derivWithin u.toFun (Icc (0 : Real) T) t :=
      (hu.derivWithin huniq).symm
    _ = derivWithin f (Icc (0 : Real) T) t :=
      derivWithin_congr heq (heq htIcc)
    _ = deriv f t := hfAt.hasDerivWithinAt.derivWithin huniq

omit [NeZero (Module.finrank Real E)] in
private theorem weight_integrable
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    {L : Real} (hL : 0 < L)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc 0 L))
    (e : Fin (Module.finrank Real E - 1) → SectionAlongCurve I M gamma)
    (heDiff : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I) gamma (e i).toFun t) t)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      covDerivAlong (I := I) g gamma (e i).toFun t = 0)
    (c : Real → Real) (hc : ContDiff Real ∞ c) :
    ∀ i, IntervalIntegrable
      (fun t ↦ indexFormIntegrand (I := I) g gamma
        (SectionAlongCurve.smulFun c (e i)).toFun
        (SectionAlongCurve.smulFun c (e i)).toFun t) volume 0 L := by
  intro i
  have hL0 : (0 : Real) ≤ L := hL.le
  have hc' : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have heTotal : ContinuousOn
      (fun t : Real ↦
        (TotalSpace.mk' E (gamma t) ((e i).toFun t) : TangentBundle I M))
      (Icc 0 L) :=
    sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) gamma (e i).toFun hgamma (fun t ht ↦ heDiff i t ht)
  have hA : ContinuousOn
      (fun t : Real ↦ g.inner (gamma t) ((e i).toFun t) ((e i).toFun t))
      (Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g heTotal heTotal
  have hUnique : UniqueMDiffOn 𝓘(Real, Real) (Icc (0 : Real) L) := by
    intro t ht
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hL) t ht
  have hTan := hgamma.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous
      (fun t : Real ↦ (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : MapsTo
      (fun t : Real ↦ (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
      (Icc (0 : Real) L) (TotalSpace.proj ⁻¹' Icc (0 : Real) L) := by
    intro t ht
    simpa using ht
  have hVel : ContinuousOn
      (fun t : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (gamma t)
          (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1) :
            TangentBundle I M)) (Icc (0 : Real) L) := by
    exact (hTan.comp hLift.continuousOn hMaps).congr (fun _ _ ↦ rfl)
  have hRiem : ContinuousOn
      (fun t : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (gamma t)
          (riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
            (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1)
            (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1))))
      (Icc 0 L) :=
    riemannOp_along_curve_continuousOn (I := I) g hgamma.continuousOn
      heTotal hVel hVel
  have hB : ContinuousOn
      (fun t : Real ↦ g.inner (gamma t)
        (riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
          (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1)
          (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1))
        ((e i).toFun t)) (Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g hRiem heTotal
  have hInt : IntervalIntegrable
      (fun t : Real ↦
        (deriv c t * deriv c t) *
            g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) -
          (c t * c t) * g.inner (gamma t)
            (riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
              (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1)
              (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1))
            ((e i).toFun t)) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hL0]
    exact ((hc'.mul hc').continuousOn.mul hA).sub
      ((hc.continuous.mul hc.continuous).continuousOn.mul hB)
  refine hInt.congr_ae ?_
  have hmem : ∀ᵐ t ∂(volume.restrict (uIoc (0 : Real) L)), t ∈ Ioo (0 : Real) L := by
    rw [uIoc_of_le hL0, ← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with t ht
  have ht' : t ∈ Icc (0 : Real) L := ⟨ht.1.le, ht.2.le⟩
  have hnhds : Icc (0 : Real) L ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  rw [mfderivWithin_of_mem_nhds hnhds]
  have hnabla : covDerivAlong (I := I) g gamma
      (SectionAlongCurve.smulFun c (e i)).toFun t =
      deriv c t • (e i).toFun t := by
    have hkey := covDerivAlong_smulFun (I := I) g gamma c (e i).toFun t
      (hc.differentiable (by simp) t) (heDiff i t ht')
    rwa [hpar i t ht', smul_zero, add_zero] at hkey
  unfold indexFormIntegrand
  simp only [SectionAlongCurve.smulFun_toFun]
  rw [hnabla]
  have hriem :
      riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) =
        c t • riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) := by
    have hsmul :
        riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t) =
          c t • riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t) :=
      (riemannOp (LeviCivita (I := I) g) (gamma t)).map_smul _ _
    rw [hsmul]
    simp only [ContinuousLinearMap.smul_apply]
  have hderivSq :
      g.inner (gamma t) (deriv c t • (e i).toFun t)
          (deriv c t • (e i).toFun t) =
        deriv c t ^ 2 * g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) := by
    calc
      g.inner (gamma t) (deriv c t • (e i).toFun t)
          (deriv c t • (e i).toFun t) =
          (deriv c t • g.inner (gamma t) ((e i).toFun t))
          (deriv c t • (e i).toFun t) := by
              exact congrArg (fun L ↦ L (deriv c t • (e i).toFun t))
                ((g.inner (gamma t)).map_smul (deriv c t) ((e i).toFun t))
      _ = deriv c t * g.inner (gamma t) ((e i).toFun t)
          (deriv c t • (e i).toFun t) := by
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      _ = deriv c t * (deriv c t *
          g.inner (gamma t) ((e i).toFun t) ((e i).toFun t)) := by
            congr 1
            simpa only [smul_eq_mul] using
              (g.inner (gamma t) ((e i).toFun t)).map_smul
                (deriv c t) ((e i).toFun t)
      _ = deriv c t ^ 2 *
          g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) := by ring
  have hcurvSq :
      g.inner (gamma t)
          (riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t)
            (mfderiv 𝓘(Real, Real) I gamma t 1)
            (mfderiv 𝓘(Real, Real) I gamma t 1))
          (c t • (e i).toFun t) =
        c t ^ 2 * g.inner (gamma t)
          (riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
            (mfderiv 𝓘(Real, Real) I gamma t 1)
            (mfderiv 𝓘(Real, Real) I gamma t 1)) ((e i).toFun t) := by
    rw [hriem]
    let Z : TangentSpace I (gamma t) :=
      riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
        (mfderiv 𝓘(Real, Real) I gamma t 1)
        (mfderiv 𝓘(Real, Real) I gamma t 1)
    change g.inner (gamma t) (c t • Z) (c t • (e i).toFun t) =
      c t ^ 2 * g.inner (gamma t) Z ((e i).toFun t)
    calc
      g.inner (gamma t) (c t • Z) (c t • (e i).toFun t) =
          (c t • g.inner (gamma t) Z) (c t • (e i).toFun t) := by
            exact congrArg (fun L ↦ L (c t • (e i).toFun t))
              ((g.inner (gamma t)).map_smul (c t) Z)
      _ = c t * g.inner (gamma t) Z (c t • (e i).toFun t) := by
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      _ = c t * (c t * g.inner (gamma t) Z ((e i).toFun t)) := by
            congr 1
            simpa only [smul_eq_mul] using
              (g.inner (gamma t) Z).map_smul (c t) ((e i).toFun t)
      _ = c t ^ 2 * g.inner (gamma t) Z ((e i).toFun t) := by ring
  convert congrArg₂ (fun x y : Real ↦ x - y) hderivSq.symm hcurvSq.symm using 1
  all_goals ring

omit [SigmaCompactSpace M] in
private theorem sum_index_weight
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    {L : Real} (uPrime : Real → E)
    (huPrime : ∀ t ∈ Icc (0 : Real) L,
      (mfderiv 𝓘(Real, Real) I gamma t 1 : E) = uPrime t)
    (hunit : ∀ t ∈ Icc (0 : Real) L,
      g.inner (gamma t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank Real E - 1) → SectionAlongCurve I M gamma)
    (heDiff : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I) gamma (e i).toFun t) t)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      covDerivAlong (I := I) g gamma (e i).toFun t = 0)
    (hON : ∀ t ∈ Icc (0 : Real) L, ∀ i j,
      g.inner (gamma t) ((e i).toFun t) ((e j).toFun t) =
        if i = j then 1 else 0)
    (hperp : ∀ t ∈ Icc (0 : Real) L, ∀ i,
      g.inner (gamma t) ((e i).toFun t) (uPrime t) = 0)
    (c : Real → Real) (hc : ContDiff Real ∞ c) :
    ∀ t ∈ Icc (0 : Real) L,
      (∑ i : Fin (Module.finrank Real E - 1),
        indexFormIntegrand (I := I) g gamma
          (SectionAlongCurve.smulFun c (e i)).toFun
          (SectionAlongCurve.smulFun c (e i)).toFun t) =
      (Module.finrank Real E - 1 : Real) * deriv c t ^ 2 -
        c t ^ 2 * ricciTensor (I := I) g (gamma t) (uPrime t) (uPrime t) := by
  classical
  intro t ht
  have hnabla (i : Fin (Module.finrank Real E - 1)) :
      covDerivAlong (I := I) g gamma
          (SectionAlongCurve.smulFun c (e i)).toFun t =
        deriv c t • (e i).toFun t := by
    have hkey := covDerivAlong_smulFun (I := I) g gamma c (e i).toFun t
      (hc.differentiable (by simp) t) (heDiff i t ht)
    rwa [hpar i t ht, smul_zero, add_zero] at hkey
  have hone (i : Fin (Module.finrank Real E - 1)) :
      g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) = 1 := by
    simpa using hON t ht i i
  have hi (i : Fin (Module.finrank Real E - 1)) :
      indexFormIntegrand (I := I) g gamma
          (SectionAlongCurve.smulFun c (e i)).toFun
          (SectionAlongCurve.smulFun c (e i)).toFun t =
        deriv c t ^ 2 - c t ^ 2 *
          g.inner (gamma t)
            (riemannOp (LeviCivita (I := I) g) (gamma t)
              ((e i).toFun t) (uPrime t) (uPrime t)) ((e i).toFun t) := by
    unfold indexFormIntegrand
    simp only [SectionAlongCurve.smulFun_toFun]
    have hvel : mfderiv 𝓘(Real, Real) I gamma t (1 : Real) = uPrime t :=
      huPrime t ht
    rw [hnabla i]
    have hriem :
        riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t)
            (uPrime t) (uPrime t) =
          c t • riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
            (uPrime t) (uPrime t) := by
      have hsmul :
          riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t) =
            c t • riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t) :=
        (riemannOp (LeviCivita (I := I) g) (gamma t)).map_smul _ _
      rw [hsmul]
      simp only [ContinuousLinearMap.smul_apply]
    have hderivSq :
        g.inner (gamma t) (deriv c t • (e i).toFun t)
            (deriv c t • (e i).toFun t) =
          deriv c t ^ 2 * g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) := by
      calc
        g.inner (gamma t) (deriv c t • (e i).toFun t)
            (deriv c t • (e i).toFun t) =
            (deriv c t • g.inner (gamma t) ((e i).toFun t))
            (deriv c t • (e i).toFun t) := by
                exact congrArg (fun L ↦ L (deriv c t • (e i).toFun t))
                  ((g.inner (gamma t)).map_smul (deriv c t) ((e i).toFun t))
        _ = deriv c t * g.inner (gamma t) ((e i).toFun t)
            (deriv c t • (e i).toFun t) := by
              rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
        _ = deriv c t * (deriv c t *
            g.inner (gamma t) ((e i).toFun t) ((e i).toFun t)) := by
              congr 1
              simpa only [smul_eq_mul] using
                (g.inner (gamma t) ((e i).toFun t)).map_smul
                  (deriv c t) ((e i).toFun t)
        _ = deriv c t ^ 2 *
            g.inner (gamma t) ((e i).toFun t) ((e i).toFun t) := by ring
    have hcurvSq :
        g.inner (gamma t)
            (riemannOp (LeviCivita (I := I) g) (gamma t) (c t • (e i).toFun t)
              (uPrime t) (uPrime t)) (c t • (e i).toFun t) =
          c t ^ 2 * g.inner (gamma t)
            (riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
              (uPrime t) (uPrime t)) ((e i).toFun t) := by
      rw [hriem]
      let Z : TangentSpace I (gamma t) :=
        riemannOp (LeviCivita (I := I) g) (gamma t) ((e i).toFun t)
          (uPrime t) (uPrime t)
      change g.inner (gamma t) (c t • Z) (c t • (e i).toFun t) =
        c t ^ 2 * g.inner (gamma t) Z ((e i).toFun t)
      calc
        g.inner (gamma t) (c t • Z) (c t • (e i).toFun t) =
            (c t • g.inner (gamma t) Z) (c t • (e i).toFun t) := by
              exact congrArg (fun L ↦ L (c t • (e i).toFun t))
                ((g.inner (gamma t)).map_smul (c t) Z)
        _ = c t * g.inner (gamma t) Z (c t • (e i).toFun t) := by
              rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
        _ = c t * (c t * g.inner (gamma t) Z ((e i).toFun t)) := by
              congr 1
              simpa only [smul_eq_mul] using
                (g.inner (gamma t) Z).map_smul (c t) ((e i).toFun t)
        _ = c t ^ 2 * g.inner (gamma t) Z ((e i).toFun t) := by ring
    rw [hvel, hderivSq, hcurvSq, hone i]
    ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hi i), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have htrace :
      (∑ i : Fin (Module.finrank Real E - 1),
        g.inner (gamma t)
          (riemannOp (LeviCivita (I := I) g) (gamma t)
            ((e i).toFun t) (uPrime t) (uPrime t)) ((e i).toFun t)) =
        ricciTensor (I := I) g (gamma t) (uPrime t) (uPrime t) :=
    ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame
      (I := I) g (gamma t) (uPrime t) (hunit t ht)
      (fun i ↦ (e i).toFun t) (hON t ht) (hperp t ht)
  rw [htrace, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : 1 ≤ Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [Nat.cast_sub hn, Nat.cast_one]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem smooth_index_nonneg
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (gamma : Real → M) {L : Real} (hL : 0 < L)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I) g gamma (Icc 0 L))
    (hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Icc 0 L) →
      eta 0 = gamma 0 → eta L = gamma L →
      arcLength (I := I) g gamma 0 L ≤ arcLength (I := I) g eta 0 L)
    (hunit : ∀ t ∈ Icc (0 : Real) L,
      g.inner (gamma t) (mfderiv 𝓘(Real, Real) I gamma t 1)
        (mfderiv 𝓘(Real, Real) I gamma t 1) = 1)
    (e : Fin (Module.finrank Real E - 1) → SectionAlongCurve I M gamma)
    (heDiff : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I) gamma (e i).toFun t) t)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : Real) L,
      covDerivAlong (I := I) g gamma (e i).toFun t = 0)
    (hON : ∀ t ∈ Icc (0 : Real) L, ∀ i j,
      g.inner (gamma t) ((e i).toFun t) ((e j).toFun t) =
        if i = j then 1 else 0)
    (hperp : ∀ t ∈ Icc (0 : Real) L, ∀ i,
      g.inner (gamma t) ((e i).toFun t)
        (mfderiv 𝓘(Real, Real) I gamma t 1) = 0)
    (heBundle : ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real ↦ TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma t) ((e i).toFun t)))
    (c : Real → Real) (hc : ContDiff Real ∞ c)
    (hc0 : c 0 = 0) (hcL : c L = 0) :
    0 ≤ ∫ t in (0 : Real)..L,
      (Module.finrank Real E - 1 : Real) * deriv c t ^ 2 -
        c t ^ 2 * ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) := by
  classical
  have hInt := weight_integrable (I := I) g gamma hL
    (hgamma.contMDiffOn.of_le (by simp))
    e heDiff hpar c hc
  have hEach : ∀ i : Fin (Module.finrank Real E - 1),
      0 ≤ indexForm (I := I) g gamma 0 L
        (SectionAlongCurve.smulFun c (e i)).toFun
        (SectionAlongCurve.smulFun c (e i)).toFun := by
    intro i
    have hcM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ c := by
      rwa [contMDiff_iff_contDiff]
    have hVBundle := contMDiff_smul_bundleField_perp (I := I)
      hgamma hcM (heBundle i)
    have hVperp : ∀ t ∈ Icc (0 : Real) L,
        g.inner (gamma t) ((SectionAlongCurve.smulFun c (e i)).toFun t)
          (mfderiv 𝓘(Real, Real) I gamma t 1) = 0 := by
      intro t ht
      rw [SectionAlongCurve.smulFun_toFun]
      have hleft :
          g.inner (gamma t) (c t • (e i).toFun t)
              (mfderiv 𝓘(Real, Real) I gamma t 1) =
            c t * g.inner (gamma t) ((e i).toFun t)
              (mfderiv 𝓘(Real, Real) I gamma t 1) := by
        calc
          g.inner (gamma t) (c t • (e i).toFun t)
              (mfderiv 𝓘(Real, Real) I gamma t 1) =
              (c t • g.inner (gamma t) ((e i).toFun t))
                (mfderiv 𝓘(Real, Real) I gamma t 1) := by
                  exact congrArg (fun L ↦ L (mfderiv 𝓘(Real, Real) I gamma t 1))
                    ((g.inner (gamma t)).map_smul (c t) ((e i).toFun t))
          _ = c t * g.inner (gamma t) ((e i).toFun t)
              (mfderiv 𝓘(Real, Real) I gamma t 1) := by
                rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hleft, hperp t ht i, mul_zero]
    refine indexForm_nonneg_of_minimising_geodesic (I := I)
      g gamma L (SectionAlongCurve.smulFun c (e i)).toFun hL
      hVBundle hgeo hmin hunit hVperp ?_ ?_
    · simp only [SectionAlongCurve.smulFun_toFun, hc0, zero_smul]
    · simp only [SectionAlongCurve.smulFun_toFun, hcL, zero_smul]
  have hSum : 0 ≤ ∑ i : Fin (Module.finrank Real E - 1),
      indexForm (I := I) g gamma 0 L
        (SectionAlongCurve.smulFun c (e i)).toFun
        (SectionAlongCurve.smulFun c (e i)).toFun :=
    Finset.sum_nonneg (fun i _ ↦ hEach i)
  have hEq : (∑ i : Fin (Module.finrank Real E - 1),
      indexForm (I := I) g gamma 0 L
        (SectionAlongCurve.smulFun c (e i)).toFun
        (SectionAlongCurve.smulFun c (e i)).toFun) =
      ∫ t in (0 : Real)..L,
        (Module.finrank Real E - 1 : Real) * deriv c t ^ 2 -
          c t ^ 2 * ricciTensor (I := I) g (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t 1)
            (mfderiv 𝓘(Real, Real) I gamma t 1) := by
    rw [show (∑ i : Fin (Module.finrank Real E - 1),
        indexForm (I := I) g gamma 0 L
          (SectionAlongCurve.smulFun c (e i)).toFun
          (SectionAlongCurve.smulFun c (e i)).toFun) =
      ∑ i : Fin (Module.finrank Real E - 1), ∫ t in (0 : Real)..L,
        indexFormIntegrand (I := I) g gamma
          (SectionAlongCurve.smulFun c (e i)).toFun
          (SectionAlongCurve.smulFun c (e i)).toFun t from rfl]
    rw [← intervalIntegral.integral_finset_sum (fun i _ ↦ hInt i)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact sum_index_weight (I := I) g gamma
      (fun s ↦ (mfderiv 𝓘(Real, Real) I gamma s 1 : E))
      (fun _ _ ↦ rfl) hunit e heDiff hpar hON hperp c hc t ht
  rwa [hEq] at hSum

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A static minimizing geodesic has controlled integrated Ricci curvature when
Ricci is bounded above only on its two endpoint segments. -/
theorem ricci_int_end_le
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (gamma : Real → M) {L r A : Real}
    (hr : 0 < r) (hL : 2 * r ≤ L)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I) g gamma (Icc 0 L))
    (hunit : ∀ t ∈ Icc (0 : Real) L,
      g.inner (gamma t) (mfderiv 𝓘(Real, Real) I gamma t 1)
        (mfderiv 𝓘(Real, Real) I gamma t 1) = 1)
    (hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Icc 0 L) →
      eta 0 = gamma 0 → eta L = gamma L →
      arcLength (I := I) g gamma 0 L ≤ arcLength (I := I) g eta 0 L)
    (hRic : ∀ t ∈ Icc (0 : Real) L, t < r ∨ L - r < t →
      ricciTensor (I := I) g (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t 1)
        (mfderiv 𝓘(Real, Real) I gamma t 1) ≤ A) :
    (∫ t in (0 : Real)..L, ricciTensor (I := I) g (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t 1)
      (mfderiv 𝓘(Real, Real) I gamma t 1)) ≤
      (Module.finrank Real E - 1 : Real) * (2 / r) + A * (4 * r / 3) := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hL0 : (0 : Real) ≤ L := hLpos.le
  let velocity : Real → E :=
    fun t ↦ (mfderiv 𝓘(Real, Real) I gamma t 1 : E)
  let R : Real → Real := fun t ↦
    ricciTensor (I := I) g (gamma t) (velocity t) (velocity t)
  obtain ⟨e, heDiff, hpar, hON, hperp, heBundle⟩ :=
    exists_parallel_perp_frame (I := I) g gamma hgamma hLpos hgeo
      (hunit 0 ⟨le_rfl, hL0⟩)
  let q : timeH1 Real L := timeH1.trapezoid L r
  obtain ⟨w, f, hf, hwf, hf0, hfL, _hfNear0, _hfNearL, hw, hwD⟩ :=
    exists_flat_smooth hLpos q
  have hq0 : q.toFun 0 = 0 := by
    dsimp only [q]
    rw [timeH1.trap_left hr hL ⟨le_rfl, hr.le⟩]
    simp only [zero_div]
  have hqL : q.toFun L = 0 := by
    dsimp only [q]
    rw [timeH1.trap_right hr hL ⟨sub_le_self L hr.le, le_rfl⟩]
    simp only [sub_self, zero_div]
  have hSmoothNonneg : ∀ n,
      0 ≤ ∫ t in (0 : Real)..L,
        (Module.finrank Real E - 1 : Real) * deriv (f n) t ^ 2 -
          f n t ^ 2 * R t := by
    intro n
    simpa only [R, velocity] using
      smooth_index_nonneg (I := I) g gamma hLpos hgamma hgeo hmin
        hunit e heDiff hpar hON hperp heBundle (f n) (hf n)
        ((hf0 n).trans hq0) ((hfL n).trans hqL)
  -- Use the within derivative to obtain a continuous representative of the
  -- scalar Ricci coefficient on the compact parameter interval.
  let velocityW : Real → E := fun t ↦
    (mfderivWithin 𝓘(Real, Real) I gamma (Icc (0 : Real) L) t 1 : E)
  let RW : Real → Real := fun t ↦
    ricciTensor (I := I) g (gamma t) (velocityW t) (velocityW t)
  have hUnique : UniqueMDiffOn 𝓘(Real, Real) (Icc (0 : Real) L) := by
    intro t ht
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hLpos) t ht
  have hTan := hgamma.contMDiffOn.continuousOn_tangentMapWithin
    (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))) hUnique
  have hLift : Continuous
      (fun t : Real ↦ (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(Real, Real)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hMaps : MapsTo
      (fun t : Real ↦ (⟨t, (1 : Real)⟩ : TangentBundle 𝓘(Real, Real) Real))
      (Icc (0 : Real) L) (TotalSpace.proj ⁻¹' Icc (0 : Real) L) := by
    intro t ht
    simpa using ht
  have hVelW : ContinuousOn
      (fun t : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (gamma t)
          (velocityW t) : TangentBundle I M)) (Icc (0 : Real) L) := by
    exact (hTan.comp hLift.continuousOn hMaps).congr (fun _ _ ↦ rfl)
  have hRicSec : ContinuousOn
      (fun t : Real ↦ TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M ↦ TangentSpace I x →L[Real]
          TangentSpace I x →L[Real] Real)
        (gamma t) (ricciTensor (I := I) g (gamma t))) (Icc (0 : Real) L) := by
    exact (ricciTensor_contMDiff (I := I) g).continuous.comp_continuousOn
      hgamma.continuous.continuousOn
  have hScalarTotal : ContinuousOn
      (fun t : Real ↦ TotalSpace.mk' Real (E := fun _ : M ↦ Real)
        (gamma t) (RW t)) (Icc (0 : Real) L) := by
    exact ContinuousOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := Real)
      (b := gamma) hRicSec hVelW hVelW
  have hRW : ContinuousOn RW (Icc (0 : Real) L) := by
    have hproj : Continuous
        (fun p : TotalSpace Real (fun _ : M ↦ Real) ↦ p.2) :=
      continuous_snd.comp (Trivial.homeomorphProd M Real).continuous
    exact hproj.comp_continuousOn hScalarTotal
  have hRWeq : ∀ᵐ t ∂(timeMeasure L), RW t = R t := by
    have hmem : ∀ᵐ t ∂(timeMeasure L), t ∈ Ioo (0 : Real) L := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with t ht
    have hnhds : Icc (0 : Real) L ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    dsimp only [RW, R, velocityW, velocity]
    rw [mfderivWithin_of_mem_nhds hnhds]
  have hRWeqIcc : ∀ᵐ t ∂(volume.restrict (Icc (0 : Real) L)), RW t = R t := by
    simpa only [timeMeasure] using hRWeq
  have hRWeqIoc : ∀ᵐ t ∂(volume.restrict (uIoc (0 : Real) L)), RW t = R t := by
    rw [uIoc_of_le hL0, restrict_Ioc_eq_restrict_Icc]
    exact hRWeqIcc
  have hRInt : IntervalIntegrable R volume 0 L := by
    have hRWInt : IntervalIntegrable RW volume 0 L := by
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le hL0]
    exact hRWInt.congr_ae hRWeqIoc
  let Op : Real → Real →L[Real] Real :=
    fun t ↦ RW t • ContinuousLinearMap.id Real Real
  have hOpMeas : AEStronglyMeasurable Op (timeMeasure L) := by
    unfold timeMeasure
    exact (hRW.smul continuousOn_const).aestronglyMeasurable measurableSet_Icc
  obtain ⟨C0, hC0⟩ := isCompact_Icc.bddAbove_image hRW.norm
  let C : NNReal := ⟨max C0 0, le_max_right _ _⟩
  have hOpBound : ∀ᵐ t ∂(timeMeasure L), ‖Op t‖ ≤ (C : Real) := by
    have hmem : ∀ᵐ t ∂(timeMeasure L), t ∈ Icc (0 : Real) L :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with t ht
    have hle : ‖RW t‖ ≤ C0 := hC0 ⟨t, ht, rfl⟩
    dsimp only [Op, C]
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact hle.trans (le_max_left _ _)
  have hOpConv : ∀ delta : Real, 0 < delta → ∀ᶠ n : Nat in atTop,
      ∀ᵐ t ∂(timeMeasure L), ‖Op t - Op t‖ ≤ delta := by
    intro delta hdelta
    filter_upwards [] with n
    filter_upwards [] with t
    simp only [sub_self, norm_zero, hdelta.le]
  have hwL2 : Tendsto (fun n ↦ timeH1.toTimeL2 Real L (w n)) atTop
      (𝓝 (timeH1.toTimeL2 Real L q)) :=
    (timeH1.toTimeL2 Real L).continuous.continuousAt.tendsto.comp hw
  have hQuad := timeQuad_strong (fun _ ↦ Op) Op (fun _ ↦ hOpMeas)
    hOpMeas (fun _ ↦ C) C (fun _ ↦ hOpBound) hOpBound hOpConv
    (fun n ↦ timeH1.toTimeL2 Real L (w n))
    (timeH1.toTimeL2 Real L q) hwL2
  have hQuadRep (n : Nat) :
      timeQuad Op hOpMeas C hOpBound (timeH1.toTimeL2 Real L (w n)) =
        ∫ t in (0 : Real)..L, f n t ^ 2 * R t := by
    rw [timeQuad_eq_integral Op hOpMeas C hOpBound hL0]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hL0, restrict_Ioc_eq_restrict_Icc]
    have hcoe : ∀ᵐ t ∂(volume.restrict (Icc (0 : Real) L)),
        timeH1.toTimeL2 Real L (w n) t = (w n).toFun t := by
      simpa only [timeH1.toTimeL2_apply, timeMeasure] using
        coeFn_ofContinuousOn (w n).continuousOn_toFun
    have hmem : ∀ᵐ t ∂(volume.restrict (Icc (0 : Real) L)),
        t ∈ Icc (0 : Real) L :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hcoe, hRWeqIcc, hmem] with t hwt hrt ht
    rw [hwt, hwf n ht]
    dsimp only [Op]
    rw [hrt]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    ring
  have hQuadLim :
      timeQuad Op hOpMeas C hOpBound (timeH1.toTimeL2 Real L q) =
        ∫ t in (0 : Real)..L, q.toFun t ^ 2 * R t := by
    rw [timeQuad_eq_integral Op hOpMeas C hOpBound hL0]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hL0, restrict_Ioc_eq_restrict_Icc]
    have hcoe : ∀ᵐ t ∂(volume.restrict (Icc (0 : Real) L)),
        timeH1.toTimeL2 Real L q t = q.toFun t := by
      simpa only [timeH1.toTimeL2_apply, timeMeasure] using
        coeFn_ofContinuousOn q.continuousOn_toFun
    filter_upwards [hcoe, hRWeqIcc] with t hqt hrt
    rw [hqt]
    dsimp only [Op]
    rw [hrt]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    ring
  have hCurvLim : Tendsto
      (fun n ↦ ∫ t in (0 : Real)..L, f n t ^ 2 * R t) atTop
      (𝓝 (∫ t in (0 : Real)..L, q.toFun t ^ 2 * R t)) := by
    simpa only [hQuadRep, hQuadLim] using hQuad
  have hDerivRep (n : Nat) :
      (∫ t in (0 : Real)..L, deriv (f n) t ^ 2) = ‖(w n).deriv‖ ^ 2 := by
    rw [norm_sq_eq_integral, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL0]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hL0, restrict_Ioc_eq_restrict_Icc]
    have hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : Real) L)),
        (w n).deriv t = deriv (f n) t := by
      simpa only [timeMeasure] using
        deriv_ae_of_eqOn hLpos (w n) (f n)
          ((hf n).of_le (by simp)) (hwf n)
    filter_upwards [hae] with t ht
    rw [ht, Real.norm_eq_abs, sq_abs]
  have hDerivLim : Tendsto
      (fun n ↦ ∫ t in (0 : Real)..L, deriv (f n) t ^ 2) atTop
      (𝓝 (2 / r)) := by
    have hnorm := hwD.norm.pow 2
    rw [timeH1.trap_deriv_sq hr hL] at hnorm
    simpa only [hDerivRep] using hnorm
  have hLimitNonneg :
      0 ≤ (Module.finrank Real E - 1 : Real) * (2 / r) -
        ∫ t in (0 : Real)..L, q.toFun t ^ 2 * R t := by
    have hCombined :=
      (hDerivLim.const_mul (Module.finrank Real E - 1 : Real)).sub hCurvLim
    have hevent : ∀ᶠ n in atTop,
        0 ≤ (Module.finrank Real E - 1 : Real) *
          (∫ t in (0 : Real)..L, deriv (f n) t ^ 2) -
          ∫ t in (0 : Real)..L, f n t ^ 2 * R t := by
      filter_upwards [] with n
      have hDerivInt : IntervalIntegrable
          (fun t : Real ↦ deriv (f n) t ^ 2) volume 0 L := by
        exact (((hf n).continuous_deriv (by simp)).pow 2).intervalIntegrable
          (μ := volume) 0 L
      have hCurvInt : IntervalIntegrable
          (fun t : Real ↦ f n t ^ 2 * R t) volume 0 L := by
        simpa only [mul_comm] using
          hRInt.mul_continuousOn ((hf n).continuous.pow 2).continuousOn
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hDerivInt.const_mul _) hCurvInt]
      exact hSmoothNonneg n
    exact ge_of_tendsto hCombined hevent
  have hWeighted :
      (∫ t in (0 : Real)..L, q.toFun t ^ 2 * R t) ≤
        (Module.finrank Real E - 1 : Real) * (2 / r) := by
    linarith
  let defect : Real → Real := fun t ↦ 1 - q.toFun t ^ 2
  have hDefectCont : ContinuousOn defect (Icc (0 : Real) L) :=
    continuousOn_const.sub (q.continuousOn_toFun.pow 2)
  have hDefectRInt : IntervalIntegrable (fun t ↦ defect t * R t) volume 0 L := by
    have hRWInt : IntervalIntegrable (fun t ↦ defect t * RW t) volume 0 L := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hL0]
      exact hDefectCont.mul hRW
    refine hRWInt.congr_ae ?_
    filter_upwards [hRWeqIoc] with t ht
    rw [ht]
  have hDefectInt : IntervalIntegrable defect volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hL0]
  have hDefectBound :
      (∫ t in (0 : Real)..L, defect t * R t) ≤
        A * (4 * r / 3) := by
    have hpoint : ∀ᵐ t ∂(volume.restrict (uIoc (0 : Real) L)),
        defect t * R t ≤ A * defect t := by
      have hmem : ∀ᵐ t ∂(volume.restrict (uIoc (0 : Real) L)),
          t ∈ Ioo (0 : Real) L := by
        rw [uIoc_of_le hL0, ← restrict_Ioo_eq_restrict_Ioc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hmem] with t ht
      have htIcc : t ∈ Icc (0 : Real) L := ⟨ht.1.le, ht.2.le⟩
      by_cases hleft : t < r
      · have hRt : R t ≤ A := hRic t htIcc (Or.inl hleft)
        have hq : q.toFun t = t / r :=
          timeH1.trap_left hr hL ⟨ht.1.le, hleft.le⟩
        have hd : 0 ≤ defect t := by
          dsimp only [defect]
          rw [hq]
          have hnonneg : 0 ≤ t / r := div_nonneg ht.1.le hr.le
          have hone : t / r ≤ 1 := (div_le_one hr).2 hleft.le
          nlinarith
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hRt hd
      · by_cases hright : L - r < t
        · have hRt : R t ≤ A := hRic t htIcc (Or.inr hright)
          have hq : q.toFun t = (L - t) / r :=
            timeH1.trap_right hr hL ⟨hright.le, ht.2.le⟩
          have hd : 0 ≤ defect t := by
            dsimp only [defect]
            rw [hq]
            have hnonneg : 0 ≤ (L - t) / r := div_nonneg (sub_nonneg.mpr ht.2.le) hr.le
            have hone : (L - t) / r ≤ 1 := (div_le_one hr).2 (by linarith)
            nlinarith
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hRt hd
        · have hq : q.toFun t = 1 :=
            timeH1.trap_mid hr hL ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
          simp only [defect, hq, one_pow, sub_self, zero_mul, mul_zero]
          exact le_rfl
    calc
      (∫ t in (0 : Real)..L, defect t * R t) ≤
          ∫ t in (0 : Real)..L, A * defect t :=
        intervalIntegral.integral_mono_ae_restrict hL0 hDefectRInt
          (hDefectInt.const_mul A) (by
            simpa only [uIoc_of_le hL0, restrict_Ioc_eq_restrict_Icc] using hpoint)
      _ = A * (∫ t in (0 : Real)..L, defect t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = A * (4 * r / 3) := by
        rw [show (∫ t in (0 : Real)..L, defect t) = 4 * r / 3 by
          exact timeH1.trap_defect_int hr hL]
  have hSplit :
      (∫ t in (0 : Real)..L, R t) =
        (∫ t in (0 : Real)..L, q.toFun t ^ 2 * R t) +
          ∫ t in (0 : Real)..L, defect t * R t := by
    have hWeightedInt : IntervalIntegrable
        (fun t ↦ q.toFun t ^ 2 * R t) volume 0 L := by
      have hqCont : ContinuousOn (fun t ↦ q.toFun t ^ 2)
          (uIcc (0 : Real) L) := by
        simpa only [uIcc_of_le hL0] using q.continuousOn_toFun.pow 2
      simpa only [mul_comm] using
        hRInt.mul_continuousOn hqCont
    rw [← intervalIntegral.integral_add hWeightedInt hDefectRInt]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [defect]
    ring
  change (∫ t in (0 : Real)..L, R t) ≤ _
  rw [hSplit]
  linarith

end DifferentialGeometry.PDE.RicciFlow

end
