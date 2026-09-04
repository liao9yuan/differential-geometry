import DifferentialGeometry.Geometry.Comparison.Volume.BishopRawDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.BishopPolarFramed
import DifferentialGeometry.Geometry.Comparison.Volume.RawBallPolarEq
import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentMeasure

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [eNorm : NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private lemma gON_li
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {v : Fin (Module.finrank ℝ E - 1) → E}
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  have hpair := congrArg (fun z : E => g.inner p z (v j)) ha
  change g.inner p (∑ i, a i • v i) (v j) = g.inner p 0 (v j) at hpair
  rw [map_sum, ContinuousLinearMap.sum_apply, map_zero,
    ContinuousLinearMap.zero_apply] at hpair
  rw [Finset.sum_eq_single j] at hpair
  · have hsmul := congrArg (fun A : E →L[ℝ] ℝ => A (v j))
      ((g.inner p).map_smul (a j) (v j))
    calc
      a j = a j * 1 := (mul_one _).symm
      _ = a j * g.inner p (v j) (v j) := by rw [hON j j, if_pos rfl]
      _ = g.inner p (a j • v j) (v j) := by
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hsmul.symm
      _ = 0 := hpair
  · intro i _ hij
    have hsmul := congrArg (fun A : E →L[ℝ] ℝ => A (v j))
      ((g.inner p).map_smul (a i) (v i))
    calc
      g.inner p (a i • v i) (v j) = a i * g.inner p (v i) (v j) := by
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hsmul
      _ = a i * 0 := by rw [hON i j, if_neg hij]
      _ = 0 := mul_zero _
  · simp

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma raw_basis_density
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (B B' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    curveDensity (I := I) g (radialCurve (I := I) g p v)
        (fun i => radialJacobiField (I := I) g p v (B' i)) 1 =
      |B.det B'| *
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (B i)) 1 := by
  classical
  let F : E → M := fun w =>
    expMap (I := I) g p (show TangentSpace I p from w)
  let L : E →L[ℝ] TangentSpace I (radialCurve (I := I) g p v 1) :=
    mfderiv 𝓘(ℝ, E) I F v
  let C : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := B.toMatrix B'
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      B' i = ∑ k, C k i • B k := by
    simpa only [C, Module.Basis.toMatrix_apply] using
      (B.sum_repr (B' i)).symm
  have hcol (w : E) :
      radialJacobiField (I := I) g p v w 1 = L w := by
    simpa only [radialJacobiField, radialCurve, one_smul, F, L] using
      radial_jacobi_dom (I := I) g p v w hv
  have hjac : ∀ i,
      radialJacobiField (I := I) g p v (B' i) 1 =
        ∑ k, C k i • radialJacobiField (I := I) g p v (B k) 1 := by
    intro i
    rw [hcol, hcoord i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol]
    exact L.map_smul (C k i) (B k)
  simpa only [C, Module.Basis.det_apply] using
    curveDensity_recomb (I := I) g
      (radialCurve (I := I) g p v)
      (fun i => radialJacobiField (I := I) g p v (B i))
      (fun i => radialJacobiField (I := I) g p v (B' i))
      1 C hjac

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Converts raw-exponential Jacobian integrals to normal-frame Euclidean
coordinates without a global completeness hypothesis. -/
theorem rawJac_normal_int
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : MeasurableSet K)
    (hKdom : K ⊆ expDomain (I := I) g p) :
    (∫⁻ v in K,
        ENNReal.ofReal
          (mapJacDensity (I := I) g
            (fun b : E => expMap (I := I) g p
              (show TangentSpace I p from b)) v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let F : E → M := fun v =>
    expMap (I := I) g p (show TangentSpace I p from v)
  let Dn : E → ℝ := fun v =>
    curveDensity (I := I) g (radialCurve (I := I) g p v)
      (fun i => radialJacobiField (I := I) g p v (b' i)) 1
  have hD (v : E) (hv : v ∈ K) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (mapJacDensity (I := I) g F v) =
        ENNReal.ofReal (Dn v) := by
    have hraw : mapJacDensity (I := I) g F v =
        curveDensity (I := I) g (radialCurve (I := I) g p v)
          (fun i => radialJacobiField (I := I) g p v (b i)) 1 := by
      simpa only [F, b, radialCurve, radialJacobiField] using
        raw_exp_density (I := I) g p v (hKdom hv)
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    rw [hraw]
    exact (raw_basis_density (I := I) g p v (hKdom hv) b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂b.addHaar := by rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              setLIntegral_smul_measure]
            exact
              (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            exact setLIntegral_congr_fun hK hD
  have hbmap :
      (stdOrthonormalBasis ℝ E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g p
        ((stdOrthonormalBasis ℝ E) i) = normalBasis (I := I) g p i
    exact normalFrame_basis (I := I) g p i
  have hmap : Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis ℝ E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis ℝ E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis ℝ E).toBasis.map
          L.toLinearEquiv).addHaar :=
            Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  simpa only [Dn, L, b'] using
    (hmp.setLIntegral_comp_preimage_emb
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun v => ENNReal.ofReal (Dn v)) K).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private lemma rawSegInt_down
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {u : E} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hraw : b • u ∈ rawSegInt (I := I) g p) :
    a • u ∈ rawSegInt (I := I) g p := by
  rcases hraw with ⟨c, hc, hcraw⟩
  refine ⟨c * b / a, ?_, ?_⟩
  · apply (lt_div_iff₀ ha).mpr
    have hcb : b < c * b := by
      simpa only [one_mul, mul_one, mul_comm] using
        (mul_lt_mul_of_pos_right hc hb)
    nlinarith
  · rw [smul_smul, div_mul_cancel₀ (c * b) ha.ne']
    simpa only [smul_smul] using hcraw

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma raw_min_seg
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hraw : L • u ∈ rawSeg (I := I) g p) :
    ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g (radialCurve (I := I) g p u) 0 L ≤
        arcLength (I := I) g η 0 L := by
  intro η hη hη0 hηL
  have hradLen : arcLength (I := I) g
      (radialCurve (I := I) g p u) 0 L = L := by
    unfold arcLength
    calc
      ∫ t in (0 : ℝ)..L, Real.sqrt
          (g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) =
          ∫ _t in (0 : ℝ)..L, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Icc (0 : ℝ) L := by
              simpa only [uIcc_of_le hL.le] using ht
            have hspeed := rawSpeed_sq (I := I) g p u t ht'.1
              (fun s hs => hdom s ⟨hs.1, hs.2.trans ht'.2⟩)
            change Real.sqrt
                (g.inner (radialCurve (I := I) g p u t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) = 1
            rw [hspeed, hunit, Real.sqrt_one]
      _ = L := by simp
  have hdist := Geodesic.riemannianEDist_le_arcLength
    (I := I) g hL.le hη (fun t _ =>
      hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))
  have hdist' : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from L • u)) ≤
      ENNReal.ofReal (arcLength (I := I) g η 0 L) := by
    simpa only [hη0, hηL] using hdist
  have hnorm : Real.sqrt (g.inner p
      (show TangentSpace I p from L • u)
      (show TangentSpace I p from L • u)) = L := by
    simpa only [hunit, Real.sqrt_one, mul_one] using
      sqrt_gInner_smul_self (I := I) g p hL.le
        (show TangentSpace I p from u)
  have hdistL : ENNReal.ofReal L ≤
      ENNReal.ofReal (arcLength (I := I) g η 0 L) := by
    change ENNReal.ofReal (Real.sqrt (g.inner p
      (show TangentSpace I p from L • u)
      (show TangentSpace I p from L • u))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from L • u)) at hraw
    rw [hnorm] at hraw
    exact hraw.le.trans hdist'
  have harc : 0 ≤ arcLength (I := I) g η 0 L := by
    unfold arcLength
    apply intervalIntegral.integral_nonneg hL.le
    intro t _
    exact Real.sqrt_nonneg _
  rw [hradLen]
  exact (ENNReal.ofReal_le_ofReal_iff harc).mp hdistL

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [SigmaCompactSpace M] in
/-- Along a raw radial segment with a local Ricci lower bound, the transverse
Jacobi density ratio to the corresponding hyperbolic model is nonincreasing. -/
theorem raw_ratio_anti_q
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (q a : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) = a ^ 2)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p
          (show TangentSpace I p from b) : M)) (t • u)))
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hypDensity (q * a) (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  classical
  let γ := radialCurve (I := I) g p u
  let V : Fin (Module.finrank ℝ E - 1) → ∀ t, TangentSpace I (γ t) :=
    fun i => radialJacobiField (I := I) g p u (v i)
  have hv : LinearIndependent ℝ v := gON_li (I := I) g p hON
  have hγcc : ∀ t ∈ Icc (0 : ℝ) L,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => s • u) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := expMap_contMDiffAt (I := I) g p (hdom t ht)
    simpa only [γ, radialCurve] using
      (hexp.comp t hline).of_le
        (by decide : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  have hγ : ∀ t ∈ Ioo (0 : ℝ) L,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t :=
    fun t ht => hγcc t ⟨ht.1.le, ht.2.le⟩
  have hspeed' : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = a ^ 2 := by
    simpa only [γ] using hspeed
  have hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) L) := by
    intro t ht
    simpa only [γ, radialCurve] using
      raw_radial_geo_at (I := I) g p
        (show TangentSpace I p from u) (hdom t ht)
  have hreg (i : Fin (Module.finrank ℝ E - 1)) :
      (∀ t ∈ Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t) ∧
      ∀ t ∈ Icc (0 : ℝ) L,
        DifferentiableAt ℝ
          (chartRepAt (I := I) γ
            (fun s => covDerivAlong (I := I) g γ (V i) s) t) t := by
    constructor <;> intro t ht
    · simpa only [γ, V, radialCurve, radialJacobiField] using
        (radial_jacobi_reg (I := I) g p u (v i) t (hdom t ht)).1
    · simpa only [γ, V, radialCurve, radialJacobiField] using
        (radial_jacobi_reg (I := I) g p u (v i) t (hdom t ht)).2
  have hJac : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    simpa only [γ, V, radialCurve, radialJacobiField] using
      (radial_jacobi_on (I := I) g p u (v i) hdom).2.2 t ht
  have hzero (i : Fin (Module.finrank ℝ E - 1)) : V i 0 = 0 := by
    exact radialJacobi_zero (I := I) g p u (v i)
  have hD0 (i : Fin (Module.finrank ℝ E - 1)) :
      g.inner (γ 0) (curveVelocity (I := I) γ 0)
        (covDerivAlong (I := I) g γ (V i) 0) = 0 := by
    have hγ0 : γ 0 = p := by
      simp only [γ, radialCurve, zero_smul]
      exact expMap_zero (I := I) g p
    have hvel0 : curveVelocity (I := I) γ 0 =
        (show TangentSpace I p from u) := by
      simpa only [γ, radialCurve, curveVelocity] using
        radialCurve_launch_velocity (I := I) g p u
    have hDJ0 :
        (covDerivAlong (I := I) g γ (V i) 0 : E) = v i := by
      simpa only [γ, V, radialCurve, radialJacobiField] using
        radial_jacobi_d0 (I := I) g p u (v i)
    rw [hγ0]
    change g.inner p (curveVelocity (I := I) γ 0)
      (covDerivAlong (I := I) g γ (V i) 0 : E) = 0
    rw [hvel0, hDJ0]
    exact hperp i
  have hperpData (i : Fin (Module.finrank ℝ E - 1)) :=
    jacobi_perp_of_init (I := I) g γ (V i) hL hγcc hgeo
      (hreg i).1 (hreg i).2 (fun t ht => hJac t ht i) (hzero i) (hD0 i)
  have hVperp : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    exact (hperpData i).1 t ⟨ht.1.le, ht.2.le⟩
  have hDVperp : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    exact (hperpData i).2 t ⟨ht.1.le, ht.2.le⟩
  have hVdiff : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t :=
    fun t ht i => (hreg i).1 t ⟨ht.1.le, ht.2.le⟩
  have hDVdiff : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t :=
    fun t ht i => (hreg i).2 t ⟨ht.1.le, ht.2.le⟩
  have hLI : ∀ t ∈ Ioo (0 : ℝ) L,
      LinearIndependent ℝ fun i => V i t := by
    intro t ht
    exact radialJacobi_li_of (I := I) g p u hv ht.1.ne'
      (hdom t ⟨ht.1.le, ht.2.le⟩)
      (hinj t ht)
  have hW : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0 := by
    intro t ht i j
    exact wronskian_zero_Ioo (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ (V i) (V j) hγcc (hreg i).1 (hreg j).1 (hreg i).2 (hreg j).2
      (fun s hs => hJac s hs i) (fun s hs => hJac s hs j)
      (hzero i) (hzero j) t ⟨ht.1.le, ht.2.le⟩
  have hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hypDensity (q * a) (Module.finrank ℝ E - 1) t := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    have hpole : Tendsto
        (fun t => curveDensity (I := I) g γ V t /
          hypDensity (q * a) (Module.finrank ℝ E - 1) t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [γ, V, Fintype.card_fin] using
        radialRatio_pole (I := I) g p u v (q * a) hON
    have hev := (tendsto_order.1 hpole).1 (1 / 2) (by norm_num)
    exact hev.mono fun _ h => h.le
  have hmean := curveMean_le_on (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V q a L hq ha (by simp) hd hγ hspeed' hVperp hDVperp
    hVdiff hDVdiff hLI hW hJac (by
      intro t ht
      simpa only [γ] using hRic t ht) (by
        simpa only [γ, V] using hRatioLower)
  simpa only [γ, V] using
    curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V (q * a) L (Module.finrank ℝ E - 1) (mul_nonneg hq ha.le)
      hγ hVdiff hLI hW hmean

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma raw_ratio_ray
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) (q L : ℝ)
    (hq : 0 ≤ q) (hL : 0 < L)
    (hunit : g.inner p u u = 1)
    (hraw : L • u ∈ rawSeg (I := I) g p)
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hypDensity q (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  have hLdom : (show TangentSpace I p from L • u) ∈ expDomain (I := I) g p :=
    rawSeg_mem_dom (I := I) g p hraw
  have hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p := by
    intro t ht
    have hfrac : t / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
    have hscale := Geodesic.smul_mem_expDomain (I := I) g p
      (show TangentSpace I p from L • u) hLdom hfrac
    change (show TangentSpace I p from (t / L) • (L • u)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, div_mul_cancel₀ t hL.ne', one_smul] using hscale
  have hspeed : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) = 1 ^ 2 := by
    intro t ht
    rw [rawSpeed_sq (I := I) g p u t ht.1.le
      (fun s hs => hdom s ⟨hs.1, hs.2.trans ht.2.le⟩), hunit]
    norm_num
  have hmin := raw_min_seg (I := I) g hEnorm p u hunit L hL hdom hraw
  simpa only [mul_one] using
    raw_ratio_anti_q (I := I) g p u q 1 hq one_pos L hL hdom hspeed
      (fun t ht => raw_exp_inj_of_min (I := I) g p u hunit L hL hdom hmin ht)
      v hON hperp hd hRic

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma rawDn_cont
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) (T : Set E)
    (hTdom : ∀ w ∈ T,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p) :
    ContinuousOn (fun w : E =>
      curveDensity (I := I) g
        (radialCurve (I := I) g p
          (normalFrame (I := I) (E := E) g p w))
        (fun i => radialJacobiField (I := I) g p
          (normalFrame (I := I) (E := E) g p w)
          (normalBasis (I := I) g p i)) 1)
      T := by
  classical
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  have hTLdom : ∀ w ∈ T, L w ∈ expDomain (I := I) g p := by
    intro w hw
    simpa only [L] using hTdom w hw
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F (expDomain (I := I) g p) := by
    simpa only [F] using (expMap_contMDiffOn (I := I) g p).of_le (by norm_num)
  have hmap : ContinuousOn (mapJacDensity (I := I) g F)
      (expDomain (I := I) g p) :=
    mapJac_contOn (I := I) g (isOpen_expDomain (I := I) g p) hF
  have hmapL : ContinuousOn (fun w => mapJacDensity (I := I) g F (L w)) T :=
    hmap.comp L.continuous.continuousOn (fun w hw => hTLdom w hw)
  have heq (w : E) (hw : w ∈ T) :
      curveDensity (I := I) g (radialCurve (I := I) g p (L w))
          (fun i => radialJacobiField (I := I) g p (L w) (B i)) 1 =
        |(chartModelBasis E).det B| * mapJacDensity (I := I) g F (L w) := by
    rw [raw_basis_density (I := I) g p (L w) (hTLdom w hw)
      (chartModelBasis E) B]
    congr 1
    symm
    simpa only [F, radialCurve, radialJacobiField] using
      raw_exp_density (I := I) g p (L w) (hTLdom w hw)
  have hcont : ContinuousOn (fun w : E =>
      |(chartModelBasis E).det B| * mapJacDensity (I := I) g F (L w)) T :=
    continuousOn_const.mul hmapL
  change ContinuousOn (fun w : E =>
    curveDensity (I := I) g (radialCurve (I := I) g p (L w))
      (fun i => radialJacobiField (I := I) g p (L w) (B i)) 1) T
  exact hcont.congr heq

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma rawBall_normal
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hR : 0 < R) (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀)))
    (K : Set E)
    (hK : K = rawSegInt (I := I) g p ∩ gBall (I := I) g p R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹'
          K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  have hKmeas : MeasurableSet K := by
    rw [hK]
    exact rawSegInt_ball_meas (I := I) g hEnorm p hR hRR₀ hcpt
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    rw [hK] at hv
    exact rawSeg_mem_dom (I := I) g p
      (rawSegInt_sub (I := I) g hEnorm p hv.1)
  have hjac (v : E) (hv : v ∈ K) :
      mapJacDensity (I := I) g F v =
        curveDensity (I := I) g
          (fun t : ℝ => expMap (I := I) g p
            (show TangentSpace I p from t • v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
              expMap (I := I) g p
                (show TangentSpace I p from
                  t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
    simpa only [F] using raw_exp_density (I := I) g p v (hKdom hv)
  have hint :
      (∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
          ∂(modelHaar (E := E)) := by
    refine setLIntegral_congr_fun hKmeas (fun v hv => ?_)
    exact congrArg ENNReal.ofReal (hjac v hv)
  have hball := rawBall_integral_eq (I := I) g hEnorm p hR hRR₀ hcpt
  rw [← hK] at hball
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
        ∫⁻ v in K, ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
          ∂(modelHaar (E := E)) := by
      exact hball
    _ = ∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
        ∂(modelHaar (E := E)) := hint.symm
    _ = ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) :=
      rawJac_normal_int (I := I) g p hKmeas hKdom
    _ = _ := by rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma rawSegInt_ray_down
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (A : ℝ) (hA : 0 < A)
    (u : Metric.sphere (0 : E) 1) {a b : Set.Ioi (0 : ℝ)}
    (hab : a ≤ b)
    (hb : normalFrame (I := I) (E := E) g p (b.1 • u.1) ∈
      rawSegInt (I := I) g p ∩ gBall (I := I) g p A) :
    normalFrame (I := I) (E := E) g p (a.1 • u.1) ∈
      rawSegInt (I := I) g p ∩ gBall (I := I) g p A := by
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  have hu : g.inner p (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    dsimp only [L]
    rw [normalFrame_inner, real_inner_self_eq_norm_sq, hunorm, one_pow]
  have hLa : L (a.1 • u.1) = a.1 • L u.1 := by
    exact L.map_smul a.1 u.1
  have hLb : L (b.1 • u.1) = b.1 • L u.1 := by
    exact L.map_smul b.1 u.1
  change L (b.1 • u.1) ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A at hb
  have hInt : L (a.1 • u.1) ∈ rawSegInt (I := I) g p := by
    rw [hLa]
    apply rawSegInt_down (I := I) g p a.1 b.1 a.2 b.2 hab
    simpa only [hLb] using hb.1
  refine ⟨hInt, ?_⟩
  have hrawA := rawSegInt_sub (I := I) g hEnorm p hInt
  have hrawB := rawSegInt_sub (I := I) g hEnorm p hb.1
  have hnormA : Real.sqrt (g.inner p (L (a.1 • u.1)) (L (a.1 • u.1))) = a.1 := by
    rw [hLa]
    simpa only [hu, Real.sqrt_one, mul_one] using
      sqrt_gInner_smul_self (I := I) g p a.2.le (L u.1)
  have hnormB : Real.sqrt (g.inner p (L (b.1 • u.1)) (L (b.1 • u.1))) = b.1 := by
    rw [hLb]
    simpa only [hu, Real.sqrt_one, mul_one] using
      sqrt_gInner_smul_self (I := I) g p b.2.le (L u.1)
  have hbA : b.1 < A := by
    have hbBall := hb.2
    change riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from L (b.1 • u.1))) <
        ENNReal.ofReal A at hbBall
    change ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from L (b.1 • u.1))
        (show TangentSpace I p from L (b.1 • u.1)))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from L (b.1 • u.1))) at hrawB
    rw [← hrawB, hnormB] at hbBall
    exact (ENNReal.ofReal_lt_ofReal_iff hA).mp hbBall
  have hballA : L (a.1 • u.1) ∈ gBall (I := I) g p A := by
    change riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from L (a.1 • u.1))) <
        ENNReal.ofReal A
    change ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from L (a.1 • u.1))
        (show TangentSpace I p from L (a.1 • u.1)))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from L (a.1 • u.1))) at hrawA
    rw [← hrawA, hnormA]
    exact (ENNReal.ofReal_lt_ofReal_iff hA).mpr (hab.trans_lt hbA)
  simpa only [L] using hballA

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma rawBall_polar
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {t A A₀ : ℝ} (ht : 0 < t) (htA : t < A) (hAA₀ : A < A₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal A₀))) :
    let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
    let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := normalBasis (I := I) g p
    let Dn : E → ℝ := fun w =>
      curveDensity (I := I) g (radialCurve (I := I) g p (L w))
        (fun i => radialJacobiField (I := I) g p (L w) (B i)) 1
    let T : Set E := L ⁻¹' (rawSegInt (I := I) g p ∩ gBall (I := I) g p A)
    let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
      {r | r.1 • u.1 ∈ T}
    let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
      (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
        ∂(volume : Measure E).toSphere := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := normalBasis (I := I) g p
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g (radialCurve (I := I) g p (L w))
      (fun i => radialJacobiField (I := I) g p (L w) (B i)) 1
  let Kt : Set E := rawSegInt (I := I) g p ∩ gBall (I := I) g p t
  let Ka : Set E := rawSegInt (I := I) g p ∩ gBall (I := I) g p A
  let T : Set E := L ⁻¹' Ka
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | r.1 • u.1 ∈ T}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  have hA : 0 < A := ht.trans htA
  have htA₀ : t < A₀ := htA.trans hAA₀
  have hKa : MeasurableSet Ka := by
    simpa only [Ka] using rawSegInt_ball_meas (I := I) g hEnorm p hA hAA₀ hcpt
  have hT : MeasurableSet T :=
    hKa.preimage L.continuous.measurable
  have hTdom : ∀ w ∈ T, L w ∈ expDomain (I := I) g p := by
    intro w hw
    change L w ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A at hw
    exact rawSeg_mem_dom (I := I) g p
      (rawSegInt_sub (I := I) g hEnorm p hw.1)
  have hDn : ContinuousOn Dn T := by
    simpa only [Dn, L, B] using rawDn_cont (I := I) g p T hTdom
  have hS (u : Metric.sphere (0 : E) 1) : MeasurableSet (S u) :=
    hT.preimage (continuous_subtype_val.smul continuous_const).measurable
  have hF (u : Metric.sphere (0 : E) 1) :
      AEMeasurable (F u) (Measure.volumeIoiPow d) := by
    apply (aemeasurable_indicator_iff (hS u)).mpr
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    have hDnS : ContinuousOn (fun r : Set.Ioi (0 : ℝ) => Dn (r.1 • u.1)) (S u) :=
      hDn.comp (continuous_subtype_val.smul continuous_const).continuousOn
        (fun r hr => hr)
    exact hDnS.aemeasurable (hS u)
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r :=
    Iio_ae_eq_Iic' (hsingle r)
  have hLt : L ⁻¹' gBall (I := I) g p t = Metric.ball (0 : E) t := by
    simpa only [L] using preimage_gBall (I := I) (E := E) g p t
  have hLA : L ⁻¹' gBall (I := I) g p A = Metric.ball (0 : E) A := by
    simpa only [L] using preimage_gBall (I := I) (E := E) g p A
  have hpre : L ⁻¹' Kt = T ∩ Metric.ball (0 : E) t := by
    dsimp only [Kt, T, Ka]
    rw [preimage_inter, preimage_inter, hLt, hLA]
    ext w
    constructor
    · rintro ⟨hw, hwt⟩
      exact ⟨⟨hw, Metric.ball_subset_ball htA.le hwt⟩, hwt⟩
    · rintro ⟨⟨hw, _⟩, hwt⟩
      exact ⟨hw, hwt⟩
  have hset : MeasurableSet (T ∩ Metric.ball (0 : E) t) :=
    hT.inter measurableSet_ball
  have hind : AEMeasurable
      ((T ∩ Metric.ball (0 : E) t).indicator fun w => ENNReal.ofReal (Dn w))
      (volume : Measure E) := by
    apply (aemeasurable_indicator_iff hset).mpr
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    exact (hDn.mono Set.inter_subset_left).aemeasurable hset
  have hnormal := rawBall_normal (I := I) g hEnorm p ht htA₀ hcpt Kt rfl
  have hpolar :
      riemannianVolumeMeasure (I := I) (M := M) g
          {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
          ∫⁻ w in L ⁻¹' Kt, ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
        simpa only [L, B, Dn] using hnormal
      _ = ∫⁻ w in T ∩ Metric.ball (0 : E) t,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by rw [hpre]
      _ = ∫⁻ w : E,
          (T ∩ Metric.ball (0 : E) t).indicator (fun z => ENNReal.ofReal (Dn z)) w
          ∂(volume : Measure E) := (lintegral_indicator hset _).symm
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ),
            (T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        simpa only [d] using lintegral_polar (volume : Measure E) _ hind
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        apply lintegral_congr
        intro u
        have hu : ‖u.1‖ = 1 := by
          simpa only [mem_sphere_zero_iff_norm] using u.2
        have hball (r : Set.Ioi (0 : ℝ)) :
            r.1 • u.1 ∈ Metric.ball (0 : E) t ↔
              r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)) := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_of_nonneg r.2.le, hu, mul_one]
          rfl
        calc
          (∫⁻ r : Set.Ioi (0 : ℝ),
              (T ∩ Metric.ball (0 : E) t).indicator
                (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d) =
              ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
                ∂Measure.volumeIoiPow d := by
            rw [← lintegral_indicator measurableSet_Iio]
            apply lintegral_congr
            intro r
            have hseg : r ∈ S u ↔ r.1 • u.1 ∈ T := Iff.rfl
            dsimp only [F]
            by_cases hrS : r ∈ S u
            · by_cases hrt : r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · have hmem : r.1 • u.1 ∈ T ∩ Metric.ball (0 : E) t :=
                  ⟨hseg.mp hrS, (hball r).mpr hrt⟩
                rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hrt,
                  Set.indicator_of_mem hrS]
              · rw [Set.indicator_of_notMem (fun h => hrt ((hball r).mp h.2)),
                  Set.indicator_of_notMem hrt]
            · rw [Set.indicator_of_notMem (fun h => hrS (hseg.mpr h.1))]
              by_cases hrt : r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · rw [Set.indicator_of_mem hrt, Set.indicator_of_notMem hrS]
              · rw [Set.indicator_of_notMem hrt]
          _ = ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d := setLIntegral_congr (hIio ⟨t, ht⟩)
  simpa only [d, L, B, Dn, T, S, F] using hpolar

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A compact-buffer Bishop--Gromov comparison for strict raw metric balls. -/
theorem rawBall_vol_rel
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {q s R R₀ : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀)))
    (hRic : ∀ (y : M) (v : TangentSpace I y),
      riemannianEDist I p y < ENNReal.ofReal R₀ →
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
            g.inner y v v ≤
          ricciTensor (I := I) g y v v) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal R} *
        ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) s) ≤
      ENNReal.ofReal (hypRadVol q (Module.finrank ℝ E - 1) R) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal s} := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let A : ℝ := (R + R₀) / 2
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g (radialCurve (I := I) g p (L w))
      (fun i => radialJacobiField (I := I) g p (L w) (B i)) 1
  let T : Set E := L ⁻¹' (rawSegInt (I := I) g p ∩ gBall (I := I) g p A)
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | r.1 • u.1 ∈ T}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (hypDensity (q * r.1) d 1)
  have hR : 0 < R := hs.trans_le hsR
  have hA : 0 < A := by
    dsimp only [A]
    linarith
  have hRA : R < A := by
    dsimp only [A]
    linarith
  have hAA₀ : A < R₀ := by
    dsimp only [A]
    linarith
  have hsA : s < A := hsR.trans_lt hRA
  have hK : MeasurableSet (rawSegInt (I := I) g p ∩ gBall (I := I) g p A) :=
    rawSegInt_ball_meas (I := I) g hEnorm p hA hAA₀ hcpt
  have hT : MeasurableSet T := hK.preimage L.continuous.measurable
  have hTdom : ∀ w ∈ T, L w ∈ expDomain (I := I) g p := by
    intro w hw
    change L w ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A at hw
    exact rawSeg_mem_dom (I := I) g p
      (rawSegInt_sub (I := I) g hEnorm p hw.1)
  have hDn_cont : ContinuousOn Dn T := by
    simpa only [Dn, L, B] using rawDn_cont (I := I) g p T hTdom
  have hDn_nonneg (w : E) : 0 ≤ Dn w := by
    simp only [Dn, curveDensity]
    exact Real.sqrt_nonneg _
  have hS_meas (u : Metric.sphere (0 : E) 1) : MeasurableSet (S u) :=
    hT.preimage (continuous_subtype_val.smul continuous_const).measurable
  have hF_meas (u : Metric.sphere (0 : E) 1) :
      AEMeasurable (F u) (Measure.volumeIoiPow d) := by
    apply (aemeasurable_indicator_iff (hS_meas u)).mpr
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    have hDnS : ContinuousOn (fun r : Set.Ioi (0 : ℝ) => Dn (r.1 • u.1)) (S u) :=
      hDn_cont.comp (continuous_subtype_val.smul continuous_const).continuousOn
        (fun r hr => hr)
    exact hDnS.aemeasurable (hS_meas u)
  have hG_meas : Measurable G := by
    have hscale (r : Set.Ioi (0 : ℝ)) :
        hypDensity (q * r.1) d 1 = hypDensity q d r.1 / r.1 ^ d := by
      apply (eq_div_iff (pow_ne_zero d r.2.ne')).2
      simpa only [mul_one, mul_comm] using hypDens_scale q r.1 d 1 r.2.ne'
    rw [show G = fun r : Set.Ioi (0 : ℝ) =>
        ENNReal.ofReal (hypDensity q d r.1 / r.1 ^ d) by
      funext r
      change ENNReal.ofReal (hypDensity (q * r.1) d 1) =
        ENNReal.ofReal (hypDensity q d r.1 / r.1 ^ d)
      rw [hscale r]]
    exact ENNReal.measurable_ofReal.comp
      (((hypDen_continuous q d).measurable.comp measurable_subtype_coe).div
        (measurable_subtype_coe.pow_const d))
  have hS_down (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) : a ∈ S u := by
    change L (b.1 • u.1) ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A at hb
    change L (a.1 • u.1) ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A
    simpa only [L] using rawSegInt_ray_down (I := I) g hEnorm p A hA u hab hb
  have hu_inner (u : Metric.sphere (0 : E) 1) :
      g.inner p (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    dsimp only [L]
    rw [normalFrame_inner, real_inner_self_eq_norm_sq, hunorm, one_pow]
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r := Iio_ae_eq_Iic' (hsingle r)
  have hmodel {t : ℝ} (ht : 0 < t) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) = ENNReal.ofReal (hypRadVol q d t) := by
    calc
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d := setLIntegral_congr (hIio ⟨t, ht⟩).symm
      _ = ∫⁻ r : Set.Ioi (0 : ℝ),
          (Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))).indicator G r ∂Measure.volumeIoiPow d :=
        (lintegral_indicator measurableSet_Iio G).symm
      _ = ENNReal.ofReal (hypRadVol q d t) := by
        simpa only [G] using hypRad_lintegral q hq d ht
  have hpolar {t : ℝ} (ht : 0 < t) (htA : t < A) :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d ∂(volume : Measure E).toSphere := by
    simpa only [d, L, B, Dn, T, S, F] using
      rawBall_polar (I := I) g hEnorm p ht htA hAA₀ hcpt
  have hcross (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b)
      (hbR : b ≤ (⟨R, hR⟩ : Set.Ioi (0 : ℝ))) :
      F u b * G a ≤ F u a * G b := by
    by_cases hbS : b ∈ S u
    · have haS : a ∈ S u := hS_down u hab hbS
      have hbS' := hbS
      change L (b.1 • u.1) ∈ rawSegInt (I := I) g p ∩ gBall (I := I) g p A at hbS'
      let uT : E := L u.1
      have huT_one : g.inner p uT uT = 1 := by
        simpa only [uT] using hu_inner u
      have huT_pos : 0 < g.inner p uT uT := by
        simpa only [huT_one] using one_pos
      have huT0 : uT ≠ 0 := by
        intro hu0
        rw [hu0] at huT_pos
        simp only [map_zero, lt_self_iff_false] at huT_pos
      have hrawIntB : b.1 • uT ∈ rawSegInt (I := I) g p := by
        simpa only [uT, L.map_smul] using hbS'.1
      obtain ⟨c, hc, hcraw⟩ := hrawIntB
      have hc0 : 0 < c := one_pos.trans hc
      have hcb : b.1 < c * b.1 := lt_mul_of_one_lt_left b.2 hc
      let ell : ℝ := min ((c * b.1 + b.1) / 2) A
      have hbell : b.1 < ell := by
        apply lt_min
        · dsimp only [ell]
          nlinarith
        · exact (show b.1 ≤ R from hbR).trans_lt hRA
      have hellpos : 0 < ell := b.2.trans hbell
      have hellA : ell ≤ A := min_le_right _ _
      have hellcb : ell < c * b.1 := by
        calc
          ell ≤ (c * b.1 + b.1) / 2 := min_le_left _ _
          _ < c * b.1 := by nlinarith
      have hrawIntL : ell • uT ∈ rawSegInt (I := I) g p := by
        refine ⟨c * b.1 / ell, (lt_div_iff₀ hellpos).mpr (by
          simpa only [one_mul] using hellcb), ?_⟩
        simpa only [smul_smul, div_mul_cancel₀ (c * b.1) hellpos.ne'] using hcraw
      have hrawL : ell • uT ∈ rawSeg (I := I) g p :=
        rawSegInt_sub (I := I) g hEnorm p hrawIntL
      have hdomB : ∀ t ∈ Set.Icc (0 : ℝ) b.1,
          (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p := by
        intro t ht
        have hfrac : t / ell ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨div_nonneg ht.1 hellpos.le, (div_le_one hellpos).mpr (ht.2.trans hbell.le)⟩
        have hscale := Geodesic.smul_mem_expDomain (I := I) g p
          (show TangentSpace I p from ell • uT)
          (rawSeg_mem_dom (I := I) g p hrawL) hfrac
        change (show TangentSpace I p from (t / ell) • (ell • uT)) ∈
          expDomain (I := I) g p at hscale
        simpa only [smul_smul, div_mul_cancel₀ t hellpos.ne', one_smul] using hscale
      have hRicRay : ∀ t ∈ Set.Ioo (0 : ℝ) ell,
          -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
              g.inner (radialCurve (I := I) g p uT t)
                (curveVelocity (I := I) (radialCurve (I := I) g p uT) t)
                (curveVelocity (I := I) (radialCurve (I := I) g p uT) t) ≤
            ricciTensor (I := I) g (radialCurve (I := I) g p uT t)
              (curveVelocity (I := I) (radialCurve (I := I) g p uT) t)
              (curveVelocity (I := I) (radialCurve (I := I) g p uT) t) := by
        intro t ht
        have hrawIntT : t • uT ∈ rawSegInt (I := I) g p :=
          rawSegInt_down (I := I) g p t ell ht.1 hellpos ht.2.le hrawIntL
        have hrawT := rawSegInt_sub (I := I) g hEnorm p hrawIntT
        have hnormT : Real.sqrt (g.inner p (t • uT) (t • uT)) = t := by
          simpa only [huT_one, Real.sqrt_one, mul_one] using
            sqrt_gInner_smul_self (I := I) g p ht.1.le uT
        have hball : riemannianEDist I p (radialCurve (I := I) g p uT t) <
            ENNReal.ofReal R₀ := by
          change ENNReal.ofReal (Real.sqrt (g.inner p (t • uT) (t • uT))) =
            riemannianEDist I p (radialCurve (I := I) g p uT t) at hrawT
          rw [← hrawT, hnormT]
          exact (ENNReal.ofReal_lt_ofReal_iff (hA.trans hAA₀)).mpr
            ((ht.2.trans_le hellA).trans_lt hAA₀)
        exact hRic _ _ hball
      by_cases hd : 0 < d
      · obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p uT huT_pos
        have hperp : ∀ i, g.inner p uT (v i) = 0 := by
          intro i
          rw [g.symm p uT (v i)]
          exact hperp' i
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g (radialCurve (I := I) g p uT)
            (fun i => radialJacobiField (I := I) g p uT (v i)) t
        have hanti : AntitoneOn (fun t => Dt t / hypDensity q d t)
            (Set.Ioo (0 : ℝ) ell) := by
          simpa only [Dt, d, huT_one, Real.sqrt_one, mul_one] using
            raw_ratio_ray (I := I) g hEnorm p uT q ell hq hellpos huT_one hrawL
              v hON hperp (by simpa only [d] using hd) hRicRay
        have haWin : a.1 ∈ Set.Ioo (0 : ℝ) ell := ⟨a.2, hab.trans_lt hbell⟩
        have hbWin : b.1 ∈ Set.Ioo (0 : ℝ) ell := ⟨b.2, hbell⟩
        have hratio := hanti haWin hbWin hab
        have hHa : 0 < hypDensity q d a.1 := hypDensity_pos hq a.2
        have hHb : 0 < hypDensity q d b.1 := hypDensity_pos hq b.2
        have htrans : Dt b.1 * hypDensity q d a.1 ≤ Dt a.1 * hypDensity q d b.1 :=
          (div_le_div_iff₀ hHb hHa).1 hratio
        have hdomA : ∀ t ∈ Set.Icc (0 : ℝ) a.1,
            (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p :=
          fun t ht => hdomB t ⟨ht.1, ht.2.trans hab⟩
        let C : ℝ := |(chartModelBasis E).det B|
        let N : ℝ := normalChartDensity (I := I) g p 0
        have hCN : 0 ≤ C * N := by
          dsimp only [C, N]
          exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
        have hscale (r : ℝ) (hr : 0 < r)
            (hdom : ∀ t ∈ Set.Icc (0 : ℝ) r,
              (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p) :
            r ^ d * Dn (r • u.1) = (C * N) * Dt r := by
          have hLr : L (r • u.1) = r • uT := by
            simpa only [uT] using L.map_smul r u.1
          have hDn : Dn (r • u.1) = C *
              curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                (fun i => radialJacobiField (I := I) g p (r • uT)
                  (chartModelBasis E i)) 1 := by
            dsimp only [Dn]
            rw [hLr]
            simpa only [C] using raw_basis_density (I := I) g p (r • uT)
              (hdom r ⟨hr.le, le_rfl⟩) (chartModelBasis E) B
          have hfac := rawDens_eq_trans (I := I) g p huT0 r hr hdom v hON hperp
          calc
            r ^ d * Dn (r • u.1) = C *
                (curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                  (fun i => radialJacobiField (I := I) g p (r • uT)
                    (chartModelBasis E i)) 1 * r ^ d) := by rw [hDn]; ring
            _ = C * (N * Dt r) := by simpa only [N] using congrArg (fun z => C * z) hfac
            _ = (C * N) * Dt r := by ring
        have hSa := hscale a.1 a.2 hdomA
        have hSb := hscale b.1 b.2 hdomB
        have hGa : a.1 ^ d * hypDensity (q * a.1) d 1 = hypDensity q d a.1 := by
          simpa only [mul_one] using hypDens_scale q a.1 d 1 a.2.ne'
        have hGb : b.1 ^ d * hypDensity (q * b.1) d 1 = hypDensity q d b.1 := by
          simpa only [mul_one] using hypDens_scale q b.1 d 1 b.2.ne'
        have hpowa : 0 < a.1 ^ d := pow_pos a.2 d
        have hpowb : 0 < b.1 ^ d := pow_pos b.2 d
        have hreal : Dn (b.1 • u.1) * hypDensity (q * a.1) d 1 ≤
            Dn (a.1 • u.1) * hypDensity (q * b.1) d 1 := by
          apply (mul_le_mul_iff_right₀ (mul_pos hpowa hpowb)).mp
          calc
            (a.1 ^ d * b.1 ^ d) *
                (Dn (b.1 • u.1) * hypDensity (q * a.1) d 1) =
                (b.1 ^ d * Dn (b.1 • u.1)) *
                  (a.1 ^ d * hypDensity (q * a.1) d 1) := by ring
            _ = (C * N) * (Dt b.1 * hypDensity q d a.1) := by rw [hSb, hGa]; ring
            _ ≤ (C * N) * (Dt a.1 * hypDensity q d b.1) :=
              mul_le_mul_of_nonneg_left htrans hCN
            _ = (a.1 ^ d * Dn (a.1 • u.1)) *
                (b.1 ^ d * hypDensity (q * b.1) d 1) := by rw [hSa, hGb]; ring
            _ = (a.1 ^ d * b.1 ^ d) *
                (Dn (a.1 • u.1) * hypDensity (q * b.1) d 1) := by ring
        simp only [F, G, Set.indicator_of_mem hbS, Set.indicator_of_mem haS]
        rw [← ENNReal.ofReal_mul (hDn_nonneg (b.1 • u.1)),
          ← ENNReal.ofReal_mul (hDn_nonneg (a.1 • u.1))]
        exact ENNReal.ofReal_le_ofReal hreal
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        let v : Fin d → E := fun i => isEmptyElim (hd0 ▸ i)
        have hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hperp : ∀ i, g.inner p uT (v i) = 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g (radialCurve (I := I) g p uT)
            (fun i => radialJacobiField (I := I) g p uT (v i)) t
        have hDt (t : ℝ) : Dt t = 1 := by
          have hgram : curveGram (I := I) g (radialCurve (I := I) g p uT)
              (fun i => radialJacobiField (I := I) g p uT (v i)) t = 1 := by
            ext i
            exact isEmptyElim (hd0 ▸ i)
          simp only [Dt, curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
        have hdomA : ∀ t ∈ Set.Icc (0 : ℝ) a.1,
            (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p :=
          fun t ht => hdomB t ⟨ht.1, ht.2.trans hab⟩
        let C : ℝ := |(chartModelBasis E).det B|
        let N : ℝ := normalChartDensity (I := I) g p 0
        have hscale (r : ℝ) (hr : 0 < r)
            (hdom : ∀ t ∈ Set.Icc (0 : ℝ) r,
              (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p) :
            r ^ d * Dn (r • u.1) = (C * N) * Dt r := by
          have hLr : L (r • u.1) = r • uT := by
            simpa only [uT] using L.map_smul r u.1
          have hDn : Dn (r • u.1) = C *
              curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                (fun i => radialJacobiField (I := I) g p (r • uT)
                  (chartModelBasis E i)) 1 := by
            dsimp only [Dn]
            rw [hLr]
            simpa only [C] using raw_basis_density (I := I) g p (r • uT)
              (hdom r ⟨hr.le, le_rfl⟩) (chartModelBasis E) B
          have hfac := rawDens_eq_trans (I := I) g p huT0 r hr hdom v hON hperp
          calc
            r ^ d * Dn (r • u.1) = C *
                (curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                  (fun i => radialJacobiField (I := I) g p (r • uT)
                    (chartModelBasis E i)) 1 * r ^ d) := by rw [hDn]; ring
            _ = C * (N * Dt r) := by simpa only [N] using congrArg (fun z => C * z) hfac
            _ = (C * N) * Dt r := by ring
        have hDa : Dn (a.1 • u.1) = C * N := by
          have h := hscale a.1 a.2 hdomA
          simpa only [hd0, pow_zero, one_mul, mul_one, hDt] using h
        have hDb : Dn (b.1 • u.1) = C * N := by
          have h := hscale b.1 b.2 hdomB
          simpa only [hd0, pow_zero, one_mul, mul_one, hDt] using h
        have hGa : hypDensity (q * a.1) d 1 = 1 := by
          simp only [hd0, hypDensity, pow_zero]
        have hGb : hypDensity (q * b.1) d 1 = 1 := by
          simp only [hd0, hypDensity, pow_zero]
        simp only [F, G, Set.indicator_of_mem hbS, Set.indicator_of_mem haS,
          hDa, hDb, hGa, hGb, ENNReal.ofReal_one, mul_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
  have hdir (u : Metric.sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hypRadVol q d s) ≤
        (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hypRadVol q d R) := by
    have h := lintegral_Iic_cross
      (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
      (hF_meas u).restrict hG_meas.aemeasurable.restrict
      (fun {_a _b} hab hbR => hcross u hab hbR)
      (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
    rw [hmodel hs, hmodel hR] at h
    exact h
  rw [show Module.finrank ℝ E - 1 = d by rfl]
  rw [hpolar hR hRA, hpolar hs hsA]
  rw [mul_comm (ENNReal.ofReal (hypRadVol q d R))
    (∫⁻ u : Metric.sphere (0 : E) 1,
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d ∂(volume : Measure E).toSphere)]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hypRadVol q d s))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hypRadVol q d R))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
