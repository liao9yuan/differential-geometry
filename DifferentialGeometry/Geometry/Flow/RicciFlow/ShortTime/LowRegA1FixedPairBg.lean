import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC1Pair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgForceArms
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3FirstOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FiniteSpectralPairing
import DifferentialGeometry.Analysis.Sobolev.Tensor.CrossScaleCauchySchwarz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRHSSymm

/-!
# Fixed-background first-order Galerkin pairing

This module isolates the complete order-one correction caused by replacing the
self DeTurck background by one fixed background.  The coefficient is estimated
in intrinsic `H2` and paired directly against the Galerkin state at Rung 3, so
the dissipation coefficient uses no fourth varying-metric jet.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The order-one Galerkin vector produced by the complete fixed-background
`C1` correction.  The realization hypothesis supplies the metric certificates
for both the retracted state and the zero endpoint. -/
def galA1FixVecBg
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) :=
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := lowregFibZero (I := I) (M := M) g hR hreal
  smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
    (appCc (I := I) (M := M) g 3 2
      (lowC1CorrBg (I := I) (M := M) g gBase T hδ hT hZ)
      (iteratedCovGrad (I := I) g 0 2 1 T))

/-- The signed weighted Galerkin pairing of the state coefficients with the
complete fixed-background order-one correction. -/
def galA1FixPairBg
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (σ : ℝ) : ℝ :=
  ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ *
    (c i * (galA1FixVecBg (I := I) (M := M) g gBase
      hR hδ hreal F c).coeff i)

/-- The complementary fixed-background Galerkin arm: it retains the complete
fixed-background second-order action and `C0` action, while replacing only its
`C1` action by the self-background coefficient. -/
def galA1RestVecBg
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) :=
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := lowregFibZero (I := I) (M := M) g hR hreal
  let AB := lowBaseData (I := I) (M := M) g gBase T hδ hT hZ
  let AS := lowBaseData (I := I) (M := M) g g T hδ hT hZ
  smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
    (AB.a2 (I := I) (M := M) T +
      appCc (I := I) (M := M) g 2 2 AB.C0 T +
      appCc (I := I) (M := M) g 3 2 AS.C1
        (iteratedCovGrad (I := I) g 0 2 1 T))

/-- The fixed-background Galerkin arm is exactly its retained `C2/C0` rest
plus the complete `C1` background correction. -/
theorem galArmVecBg_split
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    galArmVecBg (I := I) (M := M) g gBase hR hδ hreal F c =
      galA1RestVecBg (I := I) (M := M) g gBase hR hδ hreal F c +
        galA1FixVecBg (I := I) (M := M) g gBase hR hδ hreal F c := by
  simp only [galArmVecBg, galA1RestVecBg, galA1FixVecBg, lowC1CorrBg]
  rw [← smoothCcToTensorHs_add]
  apply congrArg
  simp only [LowBaseActionData.a1, appCc_sub_left]
  abel

/-- The generic weighted Galerkin pairing of the state with the retained
fixed-background `C2/C0` rest arm. -/
def galA1RestPairBg
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (σ : ℝ) : ℝ :=
  ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ *
    (c i * (galA1RestVecBg (I := I) (M := M) g gBase
      hR hδ hreal F c).coeff i)

/-- At Rung 3, the signed fixed-background arm pairing splits exactly into
the retained rest pairing and the complete `C1` correction pairing. -/
theorem galArmPair3_split
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
      (c i * (galArmVecBg (I := I) (M := M) g gBase
        hR hδ hreal F c).coeff i)) =
      galA1RestPairBg (I := I) (M := M) g gBase
          hR hδ hreal F c 3 +
        galA1FixPairBg (I := I) (M := M) g gBase
          hR hδ hreal F c 3 := by
  rw [galArmVecBg_split (I := I) (M := M) g gBase hR hδ hreal F c]
  simp only [tensorHs.add_coeff, mul_add, Finset.sum_add_distrib,
    galA1RestPairBg, galA1FixPairBg]

private theorem lowArm_symm
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : symmS (I := I) (M := M) g T = T)
    {δ : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    let A := lowBaseData (I := I) (M := M) g gBase T hδ hT hZ
    symmS (I := I) (M := M) g
        (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T) =
      A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T := by
  dsimp only
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g gBase
  have hsplitT := (hsplit T
    (bilin_symm_of_symmS (I := I) (M := M) g hTsymm)
    hδ3 hδ0 hT hZ).1
  have hzero : symmS (I := I) (M := M) g
      (0 : SmoothCcTensor g 0 2) = 0 := by
    simpa only [zero_smul] using
      (symmS_smul (I := I) (M := M) g (0 : ℝ)
        (0 : SmoothCcTensor g 0 2))
  rw [← hsplitT, symmS_sub,
    symmS_smoothRem (I := I) (M := M) g gBase T hδ hT hTsymm,
    symmS_smoothRem (I := I) (M := M) g gBase
      (0 : SmoothCcTensor g 0 2) hδ hZ hzero]

/-- The signed Rung-3 Galerkin pairing of the complete fixed-background arm is
exactly the diagonal complementary-iterate pairing of the retracted state with
that arm, after multiplying by the radial retraction scalar. -/
theorem galArmPair3_diag
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
    let T : SmoothCcTensor g 0 2 :=
      symmS (I := I) (M := M) g
        (galCoreRep (I := I) (M := M) g R F c)
    let hT := galRepFib (I := I) (M := M) g hR hreal F c
    let hZ := lowregFibZero (I := I) (M := M) g hR hreal
    let A := lowBaseData (I := I) (M := M) g gBase T hδ hT hZ
    θ * (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
        (c i * (galArmVecBg (I := I) (M := M) g gBase
          hR hδ hreal F c).coeff i)) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 2 T).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 1
          (A.a2 (I := I) (M := M) T +
            A.a1 (I := I) (M := M) T)).toFun := by
  classical
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
    (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := lowregFibZero (I := I) (M := M) g hR hreal
  let A := lowBaseData (I := I) (M := M) g gBase T hδ hT hZ
  have hTfix : symmS (I := I) (M := M) g T = T := by
    dsimp only [T]
    exact symmS_idem (I := I) (M := M) g _
  have hA : symmS (I := I) (M := M) g
      (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T) =
        A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T := by
    exact lowArm_symm (I := I) (M := M) g gBase T hTfix hδ hδ0 hδ3 hT hZ
  have hrep : T = θ • symmS (I := I) (M := M) g
      (finiteEigenCombo (I := I) (M := M) g F c) := by
    dsimp only [T, θ]
    rw [galCoreRep, symmS_smul]
  have hpair := finite_symm_scale (I := I) (M := M) g F c
    (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T)
    1 2 θ hA
  rw [← hrep] at hpair
  simpa only [galArmVecBg, smoothCcToTensorHs_coeff, Nat.reduceAdd,
    T, hT, hZ, A] using hpair

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
/-- The complete fixed-background order-one correction obeys the Rung-3
cross-scale energy estimate.  The scalar lower-energy coefficient is selected
in the required order `eta -> g -> G`; the later Galerkin radius is harmless
because the solver supplies the cap `R <= 1`. -/
theorem galA1FixPair3_le
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∀ {η : ℝ}, 0 < η →
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ G : ℝ, 0 ≤ G ∧
          ∀ {R δ : ℝ}, (hR : 0 ≤ R) → (hRcap : R ≤ 1) →
          (hδ_le : δ ≤ δ₀) → 0 ≤ δ →
          (hreal : ∀ T : SmoothCcTensor g 0 2,
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ) →
          ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
            (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
            2 * |galA1FixPairBg (I := I) (M := M) g gBase
              hR (lt_of_le_of_lt hδ_le hδ₀) hreal F c 3| ≤
              η * (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                  (c i) ^ 2) +
              G * (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                  (c i) ^ 2) := by
  obtain ⟨Bc, hBc, hcorr⟩ :=
    lowC1Corr_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  intro η hη g hEq hjet
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h2_h3_h2 (I := I) (M := M) hDim g 2 2
  let K : ℝ := Capp * Bc 1
  let G : ℝ := η⁻¹ * K ^ 2
  have hK : 0 ≤ K := mul_nonneg hCapp (hBc 1 zero_le_one)
  have hG : 0 ≤ G := mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg K)
  refine ⟨G, hG, ?_⟩
  intro R δ hR hRcap hδ_le hδ_nonneg hreal F c
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := lowregFibZero (I := I) (M := M) g hR hreal
  let Corr : SmoothCcTensor g 3 2 :=
    lowC1CorrBg (I := I) (M := M) g gBase T hδ_lt hT hZ
  let Y : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 3 2 Corr
      (iteratedCovGrad (I := I) g 0 2 1 T)
  have hT2smooth :
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ R := by
    have hraw := symm_h2_of_state (I := I) (M := M) g
        (galCoreRep (I := I) (M := M) g R F c)
        (galCoreRep_ball (I := I) (M := M) g hR F c)
    rw [show (2 : ℝ) = (((1 : ℕ) : ℝ) + 1) by norm_num]
    simpa only [T] using hraw
  have hT2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 := by
    rw [norm_ccHs_eq_smoothHs]
    exact hT2smooth.trans hRcap
  have hCorr : lowJetSq (I := I) (M := M) g 2 Corr ≤ (Bc 1) ^ 2 := by
    simpa only [Corr] using
      hcorr g hEq hjet T hδ_le hδ_nonneg hT hZ 1 zero_le_one hT2
  let E3 : ℝ := ∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2
  have hE3 : 0 ≤ E3 := by
    dsimp only [E3]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i (3 : ℝ))
        (sq_nonneg (c i))
  have hT3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ Real.sqrt E3 := by
    rw [norm_ccHs_eq_smoothHs]
    simpa only [T, E3] using
      galRepHs_le (I := I) (M := M) g (3 : ℝ) hR F c
  have hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        K * Real.sqrt E3 := by
    have hact := happ Corr T (Bc 1) (hBc 1 zero_le_one)
      (by simpa only [lowJetSq, Nat.reduceAdd] using hCorr)
    have hmul := mul_le_mul_of_nonneg_left hT3
      (mul_nonneg hCapp (hBc 1 zero_le_one))
    exact hact.trans (by simpa only [K] using hmul)
  have hvec :
      galA1FixVecBg (I := I) (M := M) g gBase hR hδ_lt hreal F c =
        smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) Y := by
    rfl
  have hmass :
      (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
          ((galA1FixVecBg (I := I) (M := M) g gBase
            hR hδ_lt hreal F c).coeff i) ^ 2) ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ^ 2 := by
    simpa only [hvec, smoothCcToTensorHs_coeff] using
      cc_partial_le_norm (I := I) (M := M) g 2 (2 : ℝ) Y F
  have hmassK :
      (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
          ((galA1FixVecBg (I := I) (M := M) g gBase
            hR hδ_lt hreal F c).coeff i) ^ 2) ≤ K ^ 2 * E3 := by
    calc
      _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ^ 2 := hmass
      _ ≤ (K * Real.sqrt E3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hY 2
      _ = K ^ 2 * (Real.sqrt E3) ^ 2 := by ring
      _ = K ^ 2 * E3 := by rw [Real.sq_sqrt hE3]
  have hcross := two_abs_cross_le_eps (I := I) (M := M)
    F (3 : ℝ) c
      (fun i => (galA1FixVecBg (I := I) (M := M) g gBase
        hR hδ_lt hreal F c).coeff i) hη
  norm_num at hcross
  calc
    2 * |galA1FixPairBg (I := I) (M := M) g gBase
        hR hδ_lt hreal F c 3| ≤
        η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        η⁻¹ * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
            ((galA1FixVecBg (I := I) (M := M) g gBase
              hR hδ_lt hreal F c).coeff i) ^ 2) := by
          simpa only [galA1FixPairBg] using hcross
    _ ≤ η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        η⁻¹ * (K ^ 2 * E3) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hmassK (inv_nonneg.mpr hη.le))
    _ = η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        G * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) := by
          simp only [G, E3]
          ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
