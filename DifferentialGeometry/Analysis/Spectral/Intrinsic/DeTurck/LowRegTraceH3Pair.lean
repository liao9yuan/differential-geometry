import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2Pair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegOpJetWindows
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TsRungs

/-!
# Three-dimensional tame `H³` pair bounds for the moving trace

This module exposes the small reusable `H³` pair interface needed by the
fixed-background low-regularity coefficient estimates.  Its final currency is
`D3 + D2 + A * D2`: the third-order difference, its second-order companion,
and the tame endpoint-high/difference-low product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ### A tame three-dimensional `H³` application estimate -/

private theorem grad_sq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

private theorem grad_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 3 S := by
  have h0 := grad_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_sq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖S‖]

private theorem jet3_grad
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 3 S ≤
      lowJetSq (I := I) (M := M) g 2 S +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g r s S) := by
  have h0 := grad_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_sq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg
    ‖iteratedCovGrad (I := I) g r s 1 S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 2 S‖]

omit [BoundarylessManifold I M] in
private theorem h3_tame_sc
    {c0 c1 c2 fr X Y : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hfr : 0 ≤ fr) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    c0 * X + 2 * (c1 * X + c2 * fr * Y) ≤
      (c0 + 2 * (c1 + c2 * fr)) * (X + Y) := by
  have h0Y : 0 ≤ c0 * Y := mul_nonneg hc0 hY
  have h1Y : 0 ≤ 2 * c1 * Y :=
    mul_nonneg (mul_nonneg (by norm_num) hc1) hY
  have h2X : 0 ≤ 2 * c2 * fr * X :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc2) hfr) hX
  nlinarith only [h0Y, h1Y, h2X]

set_option maxHeartbeats 1600000 in
/-- In dimension three, applying a tensor-valued coefficient is tame from
`H³ × H²` and `H² × H³` into `H³`. -/
theorem app_h3_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * (lowJetSq (I := I) (M := M) g 3 Φ *
              lowJetSq (I := I) (M := M) g 2 W +
            lowJetSq (I := I) (M := M) g 2 Φ *
              lowJetSq (I := I) (M := M) g 3 W) := by
  obtain ⟨C0, hC0, h0⟩ := appH2 (I := I) (M := M) hDim g p r c
  obtain ⟨C1, hC1, h1⟩ := appH2 (I := I) (M := M) hDim g p r (c + 1)
  obtain ⟨C2, hC2, h2⟩ := appH2 (I := I) (M := M) hDim g p (r + 1) (c + 1)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := C0 + 2 * (C1 + C2 * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0
      (mul_nonneg (by norm_num) (add_nonneg hC1 (mul_nonneg hC2 hfr)))
  refine ⟨C, hC, ?_⟩
  intro Φ W
  let Y : SmoothCcTensor g p c := appCcRS (I := I) (M := M) g p r c Φ W
  let P : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
  let Q : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g p r W)
  let X : ℝ := lowJetSq (I := I) (M := M) g 3 Φ *
    lowJetSq (I := I) (M := M) g 2 W
  let Z : ℝ := lowJetSq (I := I) (M := M) g 2 Φ *
    lowJetSq (I := I) (M := M) g 3 W
  have hΦ23 := jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) Φ
  have hΦ2 := jetNn (I := I) (M := M) (m := 2) g Φ
  have hW2 := jetNn (I := I) (M := M) (m := 2) g W
  have hΦ3 := jetNn (I := I) (M := M) (m := 3) g Φ
  have hW3 := jetNn (I := I) (M := M) (m := 3) g W
  have hX : 0 ≤ X := mul_nonneg hΦ3 hW2
  have hZ : 0 ≤ Z := mul_nonneg hΦ2 hW3
  have hY2 : lowJetSq (I := I) (M := M) g 2 Y ≤ C0 * X := by
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          C0 * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [Y] using h0 Φ W
      _ ≤ C0 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦ23 hC0) hW2
      _ = C0 * X := by simp only [X]; ring
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ C1 * X := by
    calc
      lowJetSq (I := I) (M := M) g 2 P ≤
          C1 * lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [P] using h1 (covGrad (I := I) (M := M) g r c Φ) W
      _ ≤ C1 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (grad_h2 (I := I) (M := M) g Φ) hC1) hW2
      _ = C1 * X := by simp only [X]; ring
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ C2 * fr * Z := by
    calc
      lowJetSq (I := I) (M := M) g 2 Q ≤
          C2 * lowJetSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        simpa only [Q] using
          h2 (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g p r W)
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [fr] using slotH2 (I := I) (M := M) g r c Φ) hC2)
          (jetNn (I := I) (M := M) g
            (covGrad (I := I) (M := M) g p r W))
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left (grad_h2 (I := I) (M := M) g W)
          (mul_nonneg hC2 (mul_nonneg hfr hΦ2))
      _ = C2 * fr * Z := by simp only [Z]; ring
  have hgrad : lowJetSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g p c Y) ≤
        2 * (C1 * X + C2 * fr * Z) := by
    rw [show covGrad (I := I) (M := M) g p c Y = P + Q by
      simpa only [Y, P, Q] using covGrad_appCcRS_eq (I := I) (M := M) g p r c Φ W]
    exact (jetAdd (I := I) (M := M) g 2 P Q).trans
      (mul_le_mul_of_nonneg_left (add_le_add hP2 hQ2) (by norm_num))
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) =
      lowJetSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ lowJetSq (I := I) (M := M) g 2 Y +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) :=
      jet3_grad (I := I) (M := M) g Y
    _ ≤ C0 * X + 2 * (C1 * X + C2 * fr * Z) := add_le_add hY2 hgrad
    _ ≤ C * (X + Z) := by
      simpa only [C] using h3_tame_sc hC0 hC1 hC2 hfr hX hZ
    _ = C * (lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W +
          lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 3 W) := by
      simp only [X, Z]

/-! ### Inverse-slot endpoint and difference bounds -/

private theorem endo_slot_l2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x => rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endo_slot_jet
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem perturb_jet
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    lowJetSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g 1
          (symmRaiseEndo (I := I) (M := M) g D)) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g m D := by
  have h0 :
      lowJetSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g D)) =
        lowJetSq (I := I) (M := M) g m D := by
    rw [insert_symmRaise_eq (I := I) (M := M) g D]
    calc
      lowJetSq (I := I) (M := M) g m
          (cometricRaiseSlot0Field (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D))) =
        lowJetSq (I := I) (M := M) g m
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D)) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D)) q]
      _ = lowJetSq (I := I) (M := M) g m
          (symmS (I := I) (M := M) g D) := by
        unfold lowJetSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D) q]
      _ = lowJetSq (I := I) (M := M) g m D := by rw [hD]
  have hslot := endo_slot_jet (I := I) (M := M) g 1 m
    (symmRaiseEndo (I := I) (M := M) g D)
  rw [h0] at hslot
  simpa only [pow_one] using hslot

set_option linter.unusedVariables false in
private theorem full_slot_h3
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Aw, Sw, hwin⟩ :=
    moserWin_fullSlot (I := I) (M := M) g 1 hδ₀0 hδ₀
  let K : ℝ := |Aw 3|
  refine ⟨K, abs_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * δ₀) ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hpert : IsPathPert (I := I) (M := M) g gm P P δ₀ :=
    ⟨⟨δ, hδ0, hδ_le, hδ⟩, htie, hsup, fun _ => le_rfl⟩
  have hj := (hwin P gm P hpert).2.2 3
  have hfac : 0 ≤ 1 + lowJetSq (I := I) (M := M) g 3 P := by
    have := jetNn (I := I) (M := M) (m := 3) g P
    linarith
  exact hj.trans (mul_le_mul_of_nonneg_right (le_abs_self (Aw 3))
    hfac)

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- On a fixed fibre-small metric ball, the inverse-metric slot difference has
the three-dimensional tame `H³` modulus `D3 + D2 + A * D2`. -/
theorem inv_slot_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 3
          (gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bh, hBh, hbdd⟩ :=
    LowBaseInternal.fullSlot_bdd_h2
      (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kh, hKh, hh3⟩ :=
    full_slot_h3 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C2, hC2, happ2⟩ := appH2 (I := I) (M := M) hDim g 2 2 2
  obtain ⟨C3, hC3, happ3⟩ := app_h3_tame (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  let Z3 : ℝ → ℝ := fun R => C3 ^ 2 * fr * (Bh R) ^ 4
  let Z2 : ℝ → ℝ := fun R => C3 * Kh * fr * (Bh R) ^ 2 * (C2 + C3)
  let Z : ℝ → ℝ := fun R => Z3 R + Z2 R
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ3 : ∀ R : ℝ, 0 ≤ Z3 R := by
    intro R
    dsimp only [Z3]
    positivity
  have hZ2 : ∀ R : ℝ, 0 ≤ Z2 R := by
    intro R
    dsimp only [Z2]
    positivity
  have hZ : ∀ R : ℝ, 0 ≤ Z R := by
    intro R
    exact add_nonneg (hZ3 R) (hZ2 R)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let LT : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gT)
  let LU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gU)
  let P : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
  let X : SmoothCcTensor g 2 2 := appCcRS (I := I) (M := M) g 2 2 2 P LT
  let Y : SmoothCcTensor g 2 2 := appCcRS (I := I) (M := M) g 2 2 2 LU X
  let H3 : ℝ := Kh * (1 + A ^ 2)
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub,
      symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT,
      symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g U hU]
  have hLT2 : lowJetSq (I := I) (M := M) g 2 LT ≤ (Bh R) ^ 2 := by
    simpa only [LT] using hbdd gT T hT hTtie hδT_le hδT0 hδT R hR hT2
  have hLU2 : lowJetSq (I := I) (M := M) g 2 LU ≤ (Bh R) ^ 2 := by
    simpa only [LU] using hbdd gU U hU hUtie hδU_le hδU0 hδU R hR hU2
  have hLT3 : lowJetSq (I := I) (M := M) g 3 LT ≤ H3 := by
    calc
      lowJetSq (I := I) (M := M) g 3 LT ≤
          Kh * (1 + lowJetSq (I := I) (M := M) g 3 T) := by
        simpa only [LT] using hh3 gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ H3 := mul_le_mul_of_nonneg_left (by linarith) hKh
  have hLU3 : lowJetSq (I := I) (M := M) g 3 LU ≤ H3 := by
    calc
      lowJetSq (I := I) (M := M) g 3 LU ≤
          Kh * (1 + lowJetSq (I := I) (M := M) g 3 U) := by
        simpa only [LU] using hh3 gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ H3 := mul_le_mul_of_nonneg_left (by linarith) hKh
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ fr * D2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 P ≤
          fr * lowJetSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [P, fr] using perturb_jet (I := I) (M := M) g 2 (T - U) hsymm
      _ ≤ fr * D2 ^ 2 := mul_le_mul_of_nonneg_left hTU2 hfr
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ fr * D3 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 3 P ≤
          fr * lowJetSq (I := I) (M := M) g 3 (T - U) := by
        simpa only [P, fr] using perturb_jet (I := I) (M := M) g 3 (T - U) hsymm
      _ ≤ fr * D3 ^ 2 := mul_le_mul_of_nonneg_left hTU3 hfr
  have hH3 : 0 ≤ H3 := mul_nonneg hKh (by positivity)
  have hX2 : lowJetSq (I := I) (M := M) g 2 X ≤
      C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 X ≤
          C2 * lowJetSq (I := I) (M := M) g 2 P *
            lowJetSq (I := I) (M := M) g 2 LT := by
        simpa only [X] using happ2 P LT
      _ ≤ C2 * (fr * D2 ^ 2) * lowJetSq (I := I) (M := M) g 2 LT := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP2 hC2)
          (jetNn (I := I) (M := M) (m := 2) g LT)
      _ ≤ C2 * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hLT2
          (mul_nonneg hC2 (mul_nonneg hfr (sq_nonneg D2)))
  have hX3 : lowJetSq (I := I) (M := M) g 3 X ≤
      C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3) := by
    calc
      lowJetSq (I := I) (M := M) g 3 X ≤
          C3 * (lowJetSq (I := I) (M := M) g 3 P *
              lowJetSq (I := I) (M := M) g 2 LT +
            lowJetSq (I := I) (M := M) g 2 P *
              lowJetSq (I := I) (M := M) g 3 LT) := by
        simpa only [X] using happ3 P LT
      _ ≤ C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hP3 hLT2 (jetNn (I := I) (M := M) (m := 2) g LT)
            (mul_nonneg hfr (sq_nonneg D3)))
          (mul_le_mul hP2 hLT3 (jetNn (I := I) (M := M) (m := 3) g LT)
            (mul_nonneg hfr (sq_nonneg D2)))
  have hY3 : lowJetSq (I := I) (M := M) g 3 Y ≤
      C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
        (Bh R) ^ 2 *
          (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) := by
    calc
      lowJetSq (I := I) (M := M) g 3 Y ≤
          C3 * (lowJetSq (I := I) (M := M) g 3 LU *
              lowJetSq (I := I) (M := M) g 2 X +
            lowJetSq (I := I) (M := M) g 2 LU *
              lowJetSq (I := I) (M := M) g 3 X) := by
        simpa only [Y] using happ3 LU X
      _ ≤ C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) := by
        apply mul_le_mul_of_nonneg_left _ hC3
        exact add_le_add
          (mul_le_mul hLU3 hX2 (jetNn (I := I) (M := M) (m := 2) g X) hH3)
          (mul_le_mul hLU2 hX3 (jetNn (I := I) (M := M) (m := 3) g X)
            (sq_nonneg (Bh R)))
  have hYfold : lowJetSq (I := I) (M := M) g 3 Y ≤
      Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
    have heq :
        C3 * (H3 * (C2 * (fr * D2 ^ 2) * (Bh R) ^ 2) +
          (Bh R) ^ 2 *
            (C3 * ((fr * D3 ^ 2) * (Bh R) ^ 2 + (fr * D2 ^ 2) * H3))) =
        Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) := by
      simp only [H3, Z3, Z2]
      ring
    rw [heq] at hY3
    refine hY3.trans ?_
    calc
      Z3 R * D3 ^ 2 + Z2 R * ((1 + A ^ 2) * D2 ^ 2) ≤
          Z3 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) +
            Z2 R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg D2)))
            (hZ3 R))
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg D3))
            (hZ2 R))
      _ = Z R * (D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2) := by
        simp only [Z]
        ring
  have hlin : D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 ≤
      (D3 + D2 + A * D2) ^ 2 := by
    calc
      D3 ^ 2 + (1 + A ^ 2) * D2 ^ 2 =
          (D3 ^ 2 + D2 ^ 2) + (A * D2) ^ 2 := by ring
      _ ≤ (D3 + D2) ^ 2 + (A * D2) ^ 2 := by
        exact add_le_add (sqAdd2 hD3 hD2) le_rfl
      _ ≤ (D3 + D2 + A * D2) ^ 2 :=
        sqAdd2 (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hBsq : (B R) ^ 2 = Z R := by
    simpa only [B] using Real.sq_sqrt (hZ R)
  rw [invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    jetNeg (I := I) (M := M) g 3]
  have hYmain : lowJetSq (I := I) (M := M) g 3 Y ≤
      Z R * (D3 + D2 + A * D2) ^ 2 :=
    hYfold.trans (mul_le_mul_of_nonneg_left hlin (hZ R))
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU))
          (appCcRS (I := I) (M := M) g 2 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))
            (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT)))) =
      lowJetSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ Z R * (D3 + D2 + A * D2) ^ 2 := hYmain
    _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
      rw [mul_pow, hBsq]

/-! ### One-extra-slot transfer -/

private theorem insert_succ_l2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) i
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g
        (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g (s + 1) ((s + 1) + i)
      (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (s + 2) ((s + 2) + i) x
          ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
            (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)).toSection x) ≤
        F x := by
    intro x
    have heq :
        riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
                (slotInsertEndoCc (I := I) (M := M) g s Λ))).toSection x) := by
      rw [CurvatureCoefficientDifferenceJetTower.tsSlotInsertEndoCc_succ_eq_reindex_slotExtend
        (I := I) (M := M) g s Λ]
      simpa only [Nat.add_assoc] using
        rfns_iteratedCovGrad_rsDomDomCongr_both_eq
          (I := I) (M := M) g (s + 2) (s + 2)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g s Λ)) i x
    rw [heq]
    simpa only [F, Nat.add_assoc] using
      rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s Λ) i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 2) ((s + 2) + i)
    (iteratedCovGrad (I := I) g (s + 2) (s + 2) i
      (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)) F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          (s + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
            (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g (s + 1) ((s + 1) + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem insert_succ_jet
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g s Λ) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) i
          (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => insert_succ_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
            (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

namespace LowBaseInternal

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- On a fixed fibre-small metric ball, the moving one-slot trace has the
three-dimensional tame `H³` pair modulus `D3 + D2 + A * D2`. -/
theorem trace1_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 3
          (pureTrace (I := I) (M := M) g gT 1 -
            pureTrace (I := I) (M := M) g gU 1) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bi, hBi, hinv⟩ :=
    inv_slot_pair_h3 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ := app_h3_tame (I := I) (M := M) hDim g 3 3 1
  let F₁ : SmoothCcTensor g 3 1 := cometricDoubleTraceField (I := I) g 1
  let J2 : ℝ := lowJetSq (I := I) (M := M) g 2 F₁
  let J3 : ℝ := lowJetSq (I := I) (M := M) g 3 F₁
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := C * fr * (J3 + J2)
  let B : ℝ → ℝ := fun R => Real.sqrt Z * Bi R
  have hJ2 : 0 ≤ J2 := jetNn (I := I) (M := M) (m := 2) g F₁
  have hJ3 : 0 ≤ J3 := jetNn (I := I) (M := M) (m := 3) g F₁
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := mul_nonneg (mul_nonneg hC hfr) (add_nonneg hJ3 hJ2)
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBi R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let Λ := gInvDiffRaisedEndoField (I := I) g gT -
      gInvDiffRaisedEndoField (I := I) g gU
    let D₁ : SmoothCcTensor g 2 2 :=
      slotInsertEndoCc (I := I) (M := M) g 1 Λ
    let D₂ : SmoothCcTensor g 3 3 :=
      slotInsertEndoCc (I := I) (M := M) g 2 Λ
    have hQ : 0 ≤ Q :=
      add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
    have hD₁eq : D₁ =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
      dsimp only [D₁, Λ]
      rw [slotInsertEndoCc_sub,
        ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
        ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU]
    have hD₁3 : lowJetSq (I := I) (M := M) g 3 D₁ ≤
        (Bi R * Q) ^ 2 := by
      rw [hD₁eq]
      simpa only [Q] using
        hinv gT gU T U hT hU hTtie hUtie
          hδT_le hδT0 hδT hδU_le hδU0 hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    have hD₁2 : lowJetSq (I := I) (M := M) g 2 D₁ ≤
        (Bi R * Q) ^ 2 :=
      (jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) D₁).trans hD₁3
    have hD₂2 : lowJetSq (I := I) (M := M) g 2 D₂ ≤
        fr * (Bi R * Q) ^ 2 := by
      calc
        lowJetSq (I := I) (M := M) g 2 D₂ ≤
            fr * lowJetSq (I := I) (M := M) g 2 D₁ := by
          simpa only [D₂, D₁, fr] using
            insert_succ_jet (I := I) (M := M) g 1 2 Λ
        _ ≤ fr * (Bi R * Q) ^ 2 := mul_le_mul_of_nonneg_left hD₁2 hfr
    have hD₂3 : lowJetSq (I := I) (M := M) g 3 D₂ ≤
        fr * (Bi R * Q) ^ 2 := by
      calc
        lowJetSq (I := I) (M := M) g 3 D₂ ≤
            fr * lowJetSq (I := I) (M := M) g 3 D₁ := by
          simpa only [D₂, D₁, fr] using
            insert_succ_jet (I := I) (M := M) g 1 3 Λ
        _ ≤ fr * (Bi R * Q) ^ 2 := mul_le_mul_of_nonneg_left hD₁3 hfr
    have htrace :
        pureTrace (I := I) (M := M) g gT 1 -
            pureTrace (I := I) (M := M) g gU 1 =
          appCcRS (I := I) (M := M) g 3 3 1 F₁ D₂ := by
      rw [pureTrace_split (I := I) (M := M) g gT 1,
        pureTrace_split (I := I) (M := M) g gU 1]
      calc
        (appCcRS (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (gInvDiffRaisedEndoField (I := I) g gT)) + F₁) -
            (appCcRS (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (gInvDiffRaisedEndoField (I := I) g gU)) + F₁) =
          appCcRS (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (gInvDiffRaisedEndoField (I := I) g gT)) -
            appCcRS (I := I) (M := M) g 3 3 1 F₁
              (slotInsertEndoCc (I := I) (M := M) g 2
                (gInvDiffRaisedEndoField (I := I) g gU)) := by abel
        _ = appCcRS (I := I) (M := M) g 3 3 1 F₁ D₂ := by
          rw [← appCcRS_sub_right]
          congr 1
          dsimp only [D₂, Λ]
          rw [slotInsertEndoCc_sub]
    rw [htrace]
    have hmain : lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
          Z * (Bi R * Q) ^ 2 := by
      calc
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
          C * (J3 * lowJetSq (I := I) (M := M) g 2 D₂ +
            J2 * lowJetSq (I := I) (M := M) g 3 D₂) := by
              simpa only [J2, J3] using happ F₁ D₂
        _ ≤ C * (J3 * (fr * (Bi R * Q) ^ 2) +
            J2 * (fr * (Bi R * Q) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact add_le_add
            (mul_le_mul_of_nonneg_left hD₂2 hJ3)
            (mul_le_mul_of_nonneg_left hD₂3 hJ2)
        _ = Z * (Bi R * Q) ^ 2 := by
          simp only [Z]
          ring
    calc
      lowJetSq (I := I) (M := M) g 3
          (appCcRS (I := I) (M := M) g 3 3 1 F₁ D₂) ≤
        Z * (Bi R * Q) ^ 2 := hmain
      _ = (B R * Q) ^ 2 := by
        dsimp only [B]
        calc
          Z * (Bi R * Q) ^ 2 =
              (Real.sqrt Z) ^ 2 * (Bi R * Q) ^ 2 := by
            rw [Real.sq_sqrt hZ]
          _ = (Real.sqrt Z * Bi R * Q) ^ 2 := by ring
      _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
        simp only [Q]

end LowBaseInternal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
