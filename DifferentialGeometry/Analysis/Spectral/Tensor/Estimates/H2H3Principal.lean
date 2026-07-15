import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame

/-!
# Low-regularity principal operator estimate

This file controls a mixed tensor coefficient acting on the second covariant
derivative of a covariant tensor.  It keeps the coefficient hypotheses in
pointwise fibre-norm form so that geometric coefficient producers can supply
them without identifying the mixed-tensor and spectral Sobolev scales.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

private theorem grad_icg2_norm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (U : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + 2) 1
        (iteratedCovGrad (I := I) g 0 s 2 U)‖ =
      ‖iteratedCovGrad (I := I) g 0 s 3 U‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 s 3 U‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g
        (iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g (iteratedCovGrad (I := I) g 0 s 3 U),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((s + 2) + 1)
        (iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (s + 3)
        (iteratedCovGrad (I := I) g 0 s 3 U)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      rfns_iteratedCovGrad_comp (I := I) (M := M) g 0 s 2 1 U x
  nlinarith [norm_nonneg
    (iteratedCovGrad (I := I) g 0 (s + 2) 1
      (iteratedCovGrad (I := I) g 0 s 2 U)),
    norm_nonneg (iteratedCovGrad (I := I) g 0 s 3 U)]

/-- A mixed coefficient with pointwise zeroth- and first-jet bounds acts on
`nabla^2 U` from spectral `H3` to spectral `H1`. -/
theorem appCc_h3_h1
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (B0 B1 : ℝ),
        0 ≤ B0 → 0 ≤ B1 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ B0 ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + 1) x
              ((covGrad (I := I) (M := M) g (s + 2) c Φ).toSection x) ≤ B1 ^ 2) →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (appCc (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C * (B0 + B1) *
            ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g s 3
  let G0 : ℝ := appCcGdiag (E := E) 0
  let G1 : ℝ := appCcGdiag (E := E) 1
  let C0 : ℝ := Real.sqrt G0
  let C1 : ℝ := Real.sqrt (3 * G1)
  refine ⟨Csp * (C0 + C1) * Cin, by positivity, ?_⟩
  intro Φ U B0 B1 hB0 hB1 hΦ0 hΦ1
  let B : ℝ := B0 + B1
  let J : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 s j U‖
  let W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U
  let A : SmoothCcTensor g 0 c :=
    appCc (I := I) (M := M) g (s + 2) c Φ W
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hB0sq : B0 ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hB0 _ 2
    dsimp [B]
    linarith
  have hB1sq : B1 ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hB1 _ 2
    dsimp [B]
    linarith
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hW0 : ‖W‖ ≤ J := by
    dsimp [W, J]
    refine Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
      (fun _ _ => norm_nonneg _) ?_
    simp only [Finset.mem_range]
    omega
  have hW1 :
      ‖iteratedCovGrad (I := I) g 0 (s + 2) 1 W‖ ≤ J := by
    rw [show ‖iteratedCovGrad (I := I) g 0 (s + 2) 1 W‖ =
        ‖iteratedCovGrad (I := I) g 0 s 3 U‖ by
      exact grad_icg2_norm (I := I) (M := M) g s U]
    dsimp [J]
    refine Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
      (fun _ _ => norm_nonneg _) ?_
    simp only [Finset.mem_range]
    omega
  have hW1' : ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ≤ J := by
    simpa only [iteratedCovGrad_succ, Nat.add_zero] using hW1
  let K : ℕ → ℝ := fun _ => B ^ 2
  have hK : ∀ i, i ≤ 1 → 0 ≤ K i := fun _ _ => sq_nonneg B
  have hΦK : ∀ i, i ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + i) x
          ((iteratedCovGrad (I := I) g (s + 2) c i Φ).toSection x) ≤ K i := by
    intro i hi x
    interval_cases i
    · simpa [K] using (hΦ0 x).trans hB0sq
    · simpa [K, iteratedCovGrad_succ] using (hΦ1 x).trans hB1sq
  have hsq0raw := appCc_jet_l2Sq_le (I := I) (M := M) g (s + 2) c 0
    Φ W K (fun i hi => hK i (by omega))
    (fun i hi => hΦK i (by omega))
  have hsq1raw := appCc_jet_l2Sq_le (I := I) (M := M) g (s + 2) c 1
    Φ W K hK hΦK
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    Nat.add_zero, Nat.zero_add, Nat.reduceSub, iteratedCovGrad_zero,
    iteratedCovGrad_succ] at hsq0raw hsq1raw
  dsimp [K] at hsq0raw hsq1raw
  have hsq0raw' :
      ‖appCc (I := I) (M := M) g (s + 2) c Φ W‖ ^ 2 ≤
        appCcGdiag (E := E) 0 * (B ^ 2 * ‖W‖ ^ 2) := by
    simpa only [zero_add] using hsq0raw
  have hsq1raw' :
      ‖covGrad (I := I) (M := M) g 0 c
          (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤
        appCcGdiag (E := E) 1 *
          (B ^ 2 * (‖W‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
            B ^ 2 * ‖W‖ ^ 2) := by
    simpa only [zero_add] using hsq1raw
  have hsq0 : ‖A‖ ^ 2 ≤ G0 * B ^ 2 * J ^ 2 := by
    dsimp [A]
    calc
      ‖appCc (I := I) (M := M) g (s + 2) c Φ W‖ ^ 2
          ≤ appCcGdiag (E := E) 0 * (B ^ 2 * ‖W‖ ^ 2) := hsq0raw'
      _ ≤ appCcGdiag (E := E) 0 * (B ^ 2 * J ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg W) hW0 2) (sq_nonneg B))
          (appCcGdiag_nonneg (E := E) 0)
      _ = G0 * B ^ 2 * J ^ 2 := by dsimp [G0]; ring
  have hsq1 :
      ‖iteratedCovGrad (I := I) g 0 c 1 A‖ ^ 2 ≤
        (3 * G1) * B ^ 2 * J ^ 2 := by
    have hW0sq := pow_le_pow_left₀ (norm_nonneg W) hW0 2
    have hW1sq := pow_le_pow_left₀
      (norm_nonneg (covGrad (I := I) (M := M) g 0 (s + 2) W)) hW1' 2
    dsimp [A]
    change ‖covGrad (I := I) (M := M) g 0 c
        (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤ _
    calc
      ‖covGrad (I := I) (M := M) g 0 c
          (appCc (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2
          ≤ appCcGdiag (E := E) 1 *
              (B ^ 2 * (‖W‖ ^ 2 +
                ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
                B ^ 2 * ‖W‖ ^ 2) := hsq1raw'
      _ ≤ appCcGdiag (E := E) 1 * (3 * B ^ 2 * J ^ 2) :=
        mul_le_mul_of_nonneg_left
          (show B ^ 2 * (‖W‖ ^ 2 +
                ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
                B ^ 2 * ‖W‖ ^ 2 ≤ 3 * B ^ 2 * J ^ 2 by
              nlinarith [sq_nonneg B, sq_nonneg J])
          (appCcGdiag_nonneg (E := E) 1)
      _ = (3 * G1) * B ^ 2 * J ^ 2 := by dsimp [G1]; ring
  have hA0 : ‖A‖ ≤ C0 * B * J := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (appCcGdiag_nonneg (E := E) 0)]
    simpa [C0, G0, mul_assoc] using hsq0
  have hA1 : ‖iteratedCovGrad (I := I) g 0 c 1 A‖ ≤ C1 * B * J := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (appCcGdiag_nonneg (E := E) 1))]
    simpa [C1, G1, mul_assoc] using hsq1
  have hspA :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤
        Csp * (‖A‖ + ‖iteratedCovGrad (I := I) g 0 c 1 A‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp A
  have hAJ :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤
        Csp * ((C0 + C1) * B * J) := by
    refine le_trans hspA (mul_le_mul_of_nonneg_left ?_ hCsp)
    calc
      ‖A‖ + ‖iteratedCovGrad (I := I) g 0 c 1 A‖
          ≤ C0 * B * J + C1 * B * J := add_le_add hA0 hA1
      _ = (C0 + C1) * B * J := by ring
  have hJU : J ≤ Cin *
      ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
    simpa [J] using hin U
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤ _
  calc
    ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖
        ≤ Csp * ((C0 + C1) * B * J) := hAJ
    _ ≤ Csp * ((C0 + C1) * B *
          (Cin * ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJU
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB))
        hCsp
    _ = (Csp * (C0 + C1) * Cin) * (B0 + B1) *
          ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
      dsimp [B]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
