import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertProducers
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower

/-! # Radius-free DeTurck vector-field endo-insert jet-L² tower (brick 3b)

Radius-free (`R`-free) siblings of the private DeTurck-vector-field jet-L² tower in
`DeTurckVFEndoInsertProducers`, built on THE GATE / workhorse
(`antidiagonalTupleGrid_integral_radiusFree`) from `CurvatureCoefficientDifferenceJetTower`.  These
discharge (in later 3b sessions) the frontier `deTurckLieCoeffField_perOrder_l2_radiusFree`
(`DeTurckLieCoeffDiffRadiusFree.lean`, one flagged `sorry`).  The arm0 exemplar is
`CurvatureCoeffDiffRadiusFree.lean`; see `DeTurckVFJetRadiusFree.md` and `ShortTime/THREEARM_RECON.md`
§11c/§11d.

Each R-dependent bottom producer converts `∫ grid_q` (the antidiagonal-tuple product grid over the
`P`-jets) into a FLAT `R`-dependent constant via the ball-uniform integrator
`diagonalProductGrid_rfns_integral_ballUniform_succ` (needs `hPball : ∀ j ≤ a+2, ‖∇ʲP‖ ≤ R`).  The
workhorse `antidiagonalTupleGrid_integral_radiusFree` has the byte-identical integrand and instead
yields `∫ grid_q ≤ K_rf q · (1 + ‖∇^q P‖²)` from only the order-0 fibre bound
`hsup : ∀ x, rfns g₀ 0 2 x (P.toSection x) ≤ Λ₀²`.  Swapping it turns the producer's flat `F i` into
a LOW WINDOW `Flow i · (1 + ∑_{j≤i} ‖∇ʲP‖²)` with `Flow` radius-free.  The three split parts
(`DeTurckVFEndoInsert{Tower,Producers,TopSep}`) are read-only. -/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ### Radius-free `cometricCastG0` low-order producer.

Radius-free sibling of `cometricCastG0_order0sup_jetL2_succ_generic`
(`DeTurckVFEndoInsertProducers.lean:834`).  The single ball-uniform integration step (bounding the
`gInvDiff` endo `W`-jets) is replaced by the radius-free workhorse; the resulting per-order flat
constant `F i` becomes the low window `Flow i · (1 + ∑_{j≤i} ‖∇ʲP‖²)`.  The order-0 sup `Λ` is
already radius-free (it uses only the fibre bound at order 0, where the antidiagonal grid degenerates
to `1`). -/
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem cometricCastG0_order0sup_jetL2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ (Λ : ℝ) (Flow : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW_rf : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_rf q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW_rf q := by
    intro q; simp only [hKW_def]
    exact mul_nonneg (mul_nonneg (sq_nonneg fr) (hC_base_nn q)) (hK_rf_nn q)
  set aL : ℕ → ℝ := fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  set kd : ℕ → ℝ := fun l => appCcGdiag (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * (∑ q ∈ Finset.range (l + 1), KW_rf q) with hkd_def
  have hkd_nn : ∀ l, 0 ≤ kd l := by
    intro l; simp only [hkd_def]
    exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg _)
      (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) (Finset.sum_nonneg (fun q _ => hKW_nn q))
  set ΛT2 : ℝ := fr ^ 2 * C_base 0 with hΛT2_def
  have hΛT2_nn : 0 ≤ ΛT2 := by rw [hΛT2_def]; exact mul_nonneg (sq_nonneg fr) (hC_base_nn 0)
  refine ⟨Real.sqrt (2 * SΦ 0 + 2 * (SΦ 0 * ΛT2)),
    fun i => ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l), Real.sqrt_nonneg _,
    fun i => Finset.sum_nonneg (fun l _ => by
      have h1 : 0 ≤ aL l := by simp only [haL_def]; positivity
      have h2 : 0 ≤ kd l := hkd_nn l
      linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup
  set W : SmoothCcTensor g₀ 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁) with hW_def
  have hid : cometricCastG0 (I := I) g₀ g₁ =
      Φ + appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W := by
    have h := cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
    rw [← hΦ_def, ← hW_def] at h
    exact h
  -- order-0 W sup: `rfns(W) ≤ ΛT2` (fibre bound at order 0, grid₀ = 1).
  have hΛT : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x) ≤ ΛT2 := by
    intro x
    have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) 0 x
    simp only [iteratedCovGrad_zero] at h1
    rw [← hW_def, ← hfr_def] at h1
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ 0 x
    simp only [iteratedCovGrad_zero] at h2
    have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
        ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by simp
    rw [hgrid0, mul_one] at h2
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) := h1
      _ ≤ fr ^ 2 * C_base 0 := mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
      _ = ΛT2 := hΛT2_def.symm
  -- W L² jets via the workhorse: `‖∇^q W‖² ≤ KW_rf q · (1 + ‖∇^q P‖²)`.
  have hstep2 : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤
        KW_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    intro q
    have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
          fr ^ 2 * C_base q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
      rw [← hW_def, ← hfr_def] at h1
      have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
          ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 1 1 q
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
        _ ≤ fr ^ 2 * (C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
        _ = fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
    obtain ⟨hgi, hgb⟩ := hK_rf P hsup q
    have hint : MeasureTheory.Integrable
        (fun x => fr ^ 2 * C_base q *
          (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
      (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    rw [hKW_def]
    calc fr ^ 2 * C_base q *
          (∫ x, ∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ fr ^ 2 * C_base q * (K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgb (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
      _ = fr ^ 2 * C_base q * K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by ring
  -- Now the main per-order body over i.
  refine ⟨?_, ?_⟩
  · -- order-0 sup of cometricCastG0.
    intro x
    rw [Real.sq_sqrt (by
      have := hSΦ_nn 0
      have := mul_nonneg (hSΦ_nn 0) hΛT2_nn
      linarith : (0 : ℝ) ≤ 2 * SΦ 0 + 2 * (SΦ 0 * ΛT2))]
    rw [hid, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 1 x
      (Φ.toSection x) ((appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x)) ?_
    have hΦ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (Φ.toSection x) ≤ SΦ 0 := by
      have h := hSΦ 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    have hDIFF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        ((appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x) ≤ SΦ 0 * ΛT2 := by
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 3 1 x
        (Φ.toSection x) (W.toSection x)) ?_
      exact mul_le_mul hΦ0 (hΛT x) (riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn 0)
    linarith
  · -- low-window L² jet bound over i.
    intro i hi
    set S : ℝ := ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    -- appCcRS L² jets: `‖∇^l appCcRS‖² ≤ kd l · (1 + S)`.
    have hstep3 : ∀ l : ℕ, l ≤ i →
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
          kd l * (1 + S) := by
      intro l hl
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 1 l
                (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
            (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) := by
        intro x
        refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg _)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun i' _ => ?_)
        refine mul_le_mul (hSΦ i' x) ?_
          (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        intro q hq
        rw [Finset.mem_range] at hq ⊢
        omega
      have hint : MeasureTheory.Integrable
          (fun x => (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.integrable_finset_sum
        intro q _
        exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
        (iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum _ (fun q _ =>
          integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W))]
      have hconv : ∀ q ∈ Finset.range (l + 1),
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 := by
        intro q _
        rw [SmoothCcTensor.norm_def,
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)]
      rw [Finset.sum_congr rfl hconv]
      -- Route `∑_{q≤l} ‖∇^q W‖²` (workhorse) into `(∑ KW_rf q) · (1 + S)`.
      have hWsum : (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2) ≤
          (∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S) := by
        calc (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2)
            ≤ ∑ q ∈ Finset.range (l + 1),
                KW_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) :=
              Finset.sum_le_sum (fun q _ => hstep2 q)
          _ ≤ ∑ q ∈ Finset.range (l + 1), KW_rf q * (1 + S) := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (hKW_nn q)
              have hqle : q ≤ i := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) hl
              have hjmem : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ S :=
                Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
                  (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
              linarith
          _ = (∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S) := by rw [Finset.sum_mul]
      calc (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2)
          ≤ (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              ((∑ q ∈ Finset.range (l + 1), KW_rf q) * (1 + S)) :=
            mul_le_mul_of_nonneg_left hWsum
              (mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        _ = kd l * (1 + S) := by rw [hkd_def]; ring
    -- Per-order assembly: `‖∇^l cometricCastG0‖² ≤ (2 aL l + 2 kd l)·(1 + S)`.
    have hterm : ∀ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
          (2 * aL l + 2 * kd l) * (1 + S) := by
      intro l hl
      have hl_i : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [hid, iteratedCovGrad_add]
      have hKDl := hstep3 l hl_i
      have haLl : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
      have hkd_l_nn : 0 ≤ kd l := hkd_nn l
      have haL_l_nn : 0 ≤ aL l := by simp only [haL_def]; positivity
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
          iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)))
        (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
          (iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
      nlinarith [hsq, hKDl, haLl, hS_nn, hkd_l_nn, haL_l_nn,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (appCcRS (I := I) (M := M) g₀ 3 3 1 Φ W)‖),
        mul_nonneg hkd_l_nn hS_nn, mul_nonneg haL_l_nn hS_nn]
    calc ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2
        ≤ ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l) * (1 + S) :=
          Finset.sum_le_sum hterm
      _ = (∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * kd l)) * (1 + S) := by rw [Finset.sum_mul]

/-! ### Radius-free `sharpFlatEndoCc` low-order producer.

Radius-free sibling of `sharpFlatEndoCc_lowOrder_jetL2_succ_generic`
(`DeTurckVFEndoInsertProducers.lean:1314`).  `sharpFlatEndoCc = DiffIns + IdIns` where
`DiffIns = slotInsertEndoCc g₀ 0 (gInvDiffRaisedEndoField g₀ g₁)` carries the perturbation and
`IdIns = slotInsertEndoCc g₀ 0 (fullRaisedEndoField g₀ g₀)` is `T`-independent.  The `DiffIns` grid
is integrated by the radius-free workhorse (byte-identical integrand, order-0 fibre input `Λ₀`); the
`IdIns` jets are a `T`-free constant.  The decomposition helpers are re-derived here (their originals
are `private` in the read-only Producers split part; every sibling re-derives them). -/

private lemma gInvRaisedEndo_self_rf (g₀ : SmoothRiemannianMetric I M) (x : M) :
    gInvRaisedEndo (I := I) g₀ g₀ x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM, ContinuousLinearMap.id_apply]

private lemma fullRaisedEndoField_decomp_rf (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) =
      gInvDiffRaisedEndo (I := I) g₀ g₁ x from rfl]
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_self_rf, ContinuousLinearMap.id_apply]
  rw [gInvRaisedEndo_eq_diff_add_id]

private lemma slotInsertEndoCc_add_rf (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

private lemma sharpFlatEndoCc_eq_insert_fullRaised_rf (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g₀ g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g₀ g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om (gInvRaisedEndo (I := I) g₀ g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (gInvRaisedEndo (I := I) g₀ g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (gInvRaisedEndo (I := I) g₀ g₁ x w)).symm]
  rw [show gInvRaisedEndo (I := I) g₀ g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w) from by
    rw [gInvRaisedEndo_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g₀.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem sharpFlatEndoCc_lowOrder_jetL2_radiusFree
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ (Λ : ℝ) (Flow : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ Flow i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a + 1 →
          ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
            Flow i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_rf, hK_rf_nn, hK_rf⟩ :=
    antidiagonalTupleGrid_integral_radiusFree (I := I) (M := M) g₀ hΛ₀0
  have hSId_ex : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 1 n IdIns).toSection x) ≤ K :=
    fun n => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 (1 + n)
      (iteratedCovGrad (I := I) g₀ 1 1 n IdIns)
  choose SId hSId_nn hSId using hSId_ex
  set KW : ℕ → ℝ := fun q => C_base q * K_rf q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q => mul_nonneg (hC_base_nn q) (hK_rf_nn q)
  set FId : ℕ → ℝ := fun q => ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 with hFId_def
  have hFId_nn : ∀ q, 0 ≤ FId q := fun q => sq_nonneg _
  refine ⟨Real.sqrt (2 * C_base 0 + 2 * SId 0),
    fun i => ∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q), Real.sqrt_nonneg _,
    fun i => Finset.sum_nonneg (fun q _ => by
      have := hKW_nn q; have := hFId_nn q; linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [sharpFlatEndoCc_eq_insert_fullRaised_rf (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_decomp_rf (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_rf (I := I) (M := M) g₀ 0]
  -- Pointwise `DiffIns` grid bound (slot 0, direct from `hC_base`).
  have hDiff_pt : ∀ (n : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 1 n DiffIns).toSection x) ≤
        C_base n *
          (∑ m ∈ Finset.range (n + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m n,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) := by
    intro n x
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ n x
    rw [← hDiffIns_def] at h2
    exact h2
  -- `DiffIns` L² jets via the workhorse.
  have hDiff2 : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤
        KW q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    intro q
    obtain ⟨hgi, hgb⟩ := hK_rf P hsup q
    have hint : MeasureTheory.Integrable
        (fun x => C_base q *
          (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint (fun x => hDiff_pt q x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul, hKW_def]
    calc C_base q *
          (∫ x, ∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
            ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C_base q * (K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgb (hC_base_nn q)
      _ = C_base q * K_rf q * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · -- order-0 sup of sharpFlatEndoCc.
    intro x
    rw [Real.sq_sqrt (by have := hC_base_nn 0; have := hSId_nn 0; linarith :
      (0 : ℝ) ≤ 2 * C_base 0 + 2 * SId 0)]
    rw [hdecomp, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 1 x
      (DiffIns.toSection x) (IdIns.toSection x)) ?_
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) ≤
        C_base 0 := by
      have h := hDiff_pt 0 x
      simp only [iteratedCovGrad_zero] at h
      have hgrid0 : (∑ m ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m 0,
          ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection x)) = 1 := by simp
      rw [hgrid0, mul_one] at h
      exact h
    have hI0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) ≤ SId 0 := by
      have h := hSId 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    linarith
  · -- low-window L² jet bound over i.
    intro i hi
    set S : ℝ := ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hterm : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
          (2 * KW q + 2 * FId q) * (1 + S) := by
      intro q hq
      have hq_i : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      rw [hdecomp, iteratedCovGrad_add]
      have hDq := hDiff2 q
      have hFIdq : FId q = ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := by simp only [hFId_def]
      have hKW_q_nn : 0 ≤ KW q := hKW_nn q
      have hFId_q_nn : 0 ≤ FId q := hFId_nn q
      have hPqS : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ S :=
        Finset.single_le_sum (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns +
          iteratedCovGrad (I := I) g₀ 1 1 q IdIns))
        (norm_add_le (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns)
          (iteratedCovGrad (I := I) g₀ 1 1 q IdIns)) 2
      nlinarith [hsq, hDq, hFIdq, hKW_q_nn, hFId_q_nn, hS_nn, hPqS,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖),
        mul_nonneg hKW_q_nn hS_nn, mul_nonneg hFId_q_nn hS_nn]
    calc ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2
        ≤ ∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q) * (1 + S) :=
          Finset.sum_le_sum hterm
      _ = (∑ q ∈ Finset.range (i + 1), (2 * KW q + 2 * FId q)) * (1 + S) := by rw [Finset.sum_mul]

end DifferentialGeometry.Integral.Connection
