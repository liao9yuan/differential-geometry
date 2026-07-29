import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegPathSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSRefoldPathIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCoeffH2
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H4Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

/-!
# Low-base Ricci--DeTurck remainder actions

This module isolates the complete second-order action after subtracting the
fixed background connection Laplacian.  The decomposition is exact and uses
only the realized metric segment; no high Sobolev ball is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem bfg_two_three (b : Nat → Real) :
    Combinatorics.boundedFactorGridWindow b 2 3 =
      ∑ k ∈ Finset.range 3, Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.boundedFactorGridWindow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact (Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid
    b (K := 2) (show k ≤ 2 by omega)).symm

private theorem h2_window_three
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : Real) T‖ ≤ 1 →
      Integrable
          (fun x => Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
              ((iteratedCovGrad (I := I) g 0 2 l T).toSection x)) 2 3)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
              ((iteratedCovGrad (I := I) g 0 2 l T).toSection x)) 2 3
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ C := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g 2
  obtain ⟨Cjet, hCjet, hjet⟩ := hs2_low2 (I := I) (M := M) g 2
  obtain ⟨K, hK, hgrid⟩ :=
    antidiagonalTupleGrid_integral_radiusFree
      (I := I) (M := M) g hCpt
  let C : Real := ∑ k ∈ Finset.range 3, K k * (1 + Cjet ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hK k) (add_nonneg zero_le_one (sq_nonneg Cjet))
  refine ⟨C, hC, ?_⟩
  intro T hT
  let N : Real := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : Real) T‖
  let b : M → Nat → Real := fun x l =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
      ((iteratedCovGrad (I := I) g 0 2 l T).toSection x)
  have hN : 0 ≤ N := norm_nonneg _
  have hN1 : N ≤ 1 := by simpa [N] using hT
  have hN_sq : N ^ 2 ≤ 1 := by nlinarith
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
        Cpt ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
          ≤ Cpt ^ 2 * N ^ 2 := by simpa [N] using hpt T x
      _ ≤ Cpt ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hN_sq (sq_nonneg Cpt)
      _ = Cpt ^ 2 := mul_one _
  have hgrid' : ∀ k : Nat,
      Integrable (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          K k * (1 + ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2) := by
    intro k
    simpa only [Combinatorics.antidiagonalTupleGrid, b] using
      hgrid T hsup k
  have hjets : ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ Cjet ^ 2 := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2
          ≤ (Cjet * N) ^ 2 := by simpa [N] using hjet T
      _ = Cjet ^ 2 * N ^ 2 := by ring
      _ ≤ Cjet ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hN_sq (sq_nonneg Cjet)
      _ = Cjet ^ 2 := mul_one _
  have hjet_one : ∀ k ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 ≤ Cjet ^ 2 := by
    intro k hk
    exact (Finset.single_le_sum
      (f := fun j : Nat => ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
      (fun j _ => sq_nonneg _) hk).trans hjets
  have hwin : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) 2 3 =
        ∑ k ∈ Finset.range 3, Combinatorics.antidiagonalTupleGrid (b x) k :=
    fun x => bfg_two_three (b x)
  have hsum_int : Integrable
      (fun x => ∑ k ∈ Finset.range 3,
        Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_finset_sum (Finset.range 3) fun k _ => (hgrid' k).1
  refine ⟨by simpa only [hwin] using hsum_int, ?_⟩
  calc
    (∫ x, Combinatorics.boundedFactorGridWindow (b x) 2 3
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, ∑ k ∈ Finset.range 3,
          Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_congr_ae (Eventually.of_forall hwin)
    _ = ∑ k ∈ Finset.range 3,
        ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_finset_sum (Finset.range 3) fun k _ => (hgrid' k).1
    _ ≤ ∑ k ∈ Finset.range 3, K k * (1 + Cjet ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hgrid' k).2.trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (le_refl 1) (hjet_one k hk)) (hK k))
    _ = C := rfl

/-- On a three-dimensional small spectral `H2` metric ball, the moving
pair-contracted coefficient has a uniform `L2` bound through two covariant derivatives. -/
theorem mvPair_h2_ball
    (hDim : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : Real, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : Real) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 2 j
            (mvPairTraceOp (I := I) (M := M) g g₁)‖ ^ 2 ≤ C ^ 2 := by
  classical
  obtain ⟨Cop, hCop, hop⟩ := hs2_op_bound (I := I) (M := M) hDim g
  obtain ⟨Cwin, hCwin, hwin⟩ := h2_window_three (I := I) (M := M) hDim g
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    exists_rfns_icg_mvPairTraceOp_window
      (I := I) (M := M) g (show (1 / 2 : Real) < 1 by norm_num)
  let ρ : Real := min 1 (2 * Cop)⁻¹
  let Ksq : Real := (∑ j ∈ Finset.range 3, Cpt j) * Cwin
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min zero_lt_one (inv_pos.mpr (mul_pos (by norm_num) hCop))
  have hKsq : 0 ≤ Ksq := by
    dsimp [Ksq]
    exact mul_nonneg (Finset.sum_nonneg fun j _ => hCpt j) hCwin
  refine ⟨ρ, Real.sqrt Ksq, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T g₁ hT htie
  let N : Real := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : Real) T‖
  let δ : Real := Cop * N
  let b : M → Nat → Real := fun x l =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + l) x
      ((iteratedCovGrad (I := I) g 0 2 l T).toSection x)
  have hN : 0 ≤ N := norm_nonneg _
  have hNρ : N ≤ ρ := by simpa [N] using hT
  have hN1 : N ≤ 1 :=
    hNρ.trans (by dsimp [ρ]; exact min_le_left _ _)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    calc
      δ = Cop * N := rfl
      _ ≤ Cop * ρ := mul_le_mul_of_nonneg_left hNρ (le_of_lt hCop)
      _ ≤ Cop * (2 * Cop)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (by dsimp [ρ]; exact min_le_right _ _) (le_of_lt hCop)
      _ = 1 / 2 := by field_simp [ne_of_gt hCop]
  have hbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ := by
    simpa [δ, N] using hop T
  have hwinT :
      Integrable
          (fun x => Combinatorics.boundedFactorGridWindow (b x) 2 3)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.boundedFactorGridWindow (b x) 2 3
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ Cwin := by
    simpa only [b] using hwin T hN1
  have hb_nn : ∀ x : M, ∀ l : Nat, 0 ≤ b x l := by
    intro x l
    exact riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 (2 + l) x _
  have hj_bound : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (mvPairTraceOp (I := I) (M := M) g g₁)‖ ^ 2 ≤ Cpt j * Cwin := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hpt_j : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 6 (2 + j) x
            ((iteratedCovGrad (I := I) g 6 2 j
              (mvPairTraceOp (I := I) (M := M) g g₁)).toSection x) ≤
          Cpt j * Combinatorics.boundedFactorGridWindow (b x) 2 3 := by
      intro x
      calc
        riemannianFiberNormSq (I := I) (M := M) g 6 (2 + j) x
            ((iteratedCovGrad (I := I) g 6 2 j
              (mvPairTraceOp (I := I) (M := M) g g₁)).toSection x)
            ≤ Cpt j * Combinatorics.boundedFactorGridWindow (b x) 2 (j + 1) := by
              simpa only [b] using
                hpt g₁ T htie hδhalf hδ hbound j 2 (by omega) x
        _ ≤ Cpt j * Combinatorics.boundedFactorGridWindow (b x) 2 3 :=
          mul_le_mul_of_nonneg_left
            (Combinatorics.boundedFactorGridWindow_mono
              (b x) (hb_nn x) (le_refl 2) (by omega)) (hCpt j)
    have hscaled : Integrable
        (fun x => Cpt j * Combinatorics.boundedFactorGridWindow (b x) 2 3)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hwinT.1.const_mul (Cpt j)
    refine (normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 6 (2 + j)
      (iteratedCovGrad (I := I) g 6 2 j
        (mvPairTraceOp (I := I) (M := M) g g₁))
      _ hscaled hpt_j).trans ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hwinT.2 (hCpt j)
  calc
    ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 2 j
          (mvPairTraceOp (I := I) (M := M) g g₁)‖ ^ 2
        ≤ ∑ j ∈ Finset.range 3, Cpt j * Cwin := by
          exact Finset.sum_le_sum fun j hj => hj_bound j hj
    _ = (∑ j ∈ Finset.range 3, Cpt j) * Cwin := by
      rw [Finset.sum_mul]
    _ = Ksq := rfl
    _ = (Real.sqrt Ksq) ^ 2 := (Real.sq_sqrt hKsq).symm

private def edgeArg
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
    (slotExtendTwo (I := I) (M := M) g
      (domDomCongrSection (I := I) g
        (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G))

private theorem edgeArg_perm
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (6 + j) x
        ((iteratedCovGrad (I := I) g 2 6 j
          (edgeArg (I := I) (M := M) g G σ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (6 + j) x
        ((iteratedCovGrad (I := I) g 2 6 j
          (slotExtendTwo (I := I) (M := M) g
            (domDomCongrSection (I := I) g
              (σ.trans (Equiv.swap (0 : Fin 4) 2 *
                Equiv.swap (1 : Fin 4) 3)) G))).toSection x) := by
  unfold edgeArg
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g 2 6 sigmaE
    (slotExtendTwo (I := I) (M := M) g
      (domDomCongrSection (I := I) g
        (σ.trans (Equiv.swap (0 : Fin 4) 2 *
          Equiv.swap (1 : Fin 4) 3)) G))
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
      (slotExtendTwo (I := I) (M := M) g
        (domDomCongrSection (I := I) g
          (σ.trans (Equiv.swap (0 : Fin 4) 2 *
            Equiv.swap (1 : Fin 4) 3)) G)))
    (fun y d => ?_) j x
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]

private theorem edgeArg_rfns
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (6 + j) x
        ((iteratedCovGrad (I := I) g 2 6 j
          (edgeArg (I := I) (M := M) g G σ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j G).toSection x) := by
  let X : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)) G
  let Y : SmoothCcTensor g 1 5 :=
    slotExtend (I := I) (M := M) g 0 4 X
  have houter :=
    rfns_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g 1 5 Y j x
  have hinner :=
    rfns_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g 0 4 X j x
  have hperm :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g
      (σ.trans (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))
      G j x
  rw [edgeArg_perm (I := I) (M := M) g G σ j x]
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g 1 (5 + j) x
          ((iteratedCovGrad (I := I) g 1 5 j Y).toSection x) := by
      simpa only [slotExtendTwo, X, Y, Nat.reduceAdd] using houter
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
            ((iteratedCovGrad (I := I) g 0 4 j X).toSection x)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Nat.reduceAdd] using hinner)
        (Nat.cast_nonneg _)
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j G).toSection x) := by
      rw [show
        riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
            ((iteratedCovGrad (I := I) g 0 4 j X).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
            ((iteratedCovGrad (I := I) g 0 4 j G).toSection x) by
        simpa only [X] using hperm]
      ring

private theorem edgeArg_norm_sq
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 6 j
        (edgeArg (I := I) (M := M) g G σ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 := by
  let d : ℝ := (Module.finrank ℝ E : ℝ)
  let F : M → ℝ := fun x =>
    d ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
      ((iteratedCovGrad (I := I) g 0 4 j G).toSection x)
  have hF : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 0 (4 + j)
      (iteratedCovGrad (I := I) g 0 4 j G)).const_mul (d ^ 2)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 2 (6 + j)
    (iteratedCovGrad (I := I) g 2 6 j
      (edgeArg (I := I) (M := M) g G σ))
    F hF (fun x => by
      simpa only [F, d] using edgeArg_rfns
        (I := I) (M := M) g G σ j x)
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul,
    ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g 0 (4 + j)
      (iteratedCovGrad (I := I) g 0 4 j G),
    DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm]
    at hsq
  simpa only [d] using hsq

private theorem edgeArg_norm
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 6 j
        (edgeArg (I := I) (M := M) g G σ)‖ ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
  have hsq := edgeArg_norm_sq (I := I) (M := M) g G σ j
  have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 4 j G‖ := norm_nonneg _
  have hleft :
      0 ≤ ‖iteratedCovGrad (I := I) g 2 6 j
        (edgeArg (I := I) (M := M) g G σ)‖ := norm_nonneg _
  apply (sq_le_sq₀ hleft (mul_nonneg hd hn)).1
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 := hsq
    _ = ((Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 := by ring

private def edgeKernelArg
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (q : Fin 4 → Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 6 :=
  (1 / 2 : ℝ) •
    (edgeArg (I := I) (M := M) g G (q 0) +
      edgeArg (I := I) (M := M) g G (q 1) -
      edgeArg (I := I) (M := M) g G (q 2) -
      edgeArg (I := I) (M := M) g G (q 3))

private def edgeLieArg
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (q : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 6 :=
  (1 / 2 : ℝ) •
    (edgeArg (I := I) (M := M) g G q +
      edgeArg (I := I) (M := M) g G
        (q.trans (Equiv.swap (0 : Fin 4) 1)))

private theorem edgeKernel_norm
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (q : Fin 4 → Equiv.Perm (Fin 4)) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 6 j
        (edgeKernelArg (I := I) (M := M) g G q)‖ ≤
      2 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
  let A : Fin 4 → SmoothCcTensor g 2 (6 + j) := fun k =>
    iteratedCovGrad (I := I) g 2 6 j
      (edgeArg (I := I) (M := M) g G (q k))
  have hiter :
      iteratedCovGrad (I := I) g 2 6 j
          (edgeKernelArg (I := I) (M := M) g G q) =
        (1 / 2 : ℝ) • (A 0 + A 1 - A 2 - A 3) := by
    rw [edgeKernelArg, iteratedCovGrad_smul, iteratedCovGrad_sub,
      iteratedCovGrad_sub, iteratedCovGrad_add]
  have htri :
      ‖A 0 + A 1 - A 2 - A 3‖ ≤
        ((‖A 0‖ + ‖A 1‖) + ‖A 2‖) + ‖A 3‖ := by
    calc
      _ ≤ ‖A 0 + A 1 - A 2‖ + ‖A 3‖ := norm_sub_le _ _
      _ ≤ (‖A 0 + A 1‖ + ‖A 2‖) + ‖A 3‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ ≤ ((‖A 0‖ + ‖A 1‖) + ‖A 2‖) + ‖A 3‖ :=
        add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
  have hA : ∀ k : Fin 4,
      ‖A k‖ ≤ (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
    intro k
    simpa only [A] using
      edgeArg_norm (I := I) (M := M) g G (q k) j
  rw [hiter, norm_smul, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
  calc
    (1 / 2 : ℝ) * ‖A 0 + A 1 - A 2 - A 3‖ ≤
        (1 / 2 : ℝ) * (((‖A 0‖ + ‖A 1‖) + ‖A 2‖) + ‖A 3‖) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        ((((Module.finrank ℝ E : ℝ) *
              ‖iteratedCovGrad (I := I) g 0 4 j G‖ +
            (Module.finrank ℝ E : ℝ) *
              ‖iteratedCovGrad (I := I) g 0 4 j G‖) +
          (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g 0 4 j G‖) +
        (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g 0 4 j G‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (add_le_add (add_le_add (hA 0) (hA 1)) (hA 2)) (hA 3)
    _ = 2 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by ring

private theorem edgeLieArg_norm
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (q : Equiv.Perm (Fin 4)) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 6 j
        (edgeLieArg (I := I) (M := M) g G q)‖ ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
  let A : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeArg (I := I) (M := M) g G q)
  let B : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeArg (I := I) (M := M) g G
        (q.trans (Equiv.swap (0 : Fin 4) 1)))
  have hiter :
      iteratedCovGrad (I := I) g 2 6 j
          (edgeLieArg (I := I) (M := M) g G q) =
        (1 / 2 : ℝ) • (A + B) := by
    rw [edgeLieArg, iteratedCovGrad_smul, iteratedCovGrad_add]
  have hA : ‖A‖ ≤ (Module.finrank ℝ E : ℝ) *
      ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
    simpa only [A] using edgeArg_norm (I := I) (M := M) g G q j
  have hB : ‖B‖ ≤ (Module.finrank ℝ E : ℝ) *
      ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
    simpa only [B] using edgeArg_norm (I := I) (M := M) g G
      (q.trans (Equiv.swap (0 : Fin 4) 1)) j
  rw [hiter, norm_smul, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
  calc
    (1 / 2 : ℝ) * ‖A + B‖ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖B‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g 0 4 j G‖ +
          (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g 0 4 j G‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ = (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by ring

private def rhsPairArg
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (s : ℝ) : SmoothCcTensor g 2 6 :=
  (2 : ℝ) • (s • ((1 / 2 : ℝ) •
    (edgeKernelArg (I := I) (M := M) g G ricciRefoldQA +
      edgeKernelArg (I := I) (M := M) g G ricciRefoldQB))) +
    s • ∑ i : Fin 3, lieRefoldEps i •
      edgeLieArg (I := I) (M := M) g G (lieRefoldQ i)

/-- Pair-contracted action corresponding to the complete second-order Ricci--DeTurck
refold, with an arbitrary rank-four passenger. -/
def rhsRefoldPair
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (s : Real) : SmoothCcTensor g 2 2 :=
  (2 : Real) • (s • ((1 / 2 : Real) •
    (edgeKernelPair (I := I) (M := M) g gm G ricciRefoldQA +
      edgeKernelPair (I := I) (M := M) g gm G ricciRefoldQB))) +
    s • ∑ i : Fin 3, lieRefoldEps i • ((1 / 2 : Real) •
      (edgePairMono (I := I) (M := M) g gm G (lieRefoldQ i) +
        edgePairMono (I := I) (M := M) g gm G
          ((lieRefoldQ i).trans (Equiv.swap (0 : Fin 4) 1))))

private theorem rhsPair_eq
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (s : ℝ) :
    rhsRefoldPair (I := I) (M := M) g gm G s =
      appCcRS (I := I) (M := M) g 2 6 2
        (mvPairTraceOp (I := I) (M := M) g gm)
        (rhsPairArg (I := I) (M := M) g G s) := by
  simp only [rhsRefoldPair, rhsPairArg, edgeKernelPair, edgeKernelArg,
    edgeLieArg, Fin.sum_univ_three, appCcRS_smul_right, appCcRS_add_right,
    appCcRS_sub_right, edgePairMono, edgeArg]

private theorem rhsPairArg_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 6 j
        (rhsPairArg (I := I) (M := M) g G s)‖ ≤
      21 * ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
  let N : ℝ := ‖iteratedCovGrad (I := I) g 0 4 j G‖
  let K₀ : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeKernelArg (I := I) (M := M) g G ricciRefoldQA)
  let K₁ : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeKernelArg (I := I) (M := M) g G ricciRefoldQB)
  let L₀ : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeLieArg (I := I) (M := M) g G (lieRefoldQ 0))
  let L₁ : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeLieArg (I := I) (M := M) g G (lieRefoldQ 1))
  let L₂ : SmoothCcTensor g 2 (6 + j) :=
    iteratedCovGrad (I := I) g 2 6 j
      (edgeLieArg (I := I) (M := M) g G (lieRefoldQ 2))
  have hiter :
      iteratedCovGrad (I := I) g 2 6 j
          (rhsPairArg (I := I) (M := M) g G s) =
        (2 : ℝ) • (s • ((1 / 2 : ℝ) • (K₀ + K₁))) +
          s • (lieRefoldEps 0 • L₀ +
            lieRefoldEps 1 • L₁ + lieRefoldEps 2 • L₂) := by
    simp only [rhsPairArg, Fin.sum_univ_three, iteratedCovGrad_add,
      iteratedCovGrad_smul, K₀, K₁, L₀, L₁, L₂]
  have hN : 0 ≤ N := norm_nonneg _
  have hsNorm : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hK₀ : ‖K₀‖ ≤ 6 * N := by
    have h := edgeKernel_norm (I := I) (M := M) g G ricciRefoldQA j
    rw [hDim] at h
    norm_num at h
    simpa only [K₀, N] using h
  have hK₁ : ‖K₁‖ ≤ 6 * N := by
    have h := edgeKernel_norm (I := I) (M := M) g G ricciRefoldQB j
    rw [hDim] at h
    norm_num at h
    simpa only [K₁, N] using h
  have hL₀ : ‖L₀‖ ≤ 3 * N := by
    have h := edgeLieArg_norm (I := I) (M := M) g G (lieRefoldQ 0) j
    rw [hDim] at h
    norm_num at h
    simpa only [L₀, N] using h
  have hL₁ : ‖L₁‖ ≤ 3 * N := by
    have h := edgeLieArg_norm (I := I) (M := M) g G (lieRefoldQ 1) j
    rw [hDim] at h
    norm_num at h
    simpa only [L₁, N] using h
  have hL₂ : ‖L₂‖ ≤ 3 * N := by
    have h := edgeLieArg_norm (I := I) (M := M) g G (lieRefoldQ 2) j
    rw [hDim] at h
    norm_num at h
    simpa only [L₂, N] using h
  have hKsum : ‖K₀ + K₁‖ ≤ 12 * N := by
    calc
      _ ≤ ‖K₀‖ + ‖K₁‖ := norm_add_le _ _
      _ ≤ 6 * N + 6 * N := add_le_add hK₀ hK₁
      _ = 12 * N := by ring
  have he₀ : ‖lieRefoldEps 0‖ = 1 := by norm_num [lieRefoldEps]
  have he₁ : ‖lieRefoldEps 1‖ = 1 := by norm_num [lieRefoldEps]
  have he₂ : ‖lieRefoldEps 2‖ = 1 := by
    change ‖(1 : ℝ)‖ = 1
    norm_num
  have hL₀' : ‖lieRefoldEps 0 • L₀‖ ≤ 3 * N := by
    rw [norm_smul, he₀, one_mul]
    exact hL₀
  have hL₁' : ‖lieRefoldEps 1 • L₁‖ ≤ 3 * N := by
    rw [norm_smul, he₁, one_mul]
    exact hL₁
  have hL₂' : ‖lieRefoldEps 2 • L₂‖ ≤ 3 * N := by
    rw [norm_smul, he₂, one_mul]
    exact hL₂
  have hLsum :
      ‖lieRefoldEps 0 • L₀ + lieRefoldEps 1 • L₁ +
          lieRefoldEps 2 • L₂‖ ≤ 9 * N := by
    calc
      _ ≤ ‖lieRefoldEps 0 • L₀ + lieRefoldEps 1 • L₁‖ +
          ‖lieRefoldEps 2 • L₂‖ := norm_add_le _ _
      _ ≤ (‖lieRefoldEps 0 • L₀‖ + ‖lieRefoldEps 1 • L₁‖) +
          ‖lieRefoldEps 2 • L₂‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ (3 * N + 3 * N) + 3 * N :=
        add_le_add (add_le_add hL₀' hL₁') hL₂'
      _ = 9 * N := by ring
  have hRic :
      ‖(2 : ℝ) • (s • ((1 / 2 : ℝ) • (K₀ + K₁)))‖ ≤ 12 * N := by
    rw [norm_smul, norm_smul, norm_smul,
      show ‖(2 : ℝ)‖ = 2 by norm_num,
      show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    calc
      2 * (‖s‖ * (1 / 2 * ‖K₀ + K₁‖)) ≤
          2 * (1 * (1 / 2 * (12 * N))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hsNorm
          (mul_le_mul_of_nonneg_left hKsum (by norm_num))
          (mul_nonneg (by norm_num) (norm_nonneg _)) zero_le_one
      _ = 12 * N := by ring
  have hLie :
      ‖s • (lieRefoldEps 0 • L₀ + lieRefoldEps 1 • L₁ +
        lieRefoldEps 2 • L₂)‖ ≤ 9 * N := by
    rw [norm_smul]
    calc
      ‖s‖ * ‖lieRefoldEps 0 • L₀ + lieRefoldEps 1 • L₁ +
          lieRefoldEps 2 • L₂‖ ≤ 1 * (9 * N) :=
        mul_le_mul hsNorm hLsum (norm_nonneg _) zero_le_one
      _ = 9 * N := one_mul _
  rw [hiter]
  calc
    _ ≤ ‖(2 : ℝ) • (s • ((1 / 2 : ℝ) • (K₀ + K₁)))‖ +
        ‖s • (lieRefoldEps 0 • L₀ + lieRefoldEps 1 • L₁ +
          lieRefoldEps 2 • L₂)‖ := norm_add_le _ _
    _ ≤ 12 * N + 9 * N := add_le_add hRic hLie
    _ = 21 * ‖iteratedCovGrad (I := I) g 0 4 j G‖ := by
      dsimp only [N]
      ring

private theorem rhsPairArg_jets
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (B : ℝ)
    (hG : ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 ≤ B ^ 2) :
    ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g 2 6 j
          (rhsPairArg (I := I) (M := M) g G s)‖ ^ 2 ≤
      (21 * B) ^ 2 := by
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 2 6 j
          (rhsPairArg (I := I) (M := M) g G s)‖ ^ 2 ≤
        21 ^ 2 * ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 := by
    intro j _hj
    have hj := rhsPairArg_norm (I := I) (M := M) hDim g G hs j
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _))).2 hj
    calc
      _ ≤ (21 * ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 := hsq
      _ = 21 ^ 2 * ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 := by ring
  calc
    ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g 2 6 j
          (rhsPairArg (I := I) (M := M) g G s)‖ ^ 2 ≤
        ∑ j ∈ Finset.range n,
          21 ^ 2 * ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 :=
      Finset.sum_le_sum hterm
    _ = 21 ^ 2 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 21 ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hG (sq_nonneg 21)
    _ = (21 * B) ^ 2 := by ring

/-- The complete refold pair has an `H2` jet bound from a moving-pair `H2`
bound and an `H2` passenger bound, uniformly along the metric segment. -/
theorem rhsPair_h2_jets
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
        {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 2 j
            (mvPairTraceOp (I := I) (M := M) g gm)‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (rhsRefoldPair (I := I) (M := M) g gm G s)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨Capp, hCapp, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 2 6 2
  refine ⟨21 * Capp, mul_nonneg (by norm_num) hCapp, ?_⟩
  intro gm G s hs A B hA hB hmv hG
  have harg := rhsPairArg_jets
    (I := I) (M := M) hDim g G hs 3 B hG
  rw [rhsPair_eq (I := I) (M := M) g gm G s]
  have hout := happ
    (mvPairTraceOp (I := I) (M := M) g gm)
    (rhsPairArg (I := I) (M := M) g G s)
    A (21 * B) hA (mul_nonneg (by norm_num) hB) hmv harg
  simpa only [mul_assoc, mul_left_comm] using hout

/-- The complete refold pair has an `H1` jet bound from a moving-pair `H2`
bound and an `H1` passenger bound, uniformly along the metric segment. -/
theorem rhsPair_h1_jets
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
        {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 2 j
            (mvPairTraceOp (I := I) (M := M) g gm)‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (rhsRefoldPair (I := I) (M := M) g gm G s)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨Capp, hCapp, happ⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g 2 6 2
  refine ⟨21 * Capp, mul_nonneg (by norm_num) hCapp, ?_⟩
  intro gm G s hs A B hA hB hmv hG
  have harg := rhsPairArg_jets
    (I := I) (M := M) hDim g G hs 2 B hG
  have hout := happ
    (mvPairTraceOp (I := I) (M := M) g gm)
    (rhsPairArg (I := I) (M := M) g G s)
    A (21 * B) hA (mul_nonneg (by norm_num) hB) hmv harg
  rw [← rhsPair_eq (I := I) (M := M) g gm G s] at hout
  let Y : SmoothCcTensor g 2 2 :=
    rhsRefoldPair (I := I) (M := M) g gm G s
  have hjet_eq :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j Y‖ ^ 2 =
        ‖(⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using
      (h1_jet_sq (I := I) (M := M) g 2 2 Y).symm
  have hright :
      0 ≤ Capp * A * (21 * B) :=
    mul_nonneg (mul_nonneg hCapp hA) (mul_nonneg (by norm_num) hB)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hright).2 hout
  change ∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 j Y‖ ^ 2 ≤
    ((21 * Capp) * A * B) ^ 2
  calc
    _ = ‖(⟨Y⟩ : SmoothCcTensorH1 g 2 2)‖ ^ 2 := hjet_eq
    _ ≤ (Capp * A * (21 * B)) ^ 2 := hsq
    _ = ((21 * Capp) * A * B) ^ 2 := by ring

set_option maxHeartbeats 3200000 in
private theorem rhsPair_apply_core
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (G : SmoothCcTensor g 0 4) :
    appCc (I := I) (M := M) g 2 2
        (rhsRefoldPair (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) G s) T =
      appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G := by
  rw [rhsRefoldPair, rhsRefold2, ricciRefold2, lieRefold2,
    riemannPalatiniRefoldC2Family, deTurckLieCovDerivRefoldC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [appCc_add_left, appCc_smul_left]
  rw [edgeKernel_apply (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G ricciRefoldQA,
    edgeKernel_apply (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G ricciRefoldQB,
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G (lieRefoldQ 0),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G
        ((lieRefoldQ 0).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G (lieRefoldQ 1),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G
        ((lieRefoldQ 1).trans (Equiv.swap (0 : Fin 4) 1)),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G (lieRefoldQ 2),
    edgeMonoRefold (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T G
        ((lieRefoldQ 2).trans (Equiv.swap (0 : Fin 4) 1))]

/-- On a three-dimensional small spectral `H2` metric ball, the complete
second-order refold correction has an action-level `H2` jet bound linear in
the state radius.  The passenger requires only two `L2` jets. -/
theorem rhsRefold2_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ}
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        s ∈ realizedSmallSet (δ := δ) (δ' := δ) →
        ∀ (G : SmoothCcTensor g 0 4) (B : ℝ), 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G)‖ ^ 2) ≤
          (C * R * B) ^ 2 := by
  obtain ⟨ρ, Cmv, hρ, hCmv, hmv⟩ :=
    mvPair_h2_ball (I := I) (M := M) hDim g
  obtain ⟨Cpair, hCpair, hpair⟩ :=
    rhsPair_h2_jets (I := I) (M := M) hDim g
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h2_h2_h2 (I := I) (M := M) hDim g 2 2
  obtain ⟨Cstate, hCstate, hstate⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let C : ℝ := Capp * Cpair * Cmv * Cstate
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ hδZ R hR hRρ hT s hs hs_mem G B hB hG
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδ hδZ s
  have hsNorm : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ R := by
    rw [show P = s • T by
      dsimp only [P]
      rw [convexPerturbation, smul_zero, zero_add],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul hsNorm hT (norm_nonneg _) zero_le_one).trans_eq
      (one_mul R)
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [gm, P] using
      realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ hs_mem y v w
  have hmv' :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 2 j
            (mvPairTraceOp (I := I) (M := M) g gm)‖ ^ 2 ≤ Cmv ^ 2 :=
    hmv P gm (hP.trans hRρ) htie
  have hpair' :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (rhsRefoldPair (I := I) (M := M) g gm G s)‖ ^ 2 ≤
        (Cpair * Cmv * B) ^ 2 :=
    hpair gm G hs Cmv B hCmv hB hmv' hG
  have hTjet :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
        (Cstate * R) ^ 2 := by
    exact (hstate T).trans
      (pow_le_pow_left₀
        (mul_nonneg hCstate (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hT hCstate) 2)
  have hcoeff : 0 ≤ Cpair * Cmv * B :=
    mul_nonneg (mul_nonneg hCpair hCmv) hB
  have hstateR : 0 ≤ Cstate * R := mul_nonneg hCstate hR
  have hout := happ
    (rhsRefoldPair (I := I) (M := M) g gm G s) T
    (Cpair * Cmv * B) (Cstate * R)
    hcoeff hstateR hpair' hTjet
  rw [rhsPair_apply_core (g := g) (T := T) hδ hδZ s G] at hout
  simpa only [C] using (show
    (Capp * (Cpair * Cmv * B) * (Cstate * R)) ^ 2 =
      (C * R * B) ^ 2 by
        dsimp only [C]
        ring) ▸ hout

/-- On a three-dimensional small spectral `H2` metric ball, the complete
second-order refold correction acts from a passenger with one `L2` jet and the
metric state in spectral `H2` to spectral `H1`, linearly in the state radius. -/
theorem rhsRefold2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ}
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        s ∈ realizedSmallSet (δ := δ) (δ' := δ) →
        ∀ (G : SmoothCcTensor g 0 4) (B : ℝ), 0 ≤ B →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G)‖ ≤
          C * R * B := by
  obtain ⟨ρ, Cmv, hρ, hCmv, hmv⟩ :=
    mvPair_h2_ball (I := I) (M := M) hDim g
  obtain ⟨Cpair, hCpair, hpair⟩ :=
    rhsPair_h1_jets (I := I) (M := M) hDim g
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h1_h2_h1 (I := I) (M := M) hDim g 2 2
  let C : ℝ := Capp * Cpair * Cmv
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ hδZ R hR hRρ hT s hs hs_mem G B hB hG
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδ hδZ s
  have hsNorm : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ R := by
    rw [show P = s • T by
      dsimp only [P]
      rw [convexPerturbation, smul_zero, zero_add],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul hsNorm hT (norm_nonneg _) zero_le_one).trans_eq
      (one_mul R)
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [gm, P] using
      realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ hs_mem y v w
  have hmv' :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 2 j
            (mvPairTraceOp (I := I) (M := M) g gm)‖ ^ 2 ≤ Cmv ^ 2 :=
    hmv P gm (hP.trans hRρ) htie
  have hpair' :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (rhsRefoldPair (I := I) (M := M) g gm G s)‖ ^ 2 ≤
        (Cpair * Cmv * B) ^ 2 :=
    hpair gm G hs Cmv B hCmv hB hmv' hG
  have hcoeff : 0 ≤ Cpair * Cmv * B :=
    mul_nonneg (mul_nonneg hCpair hCmv) hB
  have hout := happ
    (rhsRefoldPair (I := I) (M := M) g gm G s) T
    (Cpair * Cmv * B) hcoeff hpair'
  rw [rhsPair_apply_core (g := g) (T := T) hδ hδZ s G] at hout
  calc
    _ ≤ Capp * (Cpair * Cmv * B) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := hout
    _ ≤ Capp * (Cpair * Cmv * B) * R :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg hCapp hcoeff)
    _ = C * R * B := by
      dsimp only [C]
      ring

/-- On a three-dimensional small spectral `H2` metric ball, the complete
second-order refold correction is an `H4` to `H2` action whose norm is linear
in the state radius. -/
theorem rhsRefold2_h4_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ}
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        s ∈ realizedSmallSet (δ := δ) (δ' := δ) →
        ∀ U : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2 (I := I) (M := M) g T hδ hδZ s)
              (iteratedCovGrad (I := I) g 0 2 2 U))‖ ≤
          C * R *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
  classical
  obtain ⟨ρ, Cact, hρ, hCact, hact⟩ :=
    rhsRefold2_h2 (I := I) (M := M) hDim g
  obtain ⟨Cin, hCin, hin⟩ :=
    hsJet_le (I := I) (M := M) g 2 4
  obtain ⟨Csp, hCsp, hsp⟩ :=
    hs_le_jet (I := I) (M := M) g 2 2
  let C : ℝ := Csp * 3 * Cact * Cin
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ hδZ R hR hRρ hT s hs hs_mem U
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖
  let B : ℝ := Cin * N
  let G : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 U
  let Y : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2
      (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G
  let Q : ℝ := Cact * R * B
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCact hR) hB
  have hJ :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ B := by
    simpa only [B, N, Nat.reduceAdd] using hin U
  have hGsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ =
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (2 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [G, Nat.reduceAdd] using
                icg_comp_norm (I := I) (M := M) g 2 2 j U
      _ ≤ ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 0 U),
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 U)]
      _ ≤ B := hJ
  have hGsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 4 j G))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 4 j G)))
        hGsum 2
  have hYsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ Q ^ 2 := by
    simpa only [Y, G, Q] using
      hact T hδ hδZ hR hRρ hT hs hs_mem G B hB hGsq
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hYsq,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hYsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 3 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * Q := by norm_num
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        Csp * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
    simpa only [Nat.reduceAdd] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
    C * R * N
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := hspY
    _ ≤ Csp * (3 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = C * R * N := by
      dsimp only [C, Q, B]
      ring

/-- On a three-dimensional small spectral `H2` metric ball, the complete
second-order refold correction is an `H3` to `H1` action whose norm is linear
in the state radius. -/
theorem rhsRefold2_h3_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ}
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        s ∈ realizedSmallSet (δ := δ) (δ' := δ) →
        ∀ U : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2 (I := I) (M := M) g T hδ hδZ s)
              (iteratedCovGrad (I := I) g 0 2 2 U))‖ ≤
          C * R *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  classical
  obtain ⟨ρ, Cact, hρ, hCact, hact⟩ :=
    rhsRefold2_h1 (I := I) (M := M) hDim g
  obtain ⟨Cin, hCin, hin⟩ :=
    hsJet_le (I := I) (M := M) g 2 3
  let C : ℝ := Cact * Cin
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ hδZ R hR hRρ hT s hs hs_mem U
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖
  let B : ℝ := Cin * N
  let G : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 U
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hJ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ B := by
    simpa only [B, N, Nat.reduceAdd] using hin U
  have hGsum :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ =
          ∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 0 2 (2 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [G, Nat.reduceAdd] using
                icg_comp_norm (I := I) (M := M) g 2 2 j U
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 0 U),
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 U)]
      _ ≤ B := hJ
  have hGsq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 4 j G))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 4 j G)))
        hGsum 2
  have hout :=
    hact T hδ hδZ hR hRρ hT hs hs_mem G B hB hGsq
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
      (appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G)‖ ≤
    C * R * N
  calc
    _ ≤ Cact * R * B := hout
    _ = C * R * N := by
      dsimp only [C, B]
      ring

set_option maxHeartbeats 3200000 in
/-- Applying the generalized refold pair to the metric deviation is exactly
the complete second-order Ricci--DeTurck coefficient acting on its passenger. -/
theorem rhsPair_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : Real}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : Real) (G : SmoothCcTensor g 0 4) :
    appCc (I := I) (M := M) g 2 2
        (rhsRefoldPair (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) G s) T =
      appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hδ hδZ s) G := by
  exact rhsPair_apply_core (g := g) (T := T) hδ hδZ s G

/-- The refold correction to the second-order coefficient is jointly smooth
along the realized metric segment. -/
theorem rhsRefold2_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (rhsRefold2 (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hRic0 :=
    riemannPalatiniRefoldC2Family_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ ricciRefoldQA ricciRefoldQB
  have hRic := threeArmJoint_smul (I := I) (M := M) g (2 : ℝ) _ hRic0
  have hLie := lieRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hAll := threeArmJoint_add (I := I) (M := M) g _ _ hRic hLie
  simpa only [rhsRefold2, ricciRefold2] using hAll

private theorem appCc_path_joint
    (g : SmoothRiemannianMetric I M) (r c : ℕ)
    (Φ : ℝ → SmoothCcTensor g r c) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun x : M => TensorRSSpace r c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (W : SmoothCcTensor g 0 r) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 c ℝ E)
        (E := fun x : M => TensorRSSpace 0 c I x) p.1
        ((appCc (I := I) (M := M) g r c (Φ p.2) W).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × ℝ =>
      (appCc (I := I) (M := M) g r c (Φ p.2) W).toSection p.1)
    (S := S)
  intro Y
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 r ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 r ℝ E)
        (E := fun x : M => TensorRSSpace 0 r I x) p.1
        (W.toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    W.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hWY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hW hY
  have hout := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hjoint hWY
  refine hout.congr (fun p _ => ?_)
  refine congrArg
    (fun v : Tensor0SSpace c I p.1 =>
      TotalSpace.mk' (Tensor0SModel c ℝ E)
        (E := fun x : M => Tensor0SSpace c I x) p.1 v) ?_
  rw [appCc_toSection, ContinuousLinearMap.comp_apply]

private theorem appCc_path_eq
    (g : SmoothRiemannianMetric I M) (r c : ℕ)
    (Φ : ℝ → SmoothCcTensor g r c) (W : SmoothCcTensor g 0 r)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun x : M => TensorRSSpace r c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    appCc (I := I) (M := M) g r c
        (pathIntegralCoeffField (I := I) (M := M) g r c
          Φ S hS hSI hjoint) W =
      pathIntegralCoeffField (I := I) (M := M) g 0 c
        (fun t => appCc (I := I) (M := M) g r c (Φ t) W)
        S hS hSI (appCc_path_joint (I := I) (M := M)
          g r c Φ S hjoint W) := by
  let Ψ : ℝ → SmoothCcTensor g 0 c :=
    fun t => appCc (I := I) (M := M) g r c (Φ t) W
  have hΨjoint := appCc_path_joint (I := I) (M := M)
    g r c Φ S hjoint W
  have hcont : ∀ x : M, ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g r c Φ S hjoint x
  have hΨcont : ∀ x : M, ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 0 c Ψ S hΨjoint x
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  let u : Tensor0SModel 0 ℝ E :=
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
  have hΨInt : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Ψ t).toSection x))
      MeasureTheory.volume 0 1 :=
    ((hΨcont x).mono hSI).intervalIntegrable
  have hΨappInt : IntervalIntegrable
      (fun t : ℝ =>
        (TensorRSSpace.toModel ((Ψ t).toSection x)) u)
      MeasureTheory.volume 0 1 := by
    exact ((ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E) u).continuous.comp_continuousOn
      ((hΨcont x).mono hSI)).intervalIntegrable
  have hkey : ∀ t : ℝ,
      unitModel (I := I) (M := M) g c (Ψ t) x v =
        ((TensorRSSpace.toModel ((Ψ t).toSection x)) u) v := by
    intro t
    rw [unitModel, toModel_tensorRS_apply]
  calc
    unitModel (I := I) (M := M) g c
        (appCc (I := I) (M := M) g r c
          (pathIntegralCoeffField (I := I) (M := M) g r c
            Φ S hS hSI hjoint) W) x v =
        ∫ t in (0 : ℝ)..1,
          unitModel (I := I) (M := M) g c (Ψ t) x v := by
      simpa only [Ψ] using
        pathIntegralCoeffField_appCc_eq (I := I) (M := M)
          g r c Φ W S hS hSI hjoint hcont x v
    _ = ∫ t in (0 : ℝ)..1,
        ((TensorRSSpace.toModel ((Ψ t).toSection x)) u) v :=
      intervalIntegral.integral_congr (fun t _ => hkey t)
    _ = unitModel (I := I) (M := M) g c
        (pathIntegralCoeffField (I := I) (M := M) g 0 c
          Ψ S hS hSI hΨjoint) x v := by
      symm
      rw [show unitModel (I := I) (M := M) g c
          (pathIntegralCoeffField (I := I) (M := M) g 0 c
            Ψ S hS hSI hΨjoint) x v =
        ((TensorRSSpace.toModel
          ((pathIntegralCoeffField (I := I) (M := M) g 0 c
            Ψ S hS hSI hΨjoint).toSection x)) u) v by
          rw [unitModel, toModel_tensorRS_apply]]
      rw [pathIntegralCoeffField_toModel]
      rw [ContinuousLinearMap.intervalIntegral_apply hΨInt u]
      exact (ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ v)
        hΨappInt).symm

/-- The path integral of the second-order coefficient created by the exact
Ricci--DeTurck refold. -/
def rhsRefold2Int
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (rhsRefold2 (I := I) (M := M) g T hδ hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ)) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (rhsRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ)

/-- The interval-integrated second-order refold correction inherits the
pointwise `H2` jet action bound, with the same linear dependence on the small
spectral `H2` state radius. -/
theorem rhsRefold2Int_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ (G : SmoothCcTensor g 0 4) (B : ℝ), 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2Int (I := I) (M := M)
                g T hδ_lt hδ hδZ) G)‖ ^ 2) ≤
          (C * R * B) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hact⟩ :=
    rhsRefold2_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT G B hB hG
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 4 2 :=
    rhsRefold2 (I := I) (M := M) g T hδ hδZ
  let Ψ : ℝ → SmoothCcTensor g 0 2 :=
    fun s => appCc (I := I) (M := M) g 4 2 (Φ s) G
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hΦjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
        (E := fun x : M => TensorRSSpace 4 2 I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
    simpa only [Φ, S] using
      rhsRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hΨjoint := appCc_path_joint (I := I) (M := M)
    g 4 2 Φ S hΦjoint G
  have hQ : 0 ≤ C * R * B :=
    mul_nonneg (mul_nonneg hC hR) hB
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j (Ψ s)‖ ^ 2) ≤
        (C * R * B) ^ 2 := by
    intro s hs
    have hs_mem : s ∈ S := hSI (by
      simpa only [Set.uIcc_of_le zero_le_one] using hs)
    simpa only [Ψ, Φ] using
      hact T hδ hδZ hR hRρ hT hs hs_mem G B hB hG
  have hpath := path_jetL2_le (I := I) (M := M)
    g 0 2 2 Ψ S realizedSmallSet_isOpen hSI hΨjoint hQ hpoint
  have heq :
      appCc (I := I) (M := M) g 4 2
          (rhsRefold2Int (I := I) (M := M)
            g T hδ_lt hδ hδZ) G =
        pathIntegralCoeffField (I := I) (M := M) g 0 2
          Ψ S realizedSmallSet_isOpen hSI hΨjoint := by
    simpa only [rhsRefold2Int, Φ, Ψ, S] using
      appCc_path_eq (I := I) (M := M)
        g 4 2 Φ G S realizedSmallSet_isOpen hSI hΦjoint
  rw [← heq] at hpath
  simpa only [Nat.reduceAdd] using hpath

/-- The interval-integrated second-order refold correction maps a passenger
with one `L2` jet and the spectral `H2` state to spectral `H1`, linearly in the
small state radius. -/
theorem rhsRefold2Int_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ (G : SmoothCcTensor g 0 4) (B : ℝ), 0 ≤ B →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2Int (I := I) (M := M)
                g T hδ_lt hδ hδZ) G)‖ ≤
          C * R * B := by
  obtain ⟨ρ, Cact, hρ, hCact, hact⟩ :=
    rhsRefold2_h1 (I := I) (M := M) hDim g
  obtain ⟨Cin, hCin, hin⟩ :=
    hsJet_le (I := I) (M := M) g 2 1
  obtain ⟨Csp, hCsp, hsp⟩ :=
    hs_le_jet (I := I) (M := M) g 2 1
  let C : ℝ := Csp * 2 * Cin * Cact
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT G B hB hG
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 4 2 :=
    rhsRefold2 (I := I) (M := M) g T hδ hδZ
  let Ψ : ℝ → SmoothCcTensor g 0 2 :=
    fun s => appCc (I := I) (M := M) g 4 2 (Φ s) G
  let Q : ℝ := Cin * (Cact * R * B)
  have hQ : 0 ≤ Q :=
    mul_nonneg hCin (mul_nonneg (mul_nonneg hCact hR) hB)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hΦjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
        (E := fun x : M => TensorRSSpace 4 2 I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
    simpa only [Φ, S] using
      rhsRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hΨjoint := appCc_path_joint (I := I) (M := M)
    g 4 2 Φ S hΦjoint G
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 2 j (Ψ s)‖ ^ 2) ≤ Q ^ 2 := by
    intro s hs
    have hs_mem : s ∈ S := hSI (by
      simpa only [Set.uIcc_of_le zero_le_one] using hs)
    have hout :
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) (Ψ s)‖ ≤
          Cact * R * B := by
      simpa only [Ψ, Φ] using
        hact T hδ hδZ hR hRρ hT hs hs_mem G B hB hG
    have hsum :
        ∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 0 2 j (Ψ s)‖ ≤ Q := by
      calc
        _ ≤ Cin *
            ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) (Ψ s)‖ :=
          by
            rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
            simpa only [Nat.reduceAdd] using hin (Ψ s)
        _ ≤ Cin * (Cact * R * B) :=
          mul_le_mul_of_nonneg_left hout hCin
        _ = Q := rfl
    calc
      _ ≤ (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 2 j (Ψ s)‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 2 j (Ψ s)))
      _ ≤ Q ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j (Ψ s))))
        hsum 2
  have hpath := path_jetL2_le (I := I) (M := M)
    g 0 2 1 Ψ S realizedSmallSet_isOpen hSI hΨjoint hQ hpoint
  have heq :
      appCc (I := I) (M := M) g 4 2
          (rhsRefold2Int (I := I) (M := M)
            g T hδ_lt hδ hδZ) G =
        pathIntegralCoeffField (I := I) (M := M) g 0 2
          Ψ S realizedSmallSet_isOpen hSI hΨjoint := by
    simpa only [rhsRefold2Int, Φ, Ψ, S] using
      appCc_path_eq (I := I) (M := M)
        g 4 2 Φ G S realizedSmallSet_isOpen hSI hΦjoint
  rw [← heq] at hpath
  let Y : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2
      (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ) G
  have hYsq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ Q ^ 2 := by
    simpa only [Nat.reduceAdd, Y] using hpath
  have hterm : ∀ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hYsq,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hYsum :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 2 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 2, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 2 * Q := by norm_num
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
        Csp * ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Nat.reduceAdd] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Y‖ ≤
    C * R * B
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := hspY
    _ ≤ Csp * (2 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = C * R * B := by
      dsimp only [C, Q]
      ring

/-- On a three-dimensional small spectral `H2` metric ball, the integrated
second-order refold correction acts from spectral `H4` to spectral `H2`, with
operator bound linear in the state radius. -/
theorem rhsRefold2Int_h4_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2Int (I := I) (M := M)
                g T hδ_lt hδ hδZ)
              (iteratedCovGrad (I := I) g 0 2 2 U))‖ ≤
          C * R *
            ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
  classical
  obtain ⟨ρ, Cact, hρ, hCact, hact⟩ :=
    rhsRefold2Int_h2 (I := I) (M := M) hDim g
  obtain ⟨Cin, hCin, hin⟩ :=
    hsJet_le (I := I) (M := M) g 2 4
  obtain ⟨Csp, hCsp, hsp⟩ :=
    hs_le_jet (I := I) (M := M) g 2 2
  let C : ℝ := Csp * 3 * Cact * Cin
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖
  let B : ℝ := Cin * N
  let G : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 U
  let Y : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2
      (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ) G
  let Q : ℝ := Cact * R * B
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCact hR) hB
  have hJ :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ B := by
    simpa only [B, N, Nat.reduceAdd] using hin U
  have hGsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ =
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (2 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [G, Nat.reduceAdd] using
                icg_comp_norm (I := I) (M := M) g 2 2 j U
      _ ≤ ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 0 U),
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 U)]
      _ ≤ B := hJ
  have hGsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 4 j G))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 4 j G)))
        hGsum 2
  have hYsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ Q ^ 2 := by
    simpa only [Y, G, Q] using
      hact T hδ_lt hδ hδZ hR hRρ hT G B hB hGsq
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hYsq,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hYsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 3 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * Q := by norm_num
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        Csp * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
    simpa only [Nat.reduceAdd] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
    C * R * N
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := hspY
    _ ≤ Csp * (3 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = C * R * N := by
      dsimp only [C, Q, B]
      ring

/-- On a three-dimensional small spectral `H2` metric ball, the integrated
second-order refold correction acts from spectral `H3` to spectral `H1`, with
operator bound linear in the state radius. -/
theorem rhsRefold2Int_h3_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (appCc (I := I) (M := M) g 4 2
              (rhsRefold2Int (I := I) (M := M)
                g T hδ_lt hδ hδZ)
              (iteratedCovGrad (I := I) g 0 2 2 U))‖ ≤
          C * R *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  classical
  obtain ⟨ρ, Cact, hρ, hCact, hact⟩ :=
    rhsRefold2Int_h1 (I := I) (M := M) hDim g
  obtain ⟨Cin, hCin, hin⟩ :=
    hsJet_le (I := I) (M := M) g 2 3
  let C : ℝ := Cact * Cin
  refine ⟨ρ, C, hρ, by dsimp only [C]; positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖
  let B : ℝ := Cin * N
  let G : SmoothCcTensor g 0 4 :=
    iteratedCovGrad (I := I) g 0 2 2 U
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hJ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ B := by
    simpa only [B, N, Nat.reduceAdd] using hin U
  have hGsum :
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖ =
          ∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 0 2 (2 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [G, Nat.reduceAdd] using
                icg_comp_norm (I := I) (M := M) g 2 2 j U
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 0 U),
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 1 U)]
      _ ≤ B := hJ
  have hGsq :
      (∑ j ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 4 j G‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 0 4 j G‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 4 j G))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 4 j G)))
        hGsum 2
  have hout :=
    hact T hδ_lt hδ hδZ hR hRρ hT G B hB hGsq
  change ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
      (appCc (I := I) (M := M) g 4 2
        (rhsRefold2Int (I := I) (M := M)
          g T hδ_lt hδ hδZ) G)‖ ≤
    C * R * N
  calc
    _ ≤ Cact * R * B := hout
    _ = C * R * N := by
      dsimp only [C, B]
      ring

/-- The complete refolded top path coefficient is the sum of the newly
refolded correction and the original Ricci--DeTurck top path coefficient. -/
theorem refoldTopInt_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    rhsRefoldTopInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ =
      rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ +
        rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
          hδ_lt hδ hδ_lt hδZ := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hRefold :=
    rhsRefold2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hTop :=
    rhsTop_path_joint (I := I) (M := M) g g_bg T 0 hδ hδZ
  have hcRefold : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel
        ((rhsRefold2 (I := I) (M := M) g T hδ hδZ s).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 4 2
      (rhsRefold2 (I := I) (M := M) g T hδ hδZ)
      (realizedSmallSet (δ := δ) (δ' := δ)) hRefold x
  have hcTop : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel
        ((deTurckPhiMetTotal (I := I) (M := M) g g_bg
          (realizedFam (I := I) g T 0 hδ hδZ s)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 4 2
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g g_bg
        (realizedFam (I := I) g T 0 hδ hδZ s))
      (realizedSmallSet (δ := δ) (δ' := δ)) hTop x
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  change TensorRSSpace.toModel
      ((rhsRefoldTopInt (I := I) (M := M) g g_bg T
        hδ_lt hδ hδZ).toSection x) =
    TensorRSSpace.toModel
      ((rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ +
        rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
          hδ_lt hδ hδ_lt hδZ).toSection x)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    TensorRSSpace.toModel_add]
  rw [rhsRefoldTopInt, rhsRefold2Int, rhsTopPathIntegral]
  rw [pathIntegralCoeffField_toModel, pathIntegralCoeffField_toModel,
    pathIntegralCoeffField_toModel]
  have hIRefold : IntervalIntegrable (fun s : ℝ =>
      TensorRSSpace.toModel
        ((rhsRefold2 (I := I) (M := M) g T hδ hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    ((hcRefold x).mono hSI).intervalIntegrable
  have hITop : IntervalIntegrable (fun s : ℝ =>
      TensorRSSpace.toModel
        ((deTurckPhiMetTotal (I := I) (M := M) g g_bg
          (realizedFam (I := I) g T 0 hδ hδZ s)).toSection x))
      MeasureTheory.volume 0 1 :=
    ((hcTop x).mono hSI).intervalIntegrable
  rw [← intervalIntegral.integral_add hIRefold hITop]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [rhsRefoldTop, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]

/-- After subtracting the fixed connection Laplacian, the complete top action
is the refold correction, the small principal-coefficient deviation, and the
fixed curvature zeroth-order action. -/
theorem refold_top_split
    (g g_bg : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    appCc (I := I) (M := M) g 4 2
        (rhsRefoldTopInt (I := I) (M := M) g g_bg T
          hδ_lt hδ hδZ)
        (iteratedCovGrad (I := I) g 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g 0 2 U =
    appCc (I := I) (M := M) g 4 2
        (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
        (iteratedCovGrad (I := I) g 0 2 2 U) +
      appCc (I := I) (M := M) g 4 2
        (rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
            hδ_lt hδ hδ_lt hδZ -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
        (iteratedCovGrad (I := I) g 0 2 2 U) +
      appCc (I := I) (M := M) g 2 2
        (phiMetCurvCoeff (I := I) g g_bg g)
        (iteratedCovGrad (I := I) g 0 2 0 U) := by
  rw [refoldTopInt_eq (I := I) (M := M) g g_bg T hδ_lt hδ hδZ,
    appCc_add_left]
  rw [show
      (appCc (I := I) (M := M) g 4 2
          (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 U) +
        appCc (I := I) (M := M) g 4 2
          (rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 U)) -
        rawTensorConnLapSmooth (I := I) g 0 2 U =
      appCc (I := I) (M := M) g 4 2
          (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 U) +
        (appCc (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 U) -
          rawTensorConnLapSmooth (I := I) g 0 2 U) by abel]
  rw [top_path_split (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ U]
  abel

/-- The additional smooth second-order action after removing the already
completed principal-cometric operator.  The DeTurck background is the fixed
base metric, as required by the low-regularity short-time endpoint. -/
def extraA2Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 4 2
      (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
      (iteratedCovGrad (I := I) g 0 2 2 U) +
    appCc (I := I) (M := M) g 4 2
      (rhsTopPathIntegral (I := I) (M := M) g g T 0
          hδ_lt hδ hδ_lt hδZ -
        deTurckPhiMetTotal (I := I) (M := M) g g g)
      (iteratedCovGrad (I := I) g 0 2 2 U) -
    deTurckPrincipalCometricArm (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ 1) U

/-- The additional second-order action is additive in its passenger. -/
theorem extraA2_add
    (g : SmoothRiemannianMetric I M)
    (T U V : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    extraA2Act (I := I) (M := M) g T (U + V) hδ_lt hδ hδZ =
      extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
        extraA2Act (I := I) (M := M) g T V hδ_lt hδ hδZ := by
  simp only [extraA2Act, deTurckPrincipalCometricArm,
    iteratedCovGrad_add, appCc_add_right]
  abel

/-- The additional second-order action commutes with real scalar
multiplication in its passenger. -/
theorem extraA2_smul
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (c : ℝ)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    extraA2Act (I := I) (M := M) g T (c • U) hδ_lt hδ hδZ =
      c • extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ := by
  simp only [extraA2Act, deTurckPrincipalCometricArm,
    iteratedCovGrad_smul, appCc_smul_right]
  module

/-- Adding back the existing principal-cometric action recovers the complete
small second-order part of the refolded top path. -/
theorem extraA2_spec
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    deTurckPrincipalCometricArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ 1) U +
      extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ =
    appCc (I := I) (M := M) g 4 2
        (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
        (iteratedCovGrad (I := I) g 0 2 2 U) +
      appCc (I := I) (M := M) g 4 2
        (rhsTopPathIntegral (I := I) (M := M) g g T 0
            hδ_lt hδ hδ_lt hδZ -
          deTurckPhiMetTotal (I := I) (M := M) g g g)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  simp only [extraA2Act]
  abel

/-- The complete top path, after subtraction of the fixed connection
Laplacian, is the existing principal action, the additional small action, and
the fixed zeroth-order curvature term. -/
theorem top_a2_split
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    appCc (I := I) (M := M) g 4 2
        (rhsRefoldTopInt (I := I) (M := M) g g T
          hδ_lt hδ hδZ)
        (iteratedCovGrad (I := I) g 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g 0 2 U =
    deTurckPrincipalCometricArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ 1) U +
      extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
      appCc (I := I) (M := M) g 2 2
        (phiMetCurvCoeff (I := I) g g g)
        (iteratedCovGrad (I := I) g 0 2 0 U) := by
  rw [refold_top_split (I := I) (M := M) g g T U hδ_lt hδ hδZ,
    extraA2_spec (I := I) (M := M) g T U hδ_lt hδ hδZ]

/-- On a three-dimensional small spectral `H2` metric ball, the additional
second-order action is small from spectral `H4` to spectral `H2`. -/
theorem extraA2_h4_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (extraA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)‖ ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
  obtain ⟨ρr, Cr, hρr, hCr, href⟩ :=
    rhsRefold2Int_h4_h2 (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdev⟩ :=
    top_path_dev_h2 (I := I) (M := M) hDim g g
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h2_h4_h2 (I := I) (M := M) hDim g 2 2
  obtain ⟨ρp, Cp, hρp, hCp, hprincipal⟩ :=
    principal_arm_h4_h2 (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr (min ρd ρp)
  let C : ℝ := Cr + Capp * Cd + Cp
  refine ⟨ρ, C, by
    dsimp only [ρ]
    exact lt_min hρr (lt_min hρd hρp), by
    dsimp only [C]
    positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  have hRr : R ≤ ρr :=
    hRρ.trans (by dsimp only [ρ]; exact min_le_left _ _)
  have hRd : R ≤ ρd :=
    hRρ.trans (by
      dsimp only [ρ]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hRp : R ≤ ρp :=
    hRρ.trans (by
      dsimp only [ρ]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hzero :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR
  have href' := href T hδ_lt hδ hδZ hR hRr hT U
  obtain ⟨_, hdevJet⟩ :=
    hdev T (0 : SmoothCcTensor g 0 2)
      hδ_lt hδ hδ_lt hδZ hR hRd hT hzero
  have hdev' := happ
    (rhsTopPathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ -
      deTurckPhiMetTotal (I := I) (M := M) g g g)
    U (Cd * R) (mul_nonneg hCd hR) hdevJet
  have hTρp :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρp :=
    hT.trans hRp
  have hmem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨zero_le_one, le_rfl⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g T 0 hδ hδZ 1).inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w := by
    intro y v w
    simpa only [convexPerturbation_one] using
      realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ hmem y v w
  have hprincipal' :=
    hprincipal T (realizedFam (I := I) g T 0 hδ hδZ 1) U hTρp htie
  have hprincipalR :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ 1) U)‖ ≤
        Cp * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ :=
    hprincipal'.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT hCp)
        (norm_nonneg _))
  have hsub (A B : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (A - B) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) A -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) B := by
    rw [sub_eq_add_neg,
      show -B = (-1 : ℝ) • B by simp,
      ccTensorToHs_add, ccTensorToHs_smul]
    rw [sub_eq_add_neg]
    simp
  rw [extraA2Act, hsub, ccTensorToHs_add]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g g T 0
                hδ_lt hδ hδ_lt hδZ -
              deTurckPhiMetTotal (I := I) (M := M) g g g)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ 1) U)‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Cr * R * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ +
        (Capp * (Cd * R) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖) +
        Cp * R * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ :=
      add_le_add (add_le_add href' hdev') hprincipalR
    _ = C * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U‖ := by
      dsimp only [C]
      ring

/-- The same additional second-order action is small from spectral `H3` to
spectral `H1`; this is the lower-scale realization used for compatibility. -/
theorem extraA2_h3_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ U : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (extraA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)‖ ≤
            C * R *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  obtain ⟨ρr, Cr, hρr, hCr, href⟩ :=
    rhsRefold2Int_h3_h1 (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdev⟩ :=
    top_path_dev_h2 (I := I) (M := M) hDim g g
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_h2_h3_h1 (I := I) (M := M) hDim g 2 2
  obtain ⟨ρp, Cp, hρp, hCp, hprincipal⟩ :=
    principal_arm_h2 (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr (min ρd ρp)
  let C : ℝ := Cr + Capp * Cd + Cp
  refine ⟨ρ, C, by
    dsimp only [ρ]
    exact lt_min hρr (lt_min hρd hρp), by
    dsimp only [C]
    positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT U
  have hRr : R ≤ ρr :=
    hRρ.trans (by dsimp only [ρ]; exact min_le_left _ _)
  have hRd : R ≤ ρd :=
    hRρ.trans (by
      dsimp only [ρ]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hRp : R ≤ ρp :=
    hRρ.trans (by
      dsimp only [ρ]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hzero :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, ccTensorToHs_smul, zero_smul, norm_zero]
    exact hR
  have href' := href T hδ_lt hδ hδZ hR hRr hT U
  obtain ⟨hdevPt, hdevJet⟩ :=
    hdev T (0 : SmoothCcTensor g 0 2)
      hδ_lt hδ hδ_lt hδZ hR hRd hT hzero
  have hdev' := happ
    (rhsTopPathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ -
      deTurckPhiMetTotal (I := I) (M := M) g g g)
    U (Cd * R) (mul_nonneg hCd hR) hdevPt hdevJet
  have hTρp :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρp :=
    hT.trans hRp
  have hmem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨zero_le_one, le_rfl⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g T 0 hδ hδZ 1).inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w := by
    intro y v w
    simpa only [convexPerturbation_one] using
      realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ hmem y v w
  have hprincipal' :=
    hprincipal T (realizedFam (I := I) g T 0 hδ hδZ 1) U hTρp htie
  have hprincipalR :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ 1) U)‖ ≤
        Cp * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
    hprincipal'.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT hCp)
        (norm_nonneg _))
  have hsub (A B : SmoothCcTensor g 0 2) :
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) (A - B) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) A -
          ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) B := by
    rw [sub_eq_add_neg,
      show -B = (-1 : ℝ) • B by simp,
      ccTensorToHs_add, ccTensorToHs_smul]
    rw [sub_eq_add_neg]
    simp
  rw [extraA2Act, hsub, ccTensorToHs_add]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (appCc (I := I) (M := M) g 4 2
            (rhsTopPathIntegral (I := I) (M := M) g g T 0
                hδ_lt hδ hδ_lt hδZ -
              deTurckPhiMetTotal (I := I) (M := M) g g g)
            (iteratedCovGrad (I := I) g 0 2 2 U))‖ +
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ 1) U)‖ := by
          exact (norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Cr * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
        (Capp * (Cd * R) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖) +
        Cp * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
      add_le_add (add_le_add href' hdev') hprincipalR
    _ = C * R *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
      dsimp only [C]
      ring

private noncomputable def extraA2Core
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (σ : ℝ) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 →ₗ[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 σ where
  toFun := fun U =>
    ccTensorToHs (I := I) (M := M) g 2 σ
      (extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ)
  map_add' := fun U V => by
    rw [extraA2_add (I := I) (M := M) g T U V hδ_lt hδ hδZ,
      ccTensorToHs_add]
  map_smul' := fun c U => by
    rw [extraA2_smul (I := I) (M := M) g T U c hδ_lt hδ hδZ,
      ccTensorToHs_smul]
    rfl

/-- The additional second-order action, completed from spectral `H4` to
spectral `H2`.  Its small operator norm is proved jointly with the lower-scale
completion in `exists_extraA2_pair`. -/
noncomputable def extraA2Hi
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (2 : ℝ) :=
  (extraA2Core (I := I) (M := M) g T (2 : ℝ) hδ_lt hδ hδZ).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ))

/-- The same additional second-order action, completed from spectral `H3` to
spectral `H1`. -/
noncomputable def extraA2Lo
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
        (I := I) (M := M) g 0 2 (1 : ℝ) :=
  (extraA2Core (I := I) (M := M) g T (1 : ℝ) hδ_lt hδ hδZ).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

/-- In dimension three, the two Sobolev completions of the additional
second-order action have one common small-ball bound, agree with the same
smooth action, and commute with the adjacent Sobolev inclusions. -/
theorem exists_extraA2_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ‖extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ C * R ∧
        ‖extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ C * R ∧
        (∀ U : SmoothCcTensor g 0 2,
          extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (extraA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)) ∧
        (∀ U : SmoothCcTensor g 0 2,
          extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ
              (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (extraA2Act (I := I) (M := M)
                g T U hδ_lt hδ hδZ)) ∧
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
            (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ) =
          (extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
              (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρh, Ch, hρh, hCh, hhigh⟩ :=
    extraA2_h4_h2 (I := I) (M := M) hDim g
  obtain ⟨ρl, Cl, hρl, hCl, hlow⟩ :=
    extraA2_h3_h1 (I := I) (M := M) hDim g
  refine ⟨min ρh ρl, Ch + Cl, lt_min hρh hρl,
    add_nonneg hCh hCl, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR hRρ hT
  have hRh : R ≤ ρh := hRρ.trans (min_le_left _ _)
  have hRl : R ≤ ρl := hRρ.trans (min_le_right _ _)
  have hhigh' := hhigh T hδ_lt hδ hδZ hR hRh hT
  have hlow' := hlow T hδ_lt hδ hδZ hR hRl hT
  have hdense4 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hdense3 : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hHiNorm :
      ‖extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ Ch * R := by
    unfold extraA2Hi
    exact LinearMap.opNorm_extendOfNorm_le hdense4 (mul_nonneg hCh hR) hhigh'
  have hLoNorm :
      ‖extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤ Cl * R := by
    unfold extraA2Lo
    exact LinearMap.opNorm_extendOfNorm_le hdense3 (mul_nonneg hCl hR) hlow'
  have hHiCore (U : SmoothCcTensor g 0 2) :
      extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (extraA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ) := by
    change
      ((extraA2Core (I := I) (M := M) g T (2 : ℝ) hδ_lt hδ hδZ).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (4 : ℝ)) U) =
        (extraA2Core (I := I) (M := M)
          g T (2 : ℝ) hδ_lt hδ hδZ) U
    apply LinearMap.extendOfNorm_eq hdense4
    exact ⟨Ch * R, hhigh'⟩
  have hLoCore (U : SmoothCcTensor g 0 2) :
      extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          (extraA2Act (I := I) (M := M)
            g T U hδ_lt hδ hδZ) := by
    change
      ((extraA2Core (I := I) (M := M) g T (1 : ℝ) hδ_lt hδ hδZ).extendOfNorm
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)))
          ((ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) U) =
        (extraA2Core (I := I) (M := M)
          g T (1 : ℝ) hδ_lt hδ hδZ) U
    apply LinearMap.extendOfNorm_eq hdense3
    exact ⟨Cl * R, hlow'⟩
  have hHiNorm' :
      ‖extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤
        (Ch + Cl) * R :=
    hHiNorm.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCl) hR)
  have hLoNorm' :
      ‖extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ‖ ≤
        (Ch + Cl) * R :=
    hLoNorm.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCh) hR)
  refine ⟨hHiNorm', hLoNorm', hHiCore, hLoCore, ?_⟩
  let L :=
    (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
      (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (extraA2Hi (I := I) (M := M) g T hδ_lt hδ hδZ)
  let L' :=
    (extraA2Lo (I := I) (M := M) g T hδ_lt hδ hδZ).comp
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
        (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num))
  have hfun : (L : _ → _) = L' :=
    hdense4.equalizer L.continuous L'.continuous (by
      funext U
      simp only [Function.comp_apply, L, L', ccToHsLin_apply,
        ContinuousLinearMap.comp_apply]
      rw [hHiCore]
      have hin :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion
              (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
              (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
            ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U := by
        apply DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
        funext i
        simp only [
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply,
          ccTensorToHs_coeff]
      rw [hin, hLoCore]
      apply DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
      funext i
      simp only [
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsInclusion_coeff_apply,
        ccTensorToHs_coeff])
  apply ContinuousLinearMap.ext
  intro U
  exact congrFun hfun U

/-- The complete one-order-lower smooth action after the second-order arm has
been separated.  It contains the refolded zero-order path, the one-order path,
and the fixed curvature contribution of the background connection Laplacian. -/
def lowA1Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 2 2
      (rhsRefold0Int (I := I) (M := M) g g T hδ_lt hδ hδZ) U +
    appCc (I := I) (M := M) g 3 2
      (rhsLow1PathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ)
      (iteratedCovGrad (I := I) g 0 2 1 U) +
    appCc (I := I) (M := M) g 2 2
      (phiMetCurvCoeff (I := I) g g g)
      (iteratedCovGrad (I := I) g 0 2 0 U)

/-- On the smooth core, the full Ricci--DeTurck remainder difference is exactly
the principal-cometric action, the additional small second-order action, and
the complete one-order-lower action.  This is an algebraic identity; extending
the three actions to compatible adjacent Sobolev scales is a separate theorem. -/
theorem remainder_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    realizedRHSArm (I := I) g g T hδ_lt hδ -
          realizedRHSArm (I := I) g g 0 hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2 T =
      deTurckPrincipalCometricArm (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ 1) T +
        extraA2Act (I := I) (M := M) g T T hδ_lt hδ hδZ +
        lowA1Act (I := I) (M := M) g T T hδ_lt hδ hδZ := by
  rw [rhs_sub_zero_refold (I := I) (M := M)
    g g T hTsymm hδ_lt hδ hδZ]
  rw [show
      (appCc (I := I) (M := M) g 2 2
            (rhsRefold0Int (I := I) (M := M) g g T hδ_lt hδ hδZ) T +
          appCc (I := I) (M := M) g 3 2
            (rhsLow1PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          appCc (I := I) (M := M) g 4 2
            (rhsRefoldTopInt (I := I) (M := M) g g T
              hδ_lt hδ hδZ)
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
          rawTensorConnLapSmooth (I := I) g 0 2 T =
        appCc (I := I) (M := M) g 2 2
            (rhsRefold0Int (I := I) (M := M) g g T hδ_lt hδ hδZ) T +
          appCc (I := I) (M := M) g 3 2
            (rhsLow1PathIntegral (I := I) (M := M) g g T 0
              hδ_lt hδ hδ_lt hδZ)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          (appCc (I := I) (M := M) g 4 2
              (rhsRefoldTopInt (I := I) (M := M) g g T
                hδ_lt hδ hδZ)
              (iteratedCovGrad (I := I) g 0 2 2 T) -
            rawTensorConnLapSmooth (I := I) g 0 2 T) by abel]
  rw [top_a2_split (I := I) (M := M) g T T hδ_lt hδ hδZ]
  simp only [lowA1Act]
  abel

/-! ## Cancellation of the explicit refold pair

The `rhsRefold2Int` action was created by moving the second derivatives hidden
in the order-zero Palatini and Lie pair fields onto an arbitrary passenger.
On the diagonal, those pair fields occur with the opposite sign in
`rhsRefold0Int`.  The following two actions assign that common term to the
lower arm before cancelling it from the additional principal arm.  This is an
exact action-level normalization, not an estimate.
-/

/-- The additional second-order action after cancelling the explicit
Palatini/Lie refold pair against its order-zero occurrence. -/
def pairRedA2Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  extraA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ -
    appCc (I := I) (M := M) g 4 2
      (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
      (iteratedCovGrad (I := I) g 0 2 2 U)

/-- The lower action with the opposite explicit refold-pair action restored.
Its diagonal value is designed to be used together with `pairRedA2Act`. -/
def pairRedA1Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  lowA1Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
    appCc (I := I) (M := M) g 4 2
      (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
      (iteratedCovGrad (I := I) g 0 2 2 U)

/-- After the explicit pair cancellation, the reduced second-order action is
only the top-path deviation minus the geometric principal-cometric action. -/
theorem pairRedA2_eq
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pairRedA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ =
      appCc (I := I) (M := M) g 4 2
        (rhsTopPathIntegral (I := I) (M := M) g g T 0
            hδ_lt hδ hδ_lt hδZ -
          deTurckPhiMetTotal (I := I) (M := M) g g g)
        (iteratedCovGrad (I := I) g 0 2 2 U) -
      deTurckPrincipalCometricArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ 1) U := by
  simp only [pairRedA2Act, extraA2Act]
  abel

/-- The reduced second-order action is additive in its passenger. -/
theorem pairRedA2_add
    (g : SmoothRiemannianMetric I M)
    (T U V : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pairRedA2Act (I := I) (M := M) g T (U + V) hδ_lt hδ hδZ =
      pairRedA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
        pairRedA2Act (I := I) (M := M) g T V hδ_lt hδ hδZ := by
  simp only [pairRedA2Act, extraA2_add, iteratedCovGrad_add,
    appCc_add_right]
  abel

/-- The reduced second-order action commutes with scalar multiplication in
its passenger. -/
theorem pairRedA2_smul
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (c : ℝ)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pairRedA2Act (I := I) (M := M) g T (c • U) hδ_lt hδ hδZ =
      c • pairRedA2Act (I := I) (M := M) g T U hδ_lt hδ hδZ := by
  simp only [pairRedA2Act, extraA2_smul, iteratedCovGrad_smul,
    appCc_smul_right]
  module

/-- The reduced lower action is additive in its passenger. -/
theorem pairRedA1_add
    (g : SmoothRiemannianMetric I M)
    (T U V : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pairRedA1Act (I := I) (M := M) g T (U + V) hδ_lt hδ hδZ =
      pairRedA1Act (I := I) (M := M) g T U hδ_lt hδ hδZ +
        pairRedA1Act (I := I) (M := M) g T V hδ_lt hδ hδZ := by
  simp only [pairRedA1Act, lowA1Act, iteratedCovGrad_add,
    appCc_add_right]
  abel

/-- The reduced lower action commutes with scalar multiplication in its
passenger. -/
theorem pairRedA1_smul
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (c : ℝ)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    pairRedA1Act (I := I) (M := M) g T (c • U) hδ_lt hδ hδZ =
      c • pairRedA1Act (I := I) (M := M) g T U hδ_lt hδ hδZ := by
  simp only [pairRedA1Act, lowA1Act, iteratedCovGrad_smul,
    appCc_smul_right]
  module

/-- The complete remainder admits the same exact diagonal split after the
explicit Palatini/Lie pair has been cancelled between the two action slots. -/
theorem remainder_pair_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    realizedRHSArm (I := I) g g T hδ_lt hδ -
          realizedRHSArm (I := I) g g 0 hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2 T =
      deTurckPrincipalCometricArm (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ 1) T +
        pairRedA2Act (I := I) (M := M) g T T hδ_lt hδ hδZ +
        pairRedA1Act (I := I) (M := M) g T T hδ_lt hδ hδZ := by
  rw [remainder_split (I := I) (M := M) g T hTsymm hδ_lt hδ hδZ]
  simp only [pairRedA2Act, pairRedA1Act]
  abel

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
