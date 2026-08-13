import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFJetRadiusFree

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def gridBase (g₀ : SmoothRiemannianMetric I M) {rb sb : ℕ}
    (P : SmoothCcTensor g₀ rb sb)
    (x : M) : ℕ → ℝ :=
  fun j => riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + j) x
    ((iteratedCovGrad (I := I) g₀ rb sb j P).toSection x)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gridBase_nn (g₀ : SmoothRiemannianMetric I M) {rb sb : ℕ}
    (P : SmoothCcTensor g₀ rb sb)
    (x : M) (j : ℕ) : 0 ≤ gridBase (I := I) (M := M) g₀ P x j :=
  riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ rb (sb + j) x _

def foldConst (u v : ℕ) (KΦ KW : ℕ → ℝ) (n : ℕ) : ℝ :=
  appCcGdiag (E := E) n *
    ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      KΦ i' * KW l * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma foldConst_nn {u v : ℕ} {KΦ KW : ℕ → ℝ}
    (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l) (n : ℕ) :
    0 ≤ foldConst (E := E) u v KΦ KW n := by
  refine mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ =>
    Finset.sum_nonneg (fun l _ => ?_)))
  exact mul_nonneg (mul_nonneg (hKΦ i') (hKW l))
    (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)

theorem atgwFold (g₀ : SmoothRiemannianMetric I M) {p a b : ℕ} (u v : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    {rb sb : ℕ} (P : SmoothCcTensor g₀ rb sb) {KΦ KW : ℕ → ℝ}
    (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : ∀ (i' : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
          ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) ≤
        KΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (i' + u + 1))
    (hW : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
          ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
        KW l * Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (l + v + 1))
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + n) x
        ((iteratedCovGrad (I := I) g₀ p b n
          (appCcRS (I := I) (M := M) g₀ p a b Φ W)).toSection x) ≤
      foldConst (E := E) u v KΦ KW n * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (n + u + v + 1) := by
  classical
  set bP : ℕ → ℝ := gridBase (I := I) (M := M) g₀ P x with hbP_def
  have hbP : ∀ j, 0 ≤ bP j := gridBase_nn (I := I) (M := M) g₀ P x
  have hatgwn : 0 ≤ Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP _
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ n p a b Φ W x) ?_
  rw [foldConst, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) n)
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
          ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
        ∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
            ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
      ∑ l ∈ Finset.range (n + 1),
        (KΦ i' * KW l *
          Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1) := by
    intro i' hi'
    have hi'n : i' ≤ n := by rw [Finset.mem_range] at hi'; omega
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hKΦ i') (hKW l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)) hatgwn
    · have hmul := Combinatorics.antidiagonalTupleGridWindow_mul_le bP hbP (i' + u) (l + v)
      have hmono := Combinatorics.antidiagonalTupleGridWindow_mono bP hbP
        (show (i' + u) + (l + v) + 1 ≤ n + u + v + 1 by
          rw [Finset.mem_range] at hl; omega)
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v) :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _
      have hprod :
          riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
              ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
          (KΦ i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + u + 1)) *
            (KW l * Combinatorics.antidiagonalTupleGridWindow bP (l + v + 1)) :=
        mul_le_mul (hΦ i' x) (hW l x) (riemannianFiberNormSq_nonneg _ _ _ _ _)
          (mul_nonneg (hKΦ i')
            (Combinatorics.antidiagonalTupleGridWindow_nonneg bP hbP _))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
              ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x)
          ≤ (KΦ i' * Combinatorics.antidiagonalTupleGridWindow bP (i' + u + 1)) *
              (KW l * Combinatorics.antidiagonalTupleGridWindow bP (l + v + 1)) := hprod
        _ = KΦ i' * KW l *
              (Combinatorics.antidiagonalTupleGridWindow bP (i' + u + 1) *
                Combinatorics.antidiagonalTupleGridWindow bP (l + v + 1)) := by ring
        _ ≤ KΦ i' * KW l *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v) *
                Combinatorics.antidiagonalTupleGridWindow bP ((i' + u) + (l + v) + 1)) :=
            mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKΦ i') (hKW l))
        _ ≤ KΦ i' * KW l *
              (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v) *
                Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKΦ i') (hKW l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (KΦ i' * KW l *
              Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v)) *
              Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1) := by ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
            ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (KΦ i' * KW l *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v)) *
            Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1) :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          KΦ i' * KW l *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + u) (l + v)) *
          Combinatorics.antidiagonalTupleGridWindow bP (n + u + v + 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

theorem atgwToJetRs (g₀ : SmoothRiemannianMetric I M) (rb sb : ℕ)
    {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ rb sb),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ rb sb x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (r c n w : ℕ) (X : SmoothCcTensor g₀ r c) (K : ℝ), 0 ≤ K →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r (c + n) x
              ((iteratedCovGrad (I := I) g₀ r c n X).toSection x) ≤
            K * Combinatorics.antidiagonalTupleGridWindow
              (gridBase (I := I) (M := M) g₀ P x) (n + w)) →
          ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
            K * (∑ k ∈ Finset.range (n + w), Kint k) *
              (1 + ∑ j ∈ Finset.range (n + w),
                ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kint, hKint_nn, hKint⟩ :=
    atgGridIntRs (I := I) (M := M) g₀ rb sb hΛ₀0
  refine ⟨Kint, hKint_nn, ?_⟩
  intro P hsup r c n w X K hK hX
  have hgrid : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (gridBase (I := I) (M := M) g₀ P x) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Kint k * (1 + ‖iteratedCovGrad (I := I) g₀ rb sb k P‖ ^ 2) := by
    intro k
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (gridBase (I := I) (M := M) g₀ P x) k)
        = (fun x => ∑ m ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m k,
            ∏ q : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ rb (sb + e q) x
              ((iteratedCovGrad (I := I) g₀ rb sb (e q) P).toSection x)) := by
      funext y; rw [Combinatorics.antidiagonalTupleGrid]; rfl
    rw [hExpand]; exact hKint P hsup k
  have hwinInt : MeasureTheory.Integrable
      (fun x => K * Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (n + w))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    refine MeasureTheory.Integrable.const_mul ?_ K
    have : (fun x => Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (n + w))
        = (fun x => ∑ k ∈ Finset.range (n + w),
            Combinatorics.antidiagonalTupleGrid
              (gridBase (I := I) (M := M) g₀ P x) k) := by
      funext y; rw [Combinatorics.antidiagonalTupleGridWindow]
    rw [this]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ => (hgrid k).1)
  have hL2 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ r (c + n) (iteratedCovGrad (I := I) g₀ r c n X) _ hwinInt hX
  refine hL2.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hwinEq : (∫ x, Combinatorics.antidiagonalTupleGridWindow
        (gridBase (I := I) (M := M) g₀ P x) (n + w)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ k ∈ Finset.range (n + w), ∫ x, Combinatorics.antidiagonalTupleGrid
        (gridBase (I := I) (M := M) g₀ P x) k
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hpt : (fun x => Combinatorics.antidiagonalTupleGridWindow
          (gridBase (I := I) (M := M) g₀ P x) (n + w))
        = (fun x => ∑ k ∈ Finset.range (n + w),
            Combinatorics.antidiagonalTupleGrid
              (gridBase (I := I) (M := M) g₀ P x) k) := rfl
    rw [hpt, MeasureTheory.integral_finset_sum _ (fun k _ => (hgrid k).1)]
  rw [hwinEq]
  have hsumj : (0 : ℝ) ≤ ∑ j ∈ Finset.range (n + w),
      ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hstep : ∑ k ∈ Finset.range (n + w), ∫ x, Combinatorics.antidiagonalTupleGrid
        (gridBase (I := I) (M := M) g₀ P x) k
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) ≤
      (∑ k ∈ Finset.range (n + w), Kint k) *
        (1 + ∑ j ∈ Finset.range (n + w), ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    refine (hgrid k).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKint_nn k)
    have hle : ‖iteratedCovGrad (I := I) g₀ rb sb k P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (n + w), ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg
        ‖iteratedCovGrad (I := I) g₀ rb sb j P‖) hk
    linarith only [hle]
  calc K * ∑ k ∈ Finset.range (n + w), ∫ x, Combinatorics.antidiagonalTupleGrid
          (gridBase (I := I) (M := M) g₀ P x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ K * ((∑ k ∈ Finset.range (n + w), Kint k) *
          (1 + ∑ j ∈ Finset.range (n + w),
            ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hK
    _ = K * (∑ k ∈ Finset.range (n + w), Kint k) *
          (1 + ∑ j ∈ Finset.range (n + w),
            ‖iteratedCovGrad (I := I) g₀ rb sb j P‖ ^ 2) := by ring

theorem atgwToJet (g₀ : SmoothRiemannianMetric I M) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        ∀ (r c n w : ℕ) (X : SmoothCcTensor g₀ r c) (K : ℝ), 0 ≤ K →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r (c + n) x
              ((iteratedCovGrad (I := I) g₀ r c n X).toSection x) ≤
            K * Combinatorics.antidiagonalTupleGridWindow
              (gridBase (I := I) (M := M) g₀ P x) (n + w)) →
          ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
            K * (∑ k ∈ Finset.range (n + w), Kint k) *
              (1 + ∑ j ∈ Finset.range (n + w),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
  atgwToJetRs (I := I) (M := M) g₀ 0 2 hΛ₀0

end DifferentialGeometry.Integral.Connection

end
