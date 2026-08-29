import DifferentialGeometry.Geometry.Metric.Convergence.RicciFromJets
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedInvGramJetLipschitz
import Mathlib.Topology.Compactness.LocallyFinite

open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators Matrix

open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open Filter Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

private lemma abs_sub_le_sum (a b : Real) : |a - b| ≤ |a| + |b| := by
  exact abs_sub a b

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma basis_apply_le {m : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ)
    (v : Fin m → Fin (Module.finrank ℝ E)) :
    |F (fun i => (chartModelBasis E) (v i))| ≤
      ‖F‖ * (∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖) ^ m := by
  classical
  set B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsingle : ∀ i : Fin m, ‖(chartModelBasis E) (v i)‖ ≤ B := by
    intro i
    rw [hB]
    exact Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ (v i))
  have hprod : (∏ i : Fin m, ‖(chartModelBasis E) (v i)‖) ≤ B ^ m := by
    calc
      (∏ i : Fin m, ‖(chartModelBasis E) (v i)‖) ≤ ∏ _i : Fin m, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hsingle i)
      _ = B ^ m := by simp
  have hop := F.le_opNorm (fun i => (chartModelBasis E) (v i))
  rw [Real.norm_eq_abs] at hop
  exact hop.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg F))

set_option maxHeartbeats 400000 in
-- The finite-coordinate order-zero jet expansion exceeds the default budget.
omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jet0Diff_le_dNorm
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |(chartGramMatrix (I := I) u α y - chartGramMatrix (I := I) u' α y) p.1 p.2|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C0, hC0, h0⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 0
  let A0 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨A0 * C0, mul_nonneg hA0 hC0, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hsum :
      (∑ q ∈ Finset.range 1, metricDerivNorm (I := I) q u u' gRef y) ≤ S := by
    rw [hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => Real.sqrt_nonneg _)
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      |chartGramMatrix (I := I) u α y a b - chartGramMatrix (I := I) u' α y a b| ≤
        C0 * S := by
    intro a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have happ := basis_apply_le (E := E)
      (iteratedFDeriv ℝ 0 f z - iteratedFDeriv ℝ 0 f' z) (![] : Fin 0 → _)
    have hraw := h0 u u' y hy a b
    have heval :
        (iteratedFDeriv ℝ 0 f z - iteratedFDeriv ℝ 0 f' z) (![] : Fin 0 → E) =
          f z - f' z := by simp [iteratedFDeriv_zero_apply]
    have hargs : (fun i : Fin 0 =>
        (chartModelBasis E) ((![] : Fin 0 → Fin (Module.finrank ℝ E)) i)) =
        (![] : Fin 0 → E) := Subsingleton.elim _ _
    rw [hargs, heval, pow_zero, mul_one] at happ
    simpa only [f, f', chartGramOnE_def, hψ] using
      happ.trans (hraw.trans (mul_le_mul_of_nonneg_left hsum hC0))
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        |(chartGramMatrix (I := I) u α y - chartGramMatrix (I := I) u' α y) p.1 p.2|)
        ≤ A0 * (C0 * S) := by
          dsimp only [A0]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [Matrix.sub_apply, one_mul] using hentry p.1 p.2
    _ = (A0 * C0) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

set_option maxHeartbeats 400000 in
-- The finite-coordinate order-one jet expansion exceeds the default budget.
omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jet1Diff_le_dNorm
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u α p.1 p.2.2)
              (extChartAt I α y) -
            partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' α p.1 p.2.2)
              (extChartAt I α y)|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C1, hC1, h1⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 1
  let B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let A1 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E), B
  have hA1 : 0 ≤ A1 := Finset.sum_nonneg fun _ _ => hB
  refine ⟨A1 * C1, mul_nonneg hA1 hC1, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hsum :
      (∑ q ∈ Finset.range 2, metricDerivNorm (I := I) q u u' gRef y) ≤ S := by
    rw [hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => Real.sqrt_nonneg _)
  have hentry : ∀ d a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) d (chartGramOnE (I := I) u α a b) z -
        partialDeriv (E := E) d (chartGramOnE (I := I) u' α a b) z| ≤ C1 * B * S := by
    intro d a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have happ := basis_apply_le (E := E)
      (iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z) ![d]
    have heval : (iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z)
          ![(chartModelBasis E) d] = partialDeriv (E := E) d f z - partialDeriv (E := E) d f' z := by
      simp only [ContinuousMultilinearMap.sub_apply]
      rw [partialDeriv_eq_iteratedFDeriv_one, partialDeriv_eq_iteratedFDeriv_one]
    have hargs : (fun i : Fin 1 => (chartModelBasis E) (![d] i)) =
        ![(chartModelBasis E) d] := by
      funext i
      fin_cases i
      rfl
    rw [hargs, heval, pow_one] at happ
    have hraw := h1 u u' y hy a b
    rw [show chartGramOnE (I := I) u α a b = f from rfl,
      show chartGramOnE (I := I) u' α a b = f' from rfl]
    calc
      |partialDeriv (E := E) d f z - partialDeriv (E := E) d f' z| ≤
          ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z‖ * B := happ
      _ ≤ (C1 * S) * B := mul_le_mul_of_nonneg_right
        (hraw.trans (mul_le_mul_of_nonneg_left hsum hC1)) hB
      _ = C1 * B * S := by ring
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u α p.1 p.2.2) z -
        partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' α p.1 p.2.2) z|)
        ≤ A1 * (C1 * S) := by
          dsimp only [A1]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [B, mul_comm, mul_left_comm, mul_assoc] using hentry p.2.1 p.1 p.2.2
    _ = (A1 * C1) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

set_option maxHeartbeats 400000 in
-- The finite-coordinate order-two jet expansion exceeds the default budget.
omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jet2Sum_le_dNorm
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) u α p.2.2.1 p.2.2.2)) (extChartAt I α y) -
            partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) u' α p.2.2.1 p.2.2.2)) (extChartAt I α y)|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C2, hC2, h2⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 2
  let B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let A2 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2
  have hA2 : 0 ≤ A2 := Finset.sum_nonneg fun _ _ => sq_nonneg B
  refine ⟨A2 * C2, mul_nonneg hA2 hC2, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hentry : ∀ d c a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) d (partialDeriv (E := E) c
          (chartGramOnE (I := I) u α a b)) z -
        partialDeriv (E := E) d (partialDeriv (E := E) c
          (chartGramOnE (I := I) u' α a b)) z| ≤ C2 * B ^ 2 * S := by
    intro d c a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have hf : ContDiffAt ℝ ∞ f z :=
      (chartGramOnE_contDiffOn_int (I := I) u α a b).contDiffAt
        (isOpen_interior.mem_nhds hzint)
    have hf' : ContDiffAt ℝ ∞ f' z :=
      (chartGramOnE_contDiffOn_int (I := I) u' α a b).contDiffAt
        (isOpen_interior.mem_nhds hzint)
    have happ := basis_apply_le (E := E)
      (iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z) ![d, c]
    have heval : (iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z)
          ![(chartModelBasis E) d, (chartModelBasis E) c] =
        partialDeriv (E := E) d (partialDeriv (E := E) c f) z -
          partialDeriv (E := E) d (partialDeriv (E := E) c f') z := by
      simp only [ContinuousMultilinearMap.sub_apply]
      rw [partialDeriv_partialDeriv_eq_iteratedFDeriv_two f hf d c,
        partialDeriv_partialDeriv_eq_iteratedFDeriv_two f' hf' d c]
    have hargs : (fun i : Fin 2 => (chartModelBasis E) (![d, c] i)) =
        ![(chartModelBasis E) d, (chartModelBasis E) c] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs, heval] at happ
    have hraw := h2 u u' y hy a b
    have hraw' :
        ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z‖ ≤ C2 * S := by
      simpa only [Nat.reduceAdd, hS] using hraw
    rw [show chartGramOnE (I := I) u α a b = f from rfl,
      show chartGramOnE (I := I) u' α a b = f' from rfl]
    calc
      |partialDeriv (E := E) d (partialDeriv (E := E) c f) z -
          partialDeriv (E := E) d (partialDeriv (E := E) c f') z| ≤
          ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z‖ * B ^ 2 := happ
      _ ≤ (C2 * S) * B ^ 2 := mul_le_mul_of_nonneg_right
        hraw' (sq_nonneg B)
      _ = C2 * B ^ 2 * S := by ring
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) p.1
          (partialDeriv (E := E) p.2.1
            (chartGramOnE (I := I) u α p.2.2.1 p.2.2.2)) z -
        partialDeriv (E := E) p.1
          (partialDeriv (E := E) p.2.1
            (chartGramOnE (I := I) u' α p.2.2.1 p.2.2.2)) z|)
        ≤ A2 * (C2 * S) := by
          dsimp only [A2]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [B, mul_comm, mul_left_comm, mul_assoc] using
              hentry p.1 p.2.1 p.2.2.1 p.2.2.2
    _ = (A2 * C2) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jet2Diff_le_dNorm_on
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        chartMetricJet2DiffSup (I := I) (M := M) u u' α (extChartAt I α y) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C0, hC0, h0⟩ := jet0Diff_le_dNorm (I := I) gRef α hK hKchart
  obtain ⟨C1, hC1, h1⟩ := jet1Diff_le_dNorm (I := I) gRef α hK hKchart
  obtain ⟨C2, hC2, h2⟩ := jet2Sum_le_dNorm (I := I) gRef α hK hKchart
  refine ⟨C0 + C1 + C2, by positivity, ?_⟩
  intro u u' y hy
  have hψ : (extChartAt I α).symm (extChartAt I α y) = y :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  unfold chartMetricJet2DiffSup chartMetricJet1DiffSup chartGramDiffSup matrixEntryL1
    chartGramPartialDiffSup gramPartialDiffEntry chartGramPartial2DiffSup gramPartial2DiffEntry
  rw [hψ]
  calc
    _ ≤ C0 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) +
        C1 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) +
        C2 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) :=
      add_le_add (add_le_add (h0 u u' y hy) (h1 u u' y hy)) (h2 u u' y hy)
    _ = (C0 + C1 + C2) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by ring

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gram12_le_on
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (B : Real) :
    ∃ Q : Real, 0 ≤ Q ∧ ∀ w : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a w gRef y ≤ B) →
      ∀ y ∈ K,
        (∀ m a b : Fin (Module.finrank Real E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) w α a b)
            (extChartAt I α y)| ≤ Q) ∧
        (∀ d m a b : Fin (Module.finrank Real E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartGramOnE (I := I) w α a b))
              (extChartAt I α y)| ≤ Q) := by
  classical
  let 𝓖 := {w : SmoothRiemannianMetric I M //
    ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a w gRef y ≤ B}
  let gFam : 𝓖 → SmoothRiemannianMetric I M := fun w => w.1
  have hbdd : ∀ q : ℕ, q ≤ 2 → ∃ C : Real, ∀ k : 𝓖, ∀ y ∈ K,
      metricCovDerivNorm (I := I) q (gFam k) gRef y ≤ C := by
    intro q hq
    exact ⟨B, fun k y hy => k.2 y hy q hq⟩
  obtain ⟨Q1, hQ10, hQ1⟩ := chartGram_iter_le (I := I) gRef gFam α hK hKchart 1
    (fun q hq => hbdd q (by omega))
  obtain ⟨Q2, hQ20, hQ2⟩ := chartGram_iter_le (I := I) gRef gFam α hK hKchart 2 hbdd
  set V : Real := ∑ a : Fin (Module.finrank Real E), ‖(chartModelBasis E) a‖ with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨max (Q1 * V) (Q2 * V ^ 2),
    le_max_of_le_left (mul_nonneg hQ10 hV0), ?_⟩
  intro w hw y hy
  let k : 𝓖 := ⟨w, hw⟩
  constructor
  · intro m a b
    let f : E → Real := chartGramOnE (I := I) w α a b
    have happ := basis_apply_le (E := E) (iteratedFDeriv Real 1 f (extChartAt I α y)) ![m]
    have heval : iteratedFDeriv Real 1 f (extChartAt I α y)
          ![(chartModelBasis E) m] = partialDeriv (E := E) m f (extChartAt I α y) := by
      rw [partialDeriv_eq_iteratedFDeriv_one]
    have hargs : (fun i : Fin 1 => (chartModelBasis E) (![m] i)) =
        ![(chartModelBasis E) m] := by
      funext i
      fin_cases i
      rfl
    rw [hargs, heval, pow_one] at happ
    rw [show chartGramOnE (I := I) w α a b = f from rfl]
    exact happ.trans <| (mul_le_mul_of_nonneg_right (hQ1 k y hy a b) hV0).trans <|
      le_max_left _ _
  · intro d m a b
    let f : E → Real := chartGramOnE (I := I) w α a b
    have hyint : extChartAt I α y ∈ interior (extChartAt I α).target := by
      rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
      exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
    have hf : ContDiffAt Real ∞ f (extChartAt I α y) :=
      (chartGramOnE_contDiffOn_int (I := I) w α a b).contDiffAt
        (isOpen_interior.mem_nhds hyint)
    have happ := basis_apply_le (E := E) (iteratedFDeriv Real 2 f (extChartAt I α y)) ![d, m]
    have heval : iteratedFDeriv Real 2 f (extChartAt I α y)
          ![(chartModelBasis E) d, (chartModelBasis E) m] =
        partialDeriv (E := E) d (partialDeriv (E := E) m f) (extChartAt I α y) := by
      rw [partialDeriv_partialDeriv_eq_iteratedFDeriv_two f hf d m]
    have hargs : (fun i : Fin 2 => (chartModelBasis E) (![d, m] i)) =
        ![(chartModelBasis E) d, (chartModelBasis E) m] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs, heval] at happ
    rw [show chartGramOnE (I := I) w α a b = f from rfl]
    exact happ.trans <| (mul_le_mul_of_nonneg_right (hQ2 k y hy a b) (sq_nonneg V)).trans <|
      le_max_right _ _

set_option maxHeartbeats 800000 in
-- The nested coordinate Ricci-difference expansion exceeds the default budget.
omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
private theorem chartRicci_sub_le_on
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K, ∀ i k : Fin (Module.finrank Real E),
        |chartRicciTensor (I := I) u α i k (extChartAt I α y) -
          chartRicciTensor (I := I) u' α i k (extChartAt I α y)| ≤
        C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := gram12_le_on (I := I) gRef α hK hKchart B
  obtain ⟨Mb, hMb0, hMb⟩ := invGram_le_of_lowOn (I := I) gRef α hK hKchart lam hlam
  obtain ⟨CJ, hCJ0, hCJ⟩ := jet2Diff_le_dNorm_on (I := I) gRef α hK hKchart
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set P : Real := 3 * Q with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set R : Real := 3 * Q with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set Cinv : Real := nR ^ 2 * Mb ^ 2 with hCinv
  have hCinv0 : 0 ≤ Cinv := by rw [hCinv]; positivity
  set D : Real := nR ^ 2 * Mb ^ 2 * Q with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Cd : Real := nR ^ 2 * (2 * Cinv * Mb * Q + Mb ^ 2) with hCd
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  set Clip : Real := (1 / 2) * nR * (Cinv * P + 3 * Mb) with hClip
  have hClip0 : 0 ≤ Clip := by rw [hClip]; positivity
  set Cdiff : Real := (1 / 2) * nR * (Cd * P + 3 * D + Cinv * R + 3 * Mb) with hCdiff
  have hCdiff0 : 0 ≤ Cdiff := by rw [hCdiff]; positivity
  set Mg : Real := (1 / 2) * nR * Mb * P with hMg
  have hMg0 : 0 ≤ Mg := by rw [hMg]; positivity
  set Cr : Real := 2 * nR * Cdiff + 4 * nR ^ 2 * Clip * Mg with hCr
  have hCr0 : 0 ≤ Cr := by rw [hCr]; positivity
  refine ⟨Cr * CJ + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy i k
  set z : E := extChartAt I α y with hz
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hybase : y ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKchart hy
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hQu := (hQ u hcovu y hy).1
  have hQu' := (hQ u' hcovu' y hy).1
  have hQQu := (hQ u hcovu y hy).2
  have hMbu : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u (hlowu y hy) a b
  have hMbu' : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u' α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u' (hlowu' y hy) a b
  have hCinv' : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z - chartInvGramOnE (I := I) u' α a b z| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) u u' α ((extChartAt I α).symm z) := by
    intro a b
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    have h := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup (I := I) (M := M)
      u u' α hybase
      (fun p q => hMb y hy u (hlowu y hy) p q)
      (fun p q => hMb y hy u' (hlowu' y hy) p q) a b
    rw [hCinv, hnR]
    exact h
  have hPu : ∀ a b c : Fin (Module.finrank Real E),
      |gramBracket (I := I) u α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact gramBracket_abs_le (I := I) (M := M) u α z hQu a b c
  have hPu' : ∀ a b c : Fin (Module.finrank Real E),
      |gramBracket (I := I) u' α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact gramBracket_abs_le (I := I) (M := M) u' α z hQu' a b c
  have hRu : ∀ d a b c : Fin (Module.finrank Real E),
      |gramBracketDeriv (I := I) u α d a b c z| ≤ R := by
    intro d a b c
    rw [hR]
    exact gramBracketD_abs_le (I := I) (M := M) u α z hQQu d a b c
  have hDu' : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u' α a b) z| ≤ D := by
    intro d a b
    have h := invGramD_abs_le (I := I) (M := M) u' α hzint hMb0 hMbu' hQu' d a b
    rw [hD, hnR]
    exact h
  have hCd' : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u α a b) z -
        partialDeriv (E := E) d (chartInvGramOnE (I := I) u' α a b) z| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) u u' α z := by
    intro d a b
    have h := partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M)
      u u' α hzint hMb0 hQ0 hCinv0 hMbu hMbu' hQu hCinv' d a b
    rw [hCd, hCinv, hnR]
    exact h
  have hClip' : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z -
        chartChristoffel (I := I) u' α a b c z| ≤
        Clip * chartMetricJet1DiffSup (I := I) (M := M) u u' α z := by
    intro a b c
    have h := chartChristoffel_sub_abs_le (I := I) (M := M)
      u u' α hP0 hMb0 hMbu' hPu hCinv' hCinv0 a b c
    rw [hClip, hnR]
    exact h
  have hCdiff' : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) u α a b c) z -
        partialDeriv (E := E) d (chartChristoffel (I := I) u' α a b c) z| ≤
        Cdiff * chartMetricJet2DiffSup (I := I) (M := M) u u' α z := by
    intro d a b c
    have h := partialDeriv_chartChristoffel_sub_abs_le (I := I) (M := M)
      u u' α hzint hCd0 hCinv0 hMb0 hP0 hD0 hR0 d a b c
      (fun p q => hCd' d p q) hMbu' hPu (fun p q => hDu' d p q)
      (fun p q r => hRu d p q r) hCinv'
    rw [hCdiff, hCd, hCinv, hD, hR, hnR]
    exact h
  have hMgu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u α z a b c hMb0
      (fun l => hMbu c l) (fun l => hPu a b l)
    rw [hMg, hnR]
    exact h
  have hMgu' : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u' α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u' α z a b c hMb0
      (fun l => hMbu' c l) (fun l => hPu' a b l)
    rw [hMg, hnR]
    exact h
  have h2nd := chartRicciSecondOrderTerm_sub_abs_le (I := I) (M := M)
    u u' α hCdiff' i k
  have h1st := chartRicciFirstOrderTerm_sub_abs_le (I := I) (M := M)
    u u' α hClip0 hMg0 hClip' hMgu hMgu' i k
  set jet2 : Real := chartMetricJet2DiffSup (I := I) (M := M) u u' α z with hjet
  have hjet0 : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1 : chartMetricJet1DiffSup (I := I) (M := M) u u' α z ≤ jet2 :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' α z
  have hricJet : |chartRicciTensor (I := I) u α i k z -
      chartRicciTensor (I := I) u' α i k z| ≤ Cr * jet2 := by
    rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u α i k z,
      chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u' α i k z]
    rw [show
      (chartRicciSecondOrderTerm (I := I) u α i k z +
          chartRicciFirstOrderTerm (I := I) u α i k z) -
        (chartRicciSecondOrderTerm (I := I) u' α i k z +
          chartRicciFirstOrderTerm (I := I) u' α i k z) =
        (chartRicciSecondOrderTerm (I := I) u α i k z -
          chartRicciSecondOrderTerm (I := I) u' α i k z) +
        (chartRicciFirstOrderTerm (I := I) u α i k z -
          chartRicciFirstOrderTerm (I := I) u' α i k z) by ring]
    refine (abs_add_le _ _).trans ?_
    have h1st' : |chartRicciFirstOrderTerm (I := I) u α i k z -
        chartRicciFirstOrderTerm (I := I) u' α i k z| ≤
        4 * nR ^ 2 * Clip * Mg * jet2 := by
      refine h1st.trans ?_
      rw [hnR]
      exact mul_le_mul_of_nonneg_left hjet1 (by positivity)
    calc
      |chartRicciSecondOrderTerm (I := I) u α i k z -
          chartRicciSecondOrderTerm (I := I) u' α i k z| +
          |chartRicciFirstOrderTerm (I := I) u α i k z -
            chartRicciFirstOrderTerm (I := I) u' α i k z|
          ≤ 2 * nR * Cdiff * jet2 + 4 * nR ^ 2 * Clip * Mg * jet2 := by
            rw [hnR]
            exact add_le_add h2nd h1st'
      _ = Cr * jet2 := by rw [hCr]; ring
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hjet_le : jet2 ≤ CJ * S := by
    rw [hjet, hz]
    exact hCJ u u' y hy
  calc
    |chartRicciTensor (I := I) u α i k (extChartAt I α y) -
        chartRicciTensor (I := I) u' α i k (extChartAt I α y)|
        = |chartRicciTensor (I := I) u α i k z -
            chartRicciTensor (I := I) u' α i k z| := by rw [hz]
    _ ≤ Cr * jet2 := hricJet
    _ ≤ Cr * (CJ * S) := mul_le_mul_of_nonneg_left hjet_le hCr0
    _ ≤ (Cr * CJ + 1) * S := by nlinarith

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] in
private lemma chartRicci_abs_of_bnds
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) (α : M) (y : E)
    {Mg Md : Real} (hMg0 : 0 ≤ Mg)
    (hMg : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) g α a b c y| ≤ Mg)
    (hMd : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) g α a b c) y| ≤ Md)
    (i k : Fin (Module.finrank Real E)) :
    |chartRicciTensor (I := I) g α i k y| ≤
      2 * (Module.finrank Real E : Real) * Md +
        2 * (Module.finrank Real E : Real) ^ 2 * Mg ^ 2 := by
  classical
  rw [chartRicciTensor_eq_secondOrder_add_firstOrder]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · unfold chartRicciSecondOrderTerm
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ j : Fin (Module.finrank Real E),
          |partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y|)
          ≤ ∑ _j : Fin (Module.finrank Real E), 2 * Md := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine (abs_sub_le_sum _ _).trans ?_
            linarith [hMd j i k j, hMd k i j j]
      _ = 2 * (Module.finrank Real E : Real) * Md := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  · unfold chartRicciFirstOrderTerm
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ j : Fin (Module.finrank Real E),
          |∑ m : Fin (Module.finrank Real E),
            (chartChristoffel (I := I) g α j m j y * chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m j y * chartChristoffel (I := I) g α i j m y)|)
          ≤ ∑ _j : Fin (Module.finrank Real E),
              ∑ _m : Fin (Module.finrank Real E), 2 * Mg ^ 2 := by
            refine Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
            refine Finset.sum_le_sum fun m _ => ?_
            refine (abs_sub_le_sum _ _).trans ?_
            rw [abs_mul, abs_mul]
            have h1 := mul_le_mul (hMg j m j) (hMg i k m) (abs_nonneg _) hMg0
            have h2 := mul_le_mul (hMg k m j) (hMg i j m) (abs_nonneg _) hMg0
            nlinarith
      _ = 2 * (Module.finrank Real E : Real) ^ 2 * Mg ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
private theorem chartRicci_abs_le_on
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 ≤ C ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      ∀ y ∈ K, ∀ i k : Fin (Module.finrank Real E),
        |chartRicciTensor (I := I) u α i k (extChartAt I α y)| ≤ C := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := gram12_le_on (I := I) gRef α hK hKchart B
  obtain ⟨Mb, hMb0, hMb⟩ := invGram_le_of_lowOn (I := I) gRef α hK hKchart lam hlam
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set P : Real := 3 * Q with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set R : Real := 3 * Q with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set D : Real := nR ^ 2 * Mb ^ 2 * Q with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Mg : Real := (1 / 2) * nR * Mb * P with hMg
  have hMg0 : 0 ≤ Mg := by rw [hMg]; positivity
  set Md : Real := (1 / 2) * nR * (D * P + Mb * R) with hMd
  have hMd0 : 0 ≤ Md := by rw [hMd]; positivity
  set C : Real := 2 * nR * Md + 2 * nR ^ 2 * Mg ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, ?_⟩
  intro u hlow hcov y hy i k
  set z : E := extChartAt I α y with hz
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hQu := (hQ u hcov y hy).1
  have hQQu := (hQ u hcov y hy).2
  have hMbu : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u (hlow y hy) a b
  have hPu : ∀ a b c : Fin (Module.finrank Real E),
      |gramBracket (I := I) u α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact gramBracket_abs_le (I := I) (M := M) u α z hQu a b c
  have hRu : ∀ d a b c : Fin (Module.finrank Real E),
      |gramBracketDeriv (I := I) u α d a b c z| ≤ R := by
    intro d a b c
    rw [hR]
    exact gramBracketD_abs_le (I := I) (M := M) u α z hQQu d a b c
  have hDu : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u α a b) z| ≤ D := by
    intro d a b
    have h := invGramD_abs_le (I := I) (M := M) u α hzint hMb0 hMbu hQu d a b
    rw [hD, hnR]
    exact h
  have hMgu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u α z a b c hMb0
      (fun l => hMbu c l) (fun l => hPu a b l)
    rw [hMg, hnR]
    exact h
  have hMdu : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) u α a b c) z| ≤ Md := by
    intro d a b c
    have h := christoffelD_abs_le (I := I) (M := M) u α hzint d a b c
      hMb0 hD0 (fun l => hMbu c l) (fun l => hDu d c l)
      (fun l => hPu a b l) (fun l => hRu d a b l)
    rw [hMd, hnR]
    exact h
  have h := chartRicci_abs_of_bnds (I := I) u α z hMg0 hMgu hMdu i k
  rw [hz] at h
  rw [hC, hnR]
  exact h

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
private theorem scalarSub_le_on
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Cric, hCric0, hCric⟩ :=
    chartRicci_sub_le_on (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Cari, hCari0, hCari⟩ :=
    chartRicci_abs_le_on (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Minv, hMinv0, hMinv⟩ :=
    invGram_le_of_lowOn (I := I) gRef α hK hKchart lam hlam
  obtain ⟨CJ, hCJ0, hCJ⟩ := jet2Diff_le_dNorm_on (I := I) gRef α hK hKchart
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set Cinv : Real := nR ^ 2 * Minv ^ 2 with hCinv
  have hCinv0 : 0 ≤ Cinv := by rw [hCinv]; positivity
  set Ci : Real := Cinv * CJ with hCi
  have hCi0 : 0 ≤ Ci := by rw [hCi]; positivity
  set Ct : Real := Ci * Cari + Minv * Cric with hCt
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  refine ⟨nR ^ 2 * Ct + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  set z : E := extChartAt I α y with hz
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hybase : y ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKchart hy
  have hyg : y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]
    exact hKchart hy
  have hMinvu : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α i j z| ≤ Minv := by
    intro i j
    rw [chartInvGramOnE_def, hψ]
    exact hMinv y hy u (hlowu y hy) i j
  have hMinvu' : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u' α i j z| ≤ Minv := by
    intro i j
    rw [chartInvGramOnE_def, hψ]
    exact hMinv y hy u' (hlowu' y hy) i j
  have hInv : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z| ≤
        Ci * S := by
    intro i j
    have hmatrix := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup (I := I) (M := M)
      u u' α hybase
      (fun p q => hMinv y hy u (hlowu y hy) p q)
      (fun p q => hMinv y hy u' (hlowu' y hy) p q) i j
    have hgram : chartGramDiffSup (I := I) (M := M) u u' α y ≤
        chartMetricJet2DiffSup (I := I) (M := M) u u' α z := by
      rw [← hψ]
      exact (chartGramDiffSup_le_jet1 (I := I) (M := M) u u' α z).trans
        (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' α z)
    have hjet : chartMetricJet2DiffSup (I := I) (M := M) u u' α z ≤ CJ * S := by
      rw [hz, hS]
      exact hCJ u u' y hy
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    calc
      |chartInvGramMatrix (I := I) u α y i j - chartInvGramMatrix (I := I) u' α y i j|
          ≤ Cinv * chartGramDiffSup (I := I) (M := M) u u' α y := by
            rw [hCinv, hnR]
            exact hmatrix
      _ ≤ Cinv * chartMetricJet2DiffSup (I := I) (M := M) u u' α z :=
        mul_le_mul_of_nonneg_left hgram hCinv0
      _ ≤ Cinv * (CJ * S) := mul_le_mul_of_nonneg_left hjet hCinv0
      _ = Ci * S := by rw [hCi]; ring
  have hscalar (w : SmoothRiemannianMetric I M) :
      metricScalarAt (I := I) w y =
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) w α i j z * chartRicciTensor (I := I) w α i j z := by
    rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (I := I) w α hyg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ricciTensor_chartBasisVec_alpha_eq (I := I) w α i j hyg, hz]
  rw [hscalar u, hscalar u']
  have hdiff :
      (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u α i j z * chartRicciTensor (I := I) u α i j z) -
        (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u' α i j z * chartRicciTensor (I := I) u' α i j z) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff]
  have hterm : ∀ i j : Fin (Module.finrank Real E),
      |(chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
          chartRicciTensor (I := I) u α i j z +
        chartInvGramOnE (I := I) u' α i j z *
          (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)| ≤
        Ct * S := by
    intro i j
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA := hCari u hlowu hcovu y hy i j
    have hR := hCric u u' hlowu hlowu' hcovu hcovu' y hy i j
    have h1 := mul_le_mul (hInv i j) hA (abs_nonneg _) (mul_nonneg hCi0 hS0)
    have h2 := mul_le_mul (hMinvu' i j) hR (abs_nonneg _) hMinv0
    rw [hCt]
    nlinarith
  calc
    |∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z))|
        ≤ ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E), Ct * S := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun j _ => hterm i j
    _ = nR ^ 2 * Ct * S := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hnR]
      ring
    _ ≤ (nR ^ 2 * Ct + 1) * S := by nlinarith

omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
/-- Scalar curvature is uniformly Lipschitz in the metric two-jet on a fixed
compact set, under uniform ellipticity and covariant two-jet bounds there. -/
theorem scalarSub_le_dNormOn
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  let ρ := chartAtlasPOU I M
  have hKα : ∀ α : M, IsCompact
      (K ∩ tsupport (fun y : M => (ρ α : M → Real) y)) := fun α =>
    hK.inter_right (isClosed_tsupport (fun y : M => (ρ α : M → Real) y))
  have hKchart : ∀ α : M,
      K ∩ tsupport (fun y : M => (ρ α : M → Real) y) ⊆ (chartAt H α).source := by
    intro α y hy
    exact (chartAtlasPOU_isSubordinate I M) α hy.2
  choose Cα hCα0 hCα using fun α : M =>
    scalarSub_le_on (I := I) gRef α (hKα α) (hKchart α) lam B hlam
  let A : Set M := {α : M | (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty}
  have hA : A.Finite := by
    dsimp [A]
    exact ρ.locallyFinite.finite_nonempty_inter_compact hK
  let active : Finset M := hA.toFinset
  have hactive (α : M) : α ∈ active ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty := by
    change α ∈ hA.toFinset ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty
    rw [Set.Finite.mem_toFinset]
    rfl
  have hsum0 : 0 ≤ ∑ α ∈ active, Cα α :=
    Finset.sum_nonneg fun α _ => (hCα0 α).le
  refine ⟨(∑ α ∈ active, Cα α) + 1, by linarith, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  obtain ⟨α, hαpos⟩ := ρ.exists_pos_of_mem (Set.mem_univ y)
  have hysupp : y ∈ Function.support (fun z : M => (ρ α : M → Real) z) := ne_of_gt hαpos
  have hαS : α ∈ active := hactive α |>.2 ⟨y, hysupp, hy⟩
  have hyKα : y ∈ K ∩ tsupport (fun z : M => (ρ α : M → Real) z) :=
    ⟨hy, subset_closure hysupp⟩
  have hloc := hCα α u u'
    (fun z hz ξ => hlowu z hz.1 ξ)
    (fun z hz ξ => hlowu' z hz.1 ξ)
    (fun z hz a ha => hcovu z hz.1 a ha)
    (fun z hz a ha => hcovu' z hz.1 a ha)
    y hyKα
  have hCαle : Cα α ≤ ∑ β ∈ active, Cα β :=
    Finset.single_le_sum (fun β _ => (hCα0 β).le) hαS
  have hD0 : 0 ≤ ∑ q ∈ Finset.range 3,
      metricDerivNorm (I := I) q u u' gRef y :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  exact hloc.trans <| mul_le_mul_of_nonneg_right
    (hCαle.trans (le_add_of_nonneg_right zero_le_one)) hD0

end HCGCompactness
end DifferentialGeometry
