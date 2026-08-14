import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualWindow

/-!
# Radius-free grid integrators

Chunk of the `CurvatureCoefficientDifferenceJetTower` tower, split
out of the former 15111-line monolith (no longer elaborable in a
single Lean process).  Every declaration is verbatim.  The former
`private` helpers were promoted into the internal `CurvatureCoefficientDifferenceJetTower`
scope, so the public `Connection` API is unchanged.  Chunk map:
`CurvatureCoefficientDifferenceJetTower.md`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopSeparatedResidualIntegrator

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false in
/-- Radius-free per-order antidiagonal grid integral bound.  With a FIXED
zeroth-order fibre bound `Λ₀` (from fibre smallness, not from a Sobolev ball
radius), the integral of the order-`i` antidiagonal product grid is controlled
by a constant `K i` — depending only on `g₀` and `Λ₀` — times `1 + ‖∇ⁱP‖²`,
keeping the top jet EXPLICIT.  Sibling of
`antidiagonalTupleGrid_integral_ballUniform_tameWindow`; the only differences are
the fixed `Λ₀` (so the constant is radius-free) and that the top jet is not
lumped back into a low window.

The base valence `(r, s)` is generic.  Nothing in the argument sees it: the
Gagliardo--Nirenberg input and the per-antidiagonal workhorse `grid_prod_int_le`
are both valence-generic.  `(0, 2)` is the state's own grid (the compatibility
instance `antidiagonalTupleGrid_integral_radiusFree` just below); `(0, 3)` is
the grid of `∇P`, whose order-zero cap is `‖∇P‖_∞` — the `Λ₁` currency the
quadratic C0 summands need. -/
theorem atgGridIntRs
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ r s)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                      ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                        ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ r s k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ r s k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Λ₀ (max (Cgn k) 1)) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_max_right Λ₀ _))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hK_nn : ∀ k, 0 ≤ (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol := by
    intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, hK_nn, ?_⟩
  intro P hsup i
  have hone_le : (1 : ℝ) ≤ 1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
    linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)]
  by_cases hi0 : i = 0
  · subst hi0
    have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid0]; exact MeasureTheory.integrable_const 1
    · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol]
      calc vol ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) * 1 := by
            rw [mul_one]
            exact le_add_of_nonneg_left
              (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
        _ ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) *
            (1 + ‖iteratedCovGrad (I := I) g₀ r s 0 P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hone_le (hK_nn 0)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ r s i hi1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < i →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
                ((iteratedCovGrad (I := I) g₀ r s j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
          Cgn i * Λ₀ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
            ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
      intro j hj0 hji
      have hb := hGNspec P Λ₀ hΛ₀0 hsup j hj0 hji
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ r s i hi1).choose = Cgn i := by
        rw [hCgn]; simp only [dif_pos hi1]
      rw [hchoose] at hb
      have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i P).toFun = ‖iteratedCovGrad (I := I) g₀ r s i P‖ :=
        (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ r s i P)).symm
      rw [hnorm] at hb
      exact hb
    have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
        MeasureTheory.Integrable (fun x => ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
      intro n hn e he
      have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := grid_prod_int_le (I := I) (M := M) g₀ P
        (norm_nonneg (iteratedCovGrad (I := I) g₀ r s i P)) i hi1 hΛ₀0 hsup
        (le_refl _) (hCgn_nn i) hGNP n hn_le e hsum_e
      refine ⟨hres.1, ?_⟩
      refine le_trans hres.2 (le_of_eq ?_)
      simp only [hGfun]
    have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      apply MeasureTheory.integrable_finset_sum
      intro n hn
      apply MeasureTheory.integrable_finset_sum
      intro e he
      exact (hPT n hn e he).1
    refine ⟨hgrid_int, ?_⟩
    rw [MeasureTheory.integral_finset_sum _
      (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (i + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      intro n hn
      exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro e he
      exact (hPT n hn e he).2
    have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 =
        (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
          (Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hle1 ?_
    rw [heq2]
    have hcard_nn : 0 ≤ ∑ n ∈ Finset.range (i + 1),
        ((Finset.Nat.antidiagonalTuple n i).card : ℝ) :=
      Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
    calc (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2)
        = ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by ring
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcard_nn (hGfun_nn i))
          linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)]
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i + vol) * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_
            (by linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)])
          linarith

set_option linter.unusedVariables false in
/-- **Compatibility instance at the state's own valence `(0, 2)`.**  This is the
statement every existing radius-free per-order producer consumes; the content is
`atgGridIntRs` at `(r, s) = (0, 2)`. -/
theorem antidiagonalTupleGrid_integral_radiusFree
    (g₀ : SmoothRiemannianMetric I M) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) :=
  atgGridIntRs (I := I) (M := M) g₀ 0 2 hΛ₀0

set_option linter.unusedVariables false in
/-- THE GATE.  Radius-free, top-separated integrator for `boundedFactorGridWindow`.
With a fixed zeroth-order fibre bound `Λ₀`, the window integral splits into a LOW
part `Klow i · (1 + ∑_{j≤i+1}‖∇ʲP‖²)` and an EXPLICIT top leak
`Ktop i · ‖∇^{i+2}P‖²`, with `Klow`, `Ktop` depending only on `g₀` and `Λ₀`
(radius-free).  Sibling of
`boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders` with the
opposite constant choice: the top jet is carried as a separate leak instead of
hidden inside an `R`-dependent flat constant.

Base valence `(r, s)` generic, exactly as for `atgGridIntRs`; the compatibility
instance at `(0, 2)` is `boundedFactorGridWindow_integral_radiusFree_topSeparated`
just below. -/
theorem bfGridWinIntRs
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Klow : ℕ → ℝ, (∀ i, 0 ≤ Klow i) ∧ ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧
      ∀ (P : SmoothCcTensor g₀ r s)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
                  ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
                    ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Klow i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) +
                Ktop i * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := atgGridIntRs (I := I) (M := M) g₀ r s hΛ₀0
  refine ⟨fun i => ∑ k ∈ Finset.range (i + 3), Kt k,
    fun i => Finset.sum_nonneg (fun k _ => hKt_nn k),
    fun i => Kt (i + 2), fun i => hKt_nn (i + 2), ?_⟩
  intro P hsup i
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
    ((iteratedCovGrad (I := I) g₀ r s l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r (s + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ r s l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ r s l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ r s l P) x]
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun k _ => ?_)
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  have hint_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k => (hKt P hsup k).1
  have hint2_k : ∀ k : ℕ,
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) :=
    fun k => (hKt P hsup k).2
  have hmaj_int : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integrable_finset_sum _ (fun k _ => hint_k k)
  have hmono : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) ≤
        ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k := by
    intro x
    rw [Combinatorics.boundedFactorGridWindow]
    exact Finset.sum_le_sum (fun k _ =>
      Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid (b x) (hb x) (i + 1) k)
  refine le_trans (MeasureTheory.integral_mono hint hmaj_int hmono) ?_
  rw [MeasureTheory.integral_finset_sum _ (fun k _ => hint_k k)]
  have hstep1 : (∑ k ∈ Finset.range (i + 3),
        ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (i + 3), Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) :=
    Finset.sum_le_sum (fun k _ => hint2_k k)
  refine le_trans hstep1 ?_
  -- beta-reduce the `Klow i` / `Ktop i` redexes so `linarith` sees plain atoms.
  show (∑ k ∈ Finset.range (i + 3),
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)) ≤
      (∑ k ∈ Finset.range (i + 3), Kt k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) +
        Kt (i + 2) * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2
  -- Algebra: distribute, peel the top layer k = i+2, and route low layers to the window.
  have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hLHS : (∑ k ∈ Finset.range (i + 3),
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)) =
      (∑ k ∈ Finset.range (i + 3), Kt k) +
        ∑ k ∈ Finset.range (i + 3),
          Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hLHS]
  have hjsplit : (∑ k ∈ Finset.range (i + 3),
        Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) =
      (∑ k ∈ Finset.range (i + 2),
          Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) +
        Kt (i + 2) * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2 := by
    rw [show i + 3 = (i + 2) + 1 from rfl, Finset.sum_range_succ]
  rw [hjsplit]
  have hlow : (∑ k ∈ Finset.range (i + 2),
        Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) ≤
      (∑ k ∈ Finset.range (i + 3), Kt k) *
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
    calc (∑ k ∈ Finset.range (i + 2),
            Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)
        ≤ ∑ k ∈ Finset.range (i + 2),
            Kt k * ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          apply Finset.sum_le_sum; intro k hk
          refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
          exact Finset.single_le_sum
            (f := fun j => ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2)
            (fun j _ => sq_nonneg _) hk
      _ = (∑ k ∈ Finset.range (i + 2), Kt k) *
            ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ (∑ k ∈ Finset.range (i + 3), Kt k) *
            ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hS_nn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hKt_nn k)
          intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
  have hexp : (∑ k ∈ Finset.range (i + 3), Kt k) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) =
      (∑ k ∈ Finset.range (i + 3), Kt k) +
        (∑ k ∈ Finset.range (i + 3), Kt k) *
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
    ring
  linarith [hlow, hexp]

set_option linter.unusedVariables false in
/-- **Compatibility instance at the state's own valence `(0, 2)`.**  Content is
`bfGridWinIntRs` at `(r, s) = (0, 2)`. -/
theorem boundedFactorGridWindow_integral_radiusFree_topSeparated
    (g₀ : SmoothRiemannianMetric I M) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Klow : ℕ → ℝ, (∀ i, 0 ≤ Klow i) ∧ ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Klow i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Ktop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
  bfGridWinIntRs (I := I) (M := M) g₀ 0 2 hΛ₀0

end TopSeparatedResidualIntegrator

end Connection
end Integral
end DifferentialGeometry

end
