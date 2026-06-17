import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

/-!
# Weyl summability of negative Sobolev-scale weights

For a closed Riemannian manifold `(M, g)` of dimension `n = finrank E`, the
connection-Laplacian eigenvalues `λᵢ ≥ 0` attached to the resolvent eigenbasis of
`(0, 2)`-tensor fields satisfy the classical Weyl summability

  `∑ᵢ (1 + λᵢ)^{-s} < ∞`  for every `s > n / 2`.

This is the eigenvalue-counting / trace-class consequence of Weyl's law
`N(Λ) := #{i | 1 + λᵢ < Λ} ≲ Λ^{n/2}`, equivalently the polynomial eigenvalue
growth `1 + λ_k ≳ k^{2/n}` along the non-decreasing enumeration of the spectrum.

## Main result

* `tensorEigen_summable_negpow` — `Summable (fun i => tensorSobolevWeight i (-s))`
  for `s > n / 2`, i.e. `∑ᵢ (1 + λᵢ)^{-s} < ∞`.

## Structure

The deep classical content — the quantitative Weyl eigenvalue lower bound — is
isolated in `tensorEigen_one_add_lambda_growth`: an injective rank-enumeration
`φ : TensorEigenIdx g 0 2 → ℕ` of the (countable, discrete) spectrum together with
the polynomial growth `C · (φ i + 1)^{2/n} ≤ 1 + λᵢ`. Given that bound, the
summability follows by comparison with the convergent `p`-series
`∑ₖ (k + 1)^{-2s/n}` (`2s/n > 1`) along the injection `φ`.

The growth bound `tensorEigen_one_add_lambda_growth` is the Weyl-law node; it is
the only `sorry` here and its proof is the eigenvalue-counting estimate
(min-max / Sobolev-embedding eigenvalue counting, or the heat-kernel /
Hilbert-Schmidt resolvent route).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The shifted real `p`-series `∑ₖ (k + 1)^{-p}` converges for `1 < p`. -/
private lemma summable_nat_add_one_rpow_neg (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-p)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp
  have hshift : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
    hbase.comp_injective (add_left_injective 1)
  refine hshift.congr (fun k => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  push_cast
  ring_nf

/-- **Weyl polynomial eigenvalue growth** for the connection-Laplacian spectrum on
`(0, 2)`-tensor fields. The (countable, spectrally-discrete) eigen-index set admits
an injective rank-enumeration `φ : TensorEigenIdx g 0 2 ↪ ℕ` along which the
eigenvalues grow at least polynomially:

  `C · (φ i + 1)^{2/n} ≤ 1 + λᵢ`  for some `C > 0`,  `n = finrank E`.

This is the quantitative form of Weyl's eigenvalue-counting law
`N(Λ) ≲ Λ^{n/2}` (equivalently `1 + λ_k ≳ k^{2/n}` along a non-decreasing
enumeration). Any positive growth exponent `ε > 0` in place of `2/n` would
suffice for the consumers below; the sharp Weyl exponent `2/n` is recorded here.

The proof is the classical eigenvalue-counting estimate: order the spectrum by
the finite sub-level sets `{i | 1 + λᵢ < Λ}` (`tensorEigenIdx_one_add_lambda_lt_finite`)
and bound the counting function `N(Λ)` via the min-max / Courant–Fischer principle
against the Sobolev embedding constant (equivalently, the Hilbert–Schmidt /
heat-kernel on-diagonal bound for the resolvent power). It is the only deferred
node of this file. -/
theorem tensorEigen_one_add_lambda_growth (g : SmoothRiemannianMetric I M) :
    ∃ (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℕ) (C : ℝ),
      Function.Injective φ ∧ 0 < C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
          C * ((φ i : ℝ) + 1) ^ (2 / (Module.finrank ℝ E : ℝ)) ≤
            1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
  sorry

/-- **Weyl summability of negative Sobolev-scale weights.** For `s > n / 2`
(`n = finrank E`), the negative Sobolev weights are summable:

  `∑ᵢ (1 + λᵢ)^{-s} = ∑ᵢ tensorSobolevWeight i (-s) < ∞`.

This is the trace-class / eigenvalue-summability consequence of Weyl's law. The
proof compares `(1 + λᵢ)^{-s}` against the convergent `p`-series
`∑ₖ (k + 1)^{-2s/n}` (with `2s/n > 1`) along the polynomial eigenvalue growth
`tensorEigen_one_add_lambda_growth`. -/
theorem tensorEigen_summable_negpow (g : SmoothRiemannianMetric I M) (s : ℝ)
    (hs : (Module.finrank ℝ E : ℝ) / 2 < s) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-s)) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn : 0 < n := by
    have hne := NeZero.ne (Module.finrank ℝ E)
    rw [hn_def]; positivity
  obtain ⟨φ, C, hφ, hC, hgrowth⟩ :=
    tensorEigen_one_add_lambda_growth (I := I) (M := M) g
  have hlam : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    fun i => tensor_lambda_nonneg (I := I) (M := M) i
  have h1add : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    fun i => by linarith [hlam i]
  have hbasepos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < C * ((φ i : ℝ) + 1) ^ (2 / n) := fun i => by
    have : (0 : ℝ) < ((φ i : ℝ) + 1) ^ (2 / n) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  set gnat : ℕ → ℝ := fun k => (C * ((k : ℝ) + 1) ^ (2 / n)) ^ (-s) with hgnat
  set f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => (C * ((φ i : ℝ) + 1) ^ (2 / n)) ^ (-s) with hf
  have hfcomp : f = gnat ∘ φ := by
    funext i; simp [hf, hgnat, Function.comp]
  have hgnat_summable : Summable gnat := by
    have hrw : gnat = fun k : ℕ => C ^ (-s) * (((k : ℝ) + 1) ^ (-(2 * s / n))) := by
      funext k
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      change (C * ((k : ℝ) + 1) ^ (2 / n)) ^ (-s) = _
      rw [Real.mul_rpow hC.le (Real.rpow_pos_of_pos hkpos _).le,
        ← Real.rpow_mul hkpos.le]
      congr 2
      rw [div_mul_eq_mul_div]; ring
    rw [hrw]
    apply Summable.mul_left
    have hexp : 1 < 2 * s / n := by rw [lt_div_iff₀ hn]; linarith
    exact summable_nat_add_one_rpow_neg (2 * s / n) hexp
  have hfsummable : Summable f := by
    rw [hfcomp]; exact hgnat_summable.comp_injective hφ
  refine Summable.of_nonneg_of_le ?_ ?_ hfsummable
  · intro i
    refine Real.rpow_nonneg (by linarith [h1add i]) _
  · intro i
    change (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-s) ≤ f i
    rw [hf]
    exact Real.rpow_le_rpow_of_nonpos (hbasepos i) (hgrowth i) (by linarith : (-s) ≤ 0)

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
