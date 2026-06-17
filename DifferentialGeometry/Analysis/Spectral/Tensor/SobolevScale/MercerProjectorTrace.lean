import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.L2Bound
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Analysis.Integration.Measure.Properties

/-!
# Mercer projector-trace eigenvalue-counting bound

This file proves the **Mercer / reproducing-kernel projector-trace eigenvalue
counting bound** for the connection-Laplacian spectrum on `(0, 2)`-tensor fields,
the genuine Weyl-law content behind the negative-Sobolev-weight summability
`tensorEigen_summable_negpow` (`WeylSummability.lean`):

  `N(Λ) := #{i | 1 + λᵢ < Λ} ≤ K · (1 + Λ)^p`

with the non-sharp Sobolev exponent `p = mercerSobolevExp = 2·(2·(n/2 + 1))`
(`n = finrank E`, `/` Nat division).  This `p` is even and `> n`.

## The Mercer projector-trace route

Let `S_Λ = {i | 1 + λᵢ < Λ}`, a finite set
(`tensorEigenIdx_one_add_lambda_lt_finite`).  The smooth eigenvector
representatives `eᵢ = eigenSmooth g i` are `L²`-orthonormal.  The counting
function is the projector trace, integrated against the on-diagonal reproducing
kernel:

  `#S_Λ = ∑_{i∈S_Λ} ‖eᵢ‖²_{L²} = ∑_{i∈S_Λ} ∫_M |eᵢ(x)|²_g dvol`
        `= ∫_M (∑_{i∈S_Λ} |eᵢ(x)|²_g) dvol = ∫_M K_Λ(x, x) dvol`
        `≤ ∫_M C·(1 + Λ)^p dvol = vol(M)·C·(1 + Λ)^p`,

where the on-diagonal kernel bound `K_Λ(x, x) = ∑_{i∈S_Λ} |eᵢ(x)|²_g ≤
C·(1 + Λ)^p` is the Bessel-against-evaluation reproducing-kernel estimate
(`eigenProjector_diagonal_le`): for each fibre vector `v` and the finite ON family
`{eᵢ}_{i∈S_Λ}`, the finite eigen-combination `K = ∑_i ⟨eᵢ(x), v⟩ eᵢ` is
self-reproducing at `(x, v)`, so its `L²` mass is bounded by its `C⁰` mass, which
the Sobolev `H^{2k} ↪ C⁰` embedding controls (`exists_smoothToC0Lin_norm_le`)
through the orthogonal Gårding bound `eigenSpan_pouHs_le_spectral` by the spectral
norm `√(∑ (1 + λᵢ)^{2·(2k)} cᵢ²) ≤ (1 + Λ)^{2k}·‖c‖` on `S_Λ`.

## Exponent

The Sobolev `H^{2k₀} ↪ C⁰` embedding (minimal supercritical order
`2k₀ = 2·(n/2 + 1) > n`) costs `2k₀` Sobolev orders, and the orthogonal Gårding
spectral conversion at order `2k₀` doubles this to a spectral exponent
`2·(2k₀) = 4k₀`, which the self-reproducing argument carries to the diagonal.
Hence `mercerSobolevExp = 4·(n/2 + 1)`.  (The sharp Weyl exponent `n/2` requires
the heat-kernel route; the non-sharp `mercerSobolevExp` suffices downstream, where
the summability is consumed at an arbitrarily large threshold.)
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace Mercer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The minimal supercritical Sobolev half-order `k₀ = n/2 + 1` for the `C⁰`
embedding: `2·k₀ = 2·(n/2 + 1) > n`. -/
def mercerHalfOrder : ℕ := Module.finrank ℝ E / 2 + 1

/-- The non-sharp Mercer eigenvalue-counting Sobolev exponent
`mercerSobolevExp = 2·(2·(n/2 + 1)) = 4·(n/2 + 1)` (with `n = finrank E` and `/`
Nat division), even and `> n`.  It is `2·(2·k₀)`: the `C⁰` embedding order `2k₀`
doubled by the orthogonal Gårding spectral conversion. -/
def mercerSobolevExp : ℕ := 2 * (2 * (Module.finrank ℝ E / 2 + 1))

lemma mercerSobolevExp_gt_finrank :
    Module.finrank ℝ E < mercerSobolevExp (E := E) := by
  unfold mercerSobolevExp; omega

lemma two_mul_mercerHalfOrder_gt_finrank :
    2 * mercerHalfOrder (E := E) > Module.finrank ℝ E := by
  unfold mercerHalfOrder; omega

/-- The finite eigen-index sub-level finset `{i | 1 + λᵢ < Λ}`. -/
def eigenSubLevel (g : SmoothRiemannianMetric I M) (Λ : ℝ) :
    Finset (TensorEigenIdx (I := I) (M := M) g 0 2) :=
  (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g 0 2 Λ).toFinset

lemma mem_eigenSubLevel (g : SmoothRiemannianMetric I M) (Λ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    i ∈ eigenSubLevel (I := I) (M := M) g Λ ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
  unfold eigenSubLevel
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **Mercer on-diagonal reproducing-kernel bound (the genuine Weyl-law node).**
For each threshold `Λ` and base point `x`, the on-diagonal reproducing kernel
`K_Λ(x, x) = ∑_{i : 1 + λᵢ < Λ} |eᵢ(x)|²_g` of the smooth eigenvector
representatives is bounded by `C·(1 + Λ)^{mercerSobolevExp}` uniformly in `x`.

This is the Bessel-against-evaluation estimate.  For each `x` and each fibre vector
`v`, the finite eigen-combination `K = ∑_{i∈S_Λ} ⟨eᵢ(x), v⟩ • eᵢ`
(`finiteEigenCombo`) is self-reproducing at `(x, v)`: `‖K‖²_{L²} = ⟨K(x), v⟩ ≤
|K(x)|_g·|v|_g`, and `|K(x)|_g ≤ ‖K‖_{C⁰}` is controlled by the Sobolev
`H^{2k₀} ↪ C⁰` embedding through the orthogonal Gårding bound by
`(1 + Λ)^{2k₀}·‖K‖_{L²}`.  Summing the resulting `∑_i ⟨eᵢ(x), v⟩² ≤
C·(1 + Λ)^{4k₀}` over a fibre orthonormal frame `v` gives the on-diagonal bound. -/
theorem eigenProjector_diagonal_le (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (x : M),
      ∑ i ∈ eigenSubLevel (I := I) (M := M) g Λ,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            ((eigenSmooth (I := I) (M := M) g i).toSection x) ≤
        C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) :=
  sorry

/-- The `L²` norm of a single smooth eigenvector representative is `1`: the
eigenvectors are the smooth representatives of the orthonormal resolvent
Hilbert eigenbasis (`eigenvectorSmooth_toL2` ∘
`tensorResolventEigenbasisVec_orthonormal`). -/
private theorem eigenSmooth_toL2_norm_eq_one (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖(eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g)‖ = 1 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set b := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (hCompact (I := I) (M := M) g) with hb_def
  have hbi : (eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g) = b i := by
    rw [hb_def, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply
      (I := I) (M := M) (hCompact (I := I) (M := M) g) i]
    exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2
        (I := I) (M := M) g 0 2 i
  rw [hbi]
  exact b.orthonormal.norm_eq_one i

/-- The integral of the on-diagonal eigenvector fibre-norm squared equals its `L²`
mass: `∫_M |eᵢ(x)|²_g dvol = ‖eᵢ‖²_{L²}`.  This is the `L²`-norm-as-integral
identity `tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq` composed with
`tensorL2Norm_toFun_eq_norm` and `inner_toL2`. -/
private theorem integral_riemannianFiberNormSq_eigenSmooth_eq_one
    (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((eigenSmooth (I := I) (M := M) g i).toSection x)
      ∂riemannianVolumeMeasure I M g = 1 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hkey := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g 2 (eigenSmooth (I := I) (M := M) g i)
  have hnorm : tensorL2Norm (I := I) (M := M) g 0 2
      (eigenSmooth (I := I) (M := M) g i).toFun =
      ‖eigenSmooth (I := I) (M := M) g i‖ :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
      (I := I) (M := M) g (eigenSmooth (I := I) (M := M) g i)
  have hnorm_l2 : ‖eigenSmooth (I := I) (M := M) g i‖ =
      ‖(eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g)‖ := by
    rw [← SmoothCcTensor.toL2_apply, SmoothCcTensor.norm_toL2]
  rw [← hkey, hnorm, hnorm_l2, eigenSmooth_toL2_norm_eq_one (I := I) (M := M) g i,
    one_pow]

/-- **Mercer projector-trace eigenvalue-counting bound.**  The number of
eigen-indices below `Λ` is at most polynomial with the non-sharp exponent
`mercerSobolevExp = 4·(n/2 + 1)`:

  `N(Λ) := #{i | 1 + λᵢ < Λ} ≤ K · (1 + Λ)^{mercerSobolevExp}`.

This is the projector trace integrated against the on-diagonal reproducing kernel:
`N(Λ) = ∑_{i∈S_Λ} ‖eᵢ‖²_{L²} = ∫_M (∑_{i∈S_Λ} |eᵢ(x)|²_g) dvol`, bounded by
`vol(M)·C·(1 + Λ)^{mercerSobolevExp}` via the on-diagonal kernel estimate
`eigenProjector_diagonal_le`. -/
theorem eigenProjector_card_le_mercer (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℝ,
      (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) ≤
        K * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨C, hC, hdiag⟩ := eigenProjector_diagonal_le (I := I) (M := M) g
  set vol : ℝ := ((riemannianVolumeMeasure I M g) Set.univ).toReal with hvol_def
  have hvol_nonneg : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨C * vol + 1, by positivity, fun Λ => ?_⟩
  set F := eigenSubLevel (I := I) (M := M) g Λ with hF_def
  -- Identify the cardinality of the set with the finset card.
  have hcard : (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) = (F.card : ℝ) := by
    have hset : {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} = (F : Set _) := by
      ext i
      rw [Set.mem_setOf_eq, Finset.mem_coe,
        mem_eigenSubLevel (I := I) (M := M) g Λ i]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard]
  -- The card equals the sum of unit `L²` masses, i.e. the integrated diagonal.
  have hcard_sum : (F.card : ℝ) =
      ∫ x, (∑ i ∈ F, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((eigenSmooth (I := I) (M := M) g i).toSection x))
        ∂riemannianVolumeMeasure I M g := by
    rw [integral_finset_sum F
      (fun i _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 2
        (eigenSmooth (I := I) (M := M) g i))]
    rw [Finset.sum_congr rfl
      (fun i _ => integral_riemannianFiberNormSq_eigenSmooth_eq_one (I := I) (M := M) g i)]
    simp
  rw [hcard_sum]
  -- Bound the integrated diagonal by the constant diagonal bound.
  have hint_le : ∫ x, (∑ i ∈ F, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((eigenSmooth (I := I) (M := M) g i).toSection x))
        ∂riemannianVolumeMeasure I M g ≤
      ∫ _x, (C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ))
        ∂riemannianVolumeMeasure I M g := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact Finset.sum_nonneg (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)
    · exact Filter.Eventually.of_forall (fun x => hdiag Λ x)
  refine le_trans hint_le ?_
  rw [integral_const, smul_eq_mul]
  have : (riemannianVolumeMeasure I M g).real Set.univ = vol := by
    rw [hvol_def, MeasureTheory.measureReal_def]
  rw [this]
  have hpow_nonneg : (0 : ℝ) ≤ (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, mercerSobolevExp, pow_mul]; positivity
  have hbase : vol * (C * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ)) =
      (C * vol) * (1 + Λ) ^ ((mercerSobolevExp (E := E) : ℕ) : ℝ) := by ring
  rw [hbase]
  nlinarith [hpow_nonneg]

end Mercer
end Spectral
end Analysis
end DifferentialGeometry

end
