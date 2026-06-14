import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2

/-!
# `C^∞` spectral-series realization of the smooth-representative gate

This file carries the eigenfunction-series content that realizes the
smooth-representative gate `SpectralSmoothRealizesAsSmooth` (defined in
`SpectralSmoothing.lean`) on the intrinsic *smooth* eigenbasis
`eigenvectorSmooth g r s i`. Because these declarations are the only ones
that consume the chart-locality-free `eigenvectorSmooth_toL2` identity,
they are separated from `SpectralSmoothing.lean` so that the latter does
not import (and therefore does not leak the `TensorSpectral.TensorEigenIdx`
abbrev of) `EigenvectorSmoothToL2` into its downstream consumers.

## Main results

* `spectralSeries_hasSmoothSum_of_allOrders_summable` — the all-orders
  `Cᵏ`-completeness engine: a coordinate family with super-polynomial
  decay sums, on the smooth eigenbasis, to the `L²` class of a genuine
  `SmoothCcTensor` (a deferred classical analytic input, body `sorry`).
* `spectralSeries_smoothCcTensor_of_allOrders_summable` — the assembled
  form: concrete all-orders coefficient summability of an `L²` tensor `u`
  yields a `C^∞` representative `T` with `↑T = u`.
* `spectralSmoothRealizesAsSmooth_holds` — the gate predicate
  `SpectralSmoothRealizesAsSmooth` holds unconditionally, by extracting
  the concrete all-orders summability from the abstract `⋂_σ Hˢ`
  membership.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Smooth realization of an all-orders-decaying coordinate family
(deferred analytic input).**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family whose weighted
squares `(1 + λᵢ)^{2k} · cᵢ²` are summable for *every even order* `2k`.
Then `c` is the intrinsic eigenbasis coordinate family of a genuine
smooth, compactly-supported section `T : SmoothCcTensor g r s`:

  `∀ i, tensorL2Coeff h_compact (↑T) i = cᵢ`.

This is the precise `Cᵏ`-Banach-completeness content of the all-orders
spectral Sobolev embedding `⋂_σ Hˢ ⊆ C^∞`, isolated as the *one* deep
classical analytic input of the smooth-representative gate. Its proof is
term-by-term: the per-eigentensor `H^{2k}`-norm bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform`
(`wtwokTwoNorm g k (eigenvectorSmooth g r s i)
  ≤ ENNReal.ofReal (C · i.fst.valᐟ ^ (2k+1)) · ‖bᵢ‖`, polynomial growth
in the eigenvalue since `1 + λᵢ = i.fst.val⁻¹` by
`one_add_lambda_eq_inv_val`) is beaten by the hypothesised
super-polynomial coefficient decay; this makes the partial sums
`∑_{i ∈ finset} cᵢ · eigenvectorSmooth g r s i` Cauchy in the `Cᵏ`
(iterated-covariant-derivative) Banach norm for each `k`, via the
unconditional `C^m` tensor Sobolev embedding
`iteratedCovGrad_toSobolev_embedding_Cm_unconditional`. The common `C^∞`
limit of those `Cᵏ`-Cauchy partial sums is the desired `SmoothCcTensor`,
and its `L²` class is the eigenbasis sum, so its `i`-th eigenbasis
coordinate is `cᵢ`.

This is a **deferred input**: its body is `sorry`, and every consumer
transitively depends on `sorryAx`. It is phrased on the prescribed
coordinate family `c` (rather than on a pre-built `L²` element) so that
the entire `L²`-side identification — building the eigenbasis sum and
pinning the stated `HasSum` against the `L²`-embedded smooth eigenbasis —
is *proved* structurally in `spectralSeries_hasSmoothSum_of_allOrders_summable`
on top of this single analytic core. The hypothesis is genuinely
load-bearing: dropping `h_decay` makes the statement false (a generic
`ℓ²`-but-not-smooth coordinate family has no smooth representative). -/
theorem smoothCcTensor_exists_of_allOrders_decay
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) * (c i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      ∀ i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (T : TensorL2 r s g) i = c i :=
  sorry

/-- **Smooth-series convergence engine.**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family whose weighted
squares `(1 + λᵢ)^{2k} · cᵢ²` are summable for *every even order* `2k`.
Then the intrinsic eigenfunction series
`∑ᵢ cᵢ · eigenvectorSmooth g r s i` (each summand a smooth, compactly
supported eigentensor) sums, in `L²`, to a genuine smooth,
compactly-supported section `T : SmoothCcTensor g r s`:

  `HasSum (fun i => cᵢ • (eigenvectorSmooth g r s i : L²)) (↑T)`.

The smooth section `T` is produced by the deferred analytic core
`smoothCcTensor_exists_of_allOrders_decay`, whose `i`-th eigenbasis
coordinate is exactly `cᵢ`. The `HasSum` is then the resolvent
eigenbasis expansion of `↑T`: the `HilbertBasis.hasSum_repr` of `↑T`
against `tensorResolventHilbertEigenbasisSigma` is the series
`∑ᵢ (b.repr (↑T) i) • bᵢ = ∑ᵢ cᵢ • bᵢ`, and each basis vector
`bᵢ = (eigenvectorSmooth g r s i : L²)` by `eigenvectorSmooth_toL2`. -/
theorem spectralSeries_hasSmoothSum_of_allOrders_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) * (c i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s,
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        (T : TensorL2 r s g) := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set bsis := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact
    with hbsis_def
  obtain ⟨T, hT_coeff⟩ :=
    smoothCcTensor_exists_of_allOrders_decay (I := I) (M := M) g r s c h_decay
  refine ⟨T, ?_⟩
  have hHasSum : HasSum (fun i => bsis.repr (T : TensorL2 r s g) i • bsis i)
      (T : TensorL2 r s g) := bsis.hasSum_repr (T : TensorL2 r s g)
  refine hHasSum.congr_fun (fun i => ?_)
  have hbi : bsis i =
      (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
    rw [hbsis_def, tensorResolventHilbertEigenbasisSigma_apply,
      eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
  have hci : bsis.repr (T : TensorL2 r s g) i = c i := by
    have hcoe : bsis.repr (T : TensorL2 r s g) i =
        tensorL2Coeff (I := I) (M := M) h_compact (T : TensorL2 r s g) i := rfl
    rw [hcoe, hT_coeff i]
  rw [hbi, hci]

/-- **Classical `C^∞` spectral-series assembly (deferred analytic input).**

Let `u : TensorL2 r s g` be an `L²` tensor field whose intrinsic
eigenbasis coordinates `cᵢ = tensorL2Coeff h_compact u i` decay so fast
that, for *every even order* `2k`, the weighted squares
`(1 + λᵢ)^{2k} · cᵢ²` are summable. Then the eigenfunction series
`∑ᵢ cᵢ · eigenvectorSmooth g r s i` converges in `Cᵏ` for every `k`, and
its limit is a genuine smooth, compactly-supported section
`T : SmoothCcTensor g r s` whose `L²` class is `u`.

This is the **all-orders spectral Sobolev embedding** in its assembled
form: the per-eigentensor `H^{2k}`-norm bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform`
(`wtwokTwoNorm g k (eigenvectorSmooth g r s i)
  ≤ ENNReal.ofReal (C · i.fst.valᐟ ^ (2k+1)) · ‖bᵢ‖`, polynomial growth
in the eigenvalue, since `1 + λᵢ = i.fst.val⁻¹`) is beaten by the
hypothesised super-polynomial coefficient decay; term-by-term this makes
the partial sums Cauchy in the `Cᵏ` (iterated-covariant-derivative)
Banach norm for each `k`, and the unconditional `C^m` tensor Sobolev
embedding `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`
(`Embedding/SobolevEmbeddingCmOrderDropping.lean`) converts the
`H^{2k}`-Cauchy partial sums into a `Cᵏ`-Cauchy family of smooth
sections, whose common `C^∞` limit is the desired `SmoothCcTensor`. The
`L²` limit of the same partial sums is `u` by completeness of the
eigenbasis expansion, pinning `↑T = u`.

This lemma is the precise remaining classical analytic content of the
smooth-representative gate. It is a **deferred input**: its body is
`sorry`, and every consumer transitively depends on `sorryAx`. Its
hypothesis is the *concrete* all-orders coefficient summability of `u`
(strictly weaker, and strictly more elementary, than the abstract
`⋂_σ Hˢ`-membership hypothesis of the gate predicate, from which it is
derived in `spectralSmoothRealizesAsSmooth_holds`). -/
theorem spectralSeries_smoothCcTensor_of_allOrders_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_decay : ∀ k : ℕ,
      Summable (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            u i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  -- The deep `Cᵏ`-completeness engine: the eigenfunction series with the
  -- coefficient family `cᵢ = tensorL2Coeff h_compact u i` converges to the
  -- `L²` class of a smooth section `T`.
  obtain ⟨T, hT⟩ :=
    spectralSeries_hasSmoothSum_of_allOrders_summable
      (I := I) (M := M) g r s
      (fun i => tensorL2Coeff (I := I) (M := M) h_compact u i) h_decay
  refine ⟨T, ?_⟩
  -- The resolvent eigenbasis representation of `u` is the *same* series:
  -- `bᵢ = (eigenvectorSmooth g r s i : L²)` and `b.repr u i = tensorL2Coeff u i`.
  have h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorL2Coeff (I := I) (M := M) h_compact u i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g)) u := by
    have hbasis :=
      (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact).hasSum_repr u
    refine hbasis.congr_fun (fun i => ?_)
    have hb :
        (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact) i =
          (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
      rw [tensorResolventHilbertEigenbasisSigma_apply
        (I := I) (M := M) h_compact i,
        eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
    rw [hb]
    rfl
  exact hT.unique h_repr

/-- **The smooth-representative gate (proved).**

`SpectralSmoothRealizesAsSmooth g r s` holds unconditionally: every `L²`
tensor `u` lying (via the chart-locality-free inclusion `tensorHsToL2`)
in `Hˢ` for *every* exponent `σ ≥ 0` admits a genuine `C^∞`
representative `T : SmoothCcTensor g r s` with `↑T = u`.

The proof extracts, from the abstract `⋂_σ Hˢ`-membership hypothesis, the
*concrete* all-orders coefficient summability of `u`: at each even order
`2k`, the gate hypothesis provides an `Hˢ` witness `v` with
`tensorHsToL2 h_compact v = u`; its structural square-summability
`tensorHs.weighted_summable` together with the coordinate-faithfulness
`tensorHsToL2_tensorL2Coeff` (which identifies `v.coeff i` with the
intrinsic eigenbasis coordinate `tensorL2Coeff h_compact u i`) yields the
weighted summability of `(1 + λᵢ)^{2k} · cᵢ²`. The deferred classical
`C^∞` spectral-series assembly
`spectralSeries_smoothCcTensor_of_allOrders_summable` then converts that
super-polynomial coefficient decay into the smooth section. -/
theorem spectralSmoothRealizesAsSmooth_holds
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s := by
  intro u hu
  refine spectralSeries_smoothCcTensor_of_allOrders_summable
    (I := I) (M := M) g r s u (fun k => ?_)
  have h2k : (0 : ℝ) ≤ (2 * k : ℝ) := by positivity
  obtain ⟨v, hv⟩ := hu (2 * k : ℝ) h2k
  have hcoeff : ∀ i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u i = v.coeff i := by
    intro i
    have h := tensorHsToL2_tensorL2Coeff
      (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s) h2k v i
    rw [hv] at h
    exact h
  have hsummable := v.weighted_summable
  refine hsummable.congr (fun i => ?_)
  rw [hcoeff i]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
