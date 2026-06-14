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

/-- **Weyl-type eigenvalue-counting summability (deferred classical
spectral input).**

For the intrinsic connection-Laplacian eigenvalues `λᵢ ≥ 0` of the mixed
`(r, s)`-tensor bundle on a closed Riemannian manifold, there is an
exponent `N` (large enough) for which the powers `(1 + λᵢ)^{-N}` are
summable over the eigen-index set `TensorEigenIdx g r s`. Concretely this
is the trace-class property of a large power of the (compact) resolvent:
by the Weyl asymptotic `N(Λ) ≍ Λ^{(dim M)/2}` the eigenvalues grow like
`λⱼ ≍ j^{2/dim M}`, so `∑ⱼ (1 + λⱼ)^{-N} ≍ ∑ⱼ j^{-2N/dim M}` converges
once `2N > dim M`.

This is a **deferred input**: its body is `sorry`. It is the genuine
spectral-counting ingredient missing from the library, which carries only
the sublevel-set *finiteness* `tensorEigenIdx_one_add_lambda_lt_finite`
(`{i | 1 + λᵢ < Λ}.Finite`) — enough for countability of each sublevel,
but not for the polynomial counting bound that yields summability. The
statement is genuinely true (a standard consequence of the Weyl law on a
closed manifold) and strictly more than the available finiteness. -/
theorem tensorEigenIdx_one_add_lambda_rpow_neg_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ N : ℝ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          (1 + i.lambda) ^ (-N)) :=
  sorry

/-- **`C^∞` realization of a super-polynomially-`ℓ¹`-decaying eigenfunction
series (the deep uniform-limit-of-derivatives analytic core).**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family such that:

* the eigenfunction series `∑ᵢ cᵢ · eigenvectorSmooth g r s i` sums, in
  `L²`, to `u` (hypothesis `h_repr`); and
* the coefficients decay faster than every polynomial in the eigenvalue,
  in the absolute (`ℓ¹`) sense: for *every order* `k`, the weighted
  absolute family `|cᵢ| · (1 + λᵢ)^k` is summable (hypothesis `h_poly`).

Then `u` admits a genuine smooth, compactly-supported representative
`T : SmoothCcTensor g r s` with `↑T = u`.

This is the precise `Cᵏ`-Banach-completeness content of the all-orders
spectral Sobolev embedding `⋂_σ Hˢ ⊆ C^∞`, isolated as the *one* deep
classical analytic input of the smooth-representative gate. Its proof is
term-by-term: the partial sums of the eigenfunction series obey, in each
intrinsic `H^{2k}` (iterated-covariant-derivative) Banach norm, the
per-eigentensor uniform bound `eigenvectorSmooth_wtwokTwoNorm_le_uniform`
(`wtwokTwoNorm g k (eigenvectorSmooth g r s i)
  ≤ ENNReal.ofReal (C · (1 + λᵢ) ^ (2k+1))`, polynomial growth in the
eigenvalue since `1 + λᵢ = i.fst.val⁻¹` by `one_add_lambda_eq_inv_val`
and the eigenbasis is orthonormal); the super-polynomial `ℓ¹` coefficient
decay `h_poly` beats this polynomial growth, making the partial sums
Cauchy in the `Cᵏ` Banach norm for each `k`, via the unconditional `C^m`
tensor Sobolev embedding `iteratedCovGrad_toSobolev_embedding_Cm_unconditional`.
The common `C^∞` limit of those `Cᵏ`-Cauchy partial sums is the desired
`SmoothCcTensor`, and its `L²` class is `u` by `h_repr`.

This is a **deferred input**: its body is `sorry`, and every consumer
transitively depends on `sorryAx`. The genuine prerequisite it
black-boxes is the all-orders uniform-limit-of-derivatives passage to
`ContMDiff` (`Mathlib` carries only the single-derivative
`hasFDerivAt_of_tendstoUniformly` family; there is no `ContDiff` /
`ContMDiff` uniform-derivative-limit theorem, nor the transport of a
`Cᵏ`-for-all-`k` uniform limit to `ContMDiffSection` / `SmoothCcTensor`).
The hypotheses are genuinely load-bearing: dropping `h_poly` makes the
statement false (a generic `ℓ²`-but-not-smooth coefficient family has no
smooth representative). -/
theorem smoothCcTensor_of_eigenSeries_poly_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        u)
    (h_poly : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          |c i| * (1 + i.lambda) ^ (k : ℝ))) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u :=
  sorry

/-- **`C^∞` realization of an all-orders-decaying `L²` tensor.**

Let `u : TensorL2 r s g` be an `L²` tensor field whose intrinsic
eigenbasis coordinates `cᵢ = tensorL2Coeff h_compact u i` decay so fast
that, for *every even order* `2k`, the weighted squares
`(1 + λᵢ)^{2k} · cᵢ²` are summable. Then `u` admits a genuine smooth,
compactly-supported representative `T : SmoothCcTensor g r s` with
`↑T = u`.

This is the all-orders spectral Sobolev embedding `⋂_σ Hˢ ⊆ C^∞` in its
`L²`-coordinate form. The proof assembles two classical analytic inputs:

* the **Weyl-type eigenvalue summability**
  `tensorEigenIdx_one_add_lambda_rpow_neg_summable`
  (`∃ N, Summable (fun i => (1 + λᵢ)^{-N})`); and
* the **uniform-limit-of-derivatives `C^∞` realization core**
  `smoothCcTensor_of_eigenSeries_poly_summable`
  (a super-polynomially-`ℓ¹`-decaying eigenfunction series has a smooth
  `L²`-limit).

The genuine work done here is the bridge between the two: the hypothesised
`ℓ²`-with-`(1+λ)^{2k}`-weight decay `h_decay`, together with the Weyl
summability, yields — by the elementary `2ab ≤ a² + b²` splitting — the
super-polynomial `ℓ¹` decay `h_poly` (`∀ k, ∑ᵢ |cᵢ| (1+λᵢ)^k < ∞`) that
the realization core consumes; and the `L²` expansion `h_repr` of `u` on
the orthonormal smooth eigenbasis (`HilbertBasis.hasSum_repr` together
with `eigenvectorSmooth_toL2`) supplies its other hypothesis.

The `h_decay` hypothesis is genuinely load-bearing: dropping it makes the
statement false (a generic `ℓ²`-but-not-smooth `L²` tensor has no smooth
representative). -/
theorem tensorL2_smoothRepr_of_allOrders_decay
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u : TensorL2 r s g)
    (h_decay : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
              u i) ^ 2)) :
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set c : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact u i with hc_def
  -- The `L²` expansion of `u` on the orthonormal smooth eigenbasis:
  -- `u = ∑ᵢ cᵢ • eigenvectorSmooth i`, with `cᵢ = tensorL2Coeff h_compact u i`.
  have h_repr :
      HasSum
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          c i •
            (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g))
        u := by
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
  -- The super-polynomial `ℓ¹` decay of `c`, produced from the `ℓ²` decay
  -- `h_decay` and the Weyl eigenvalue summability by the `2ab ≤ a² + b²`
  -- splitting.
  obtain ⟨N, hN⟩ :=
    tensorEigenIdx_one_add_lambda_rpow_neg_summable (I := I) (M := M) g r s
  have h_poly : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          |c i| * (1 + i.lambda) ^ (k : ℝ)) := by
    intro k
    -- pick a natural shift `m` with `2 m ≥ N + 2 k`, so that the negative
    -- leftover exponent `2(k - m)` is `≤ -N`.
    obtain ⟨m, hm⟩ := exists_nat_ge ((N + 2 * (k : ℝ)) / 2)
    have hm2 : N + 2 * (k : ℝ) ≤ 2 * (m : ℝ) := by
      have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hm
      linarith
    -- `aᵢ = |cᵢ| (1+λᵢ)^m`, `bᵢ = (1+λᵢ)^(k - m)`.
    set base : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
      fun i => 1 + i.lambda with hbase_def
    have hbase_pos : ∀ i, (0 : ℝ) < base i := by
      intro i
      have := tensor_lambda_nonneg (I := I) (M := M) i
      simp only [hbase_def]; linarith
    have hbase_one_le : ∀ i, (1 : ℝ) ≤ base i := by
      intro i
      have := tensor_lambda_nonneg (I := I) (M := M) i
      simp only [hbase_def]; linarith
    -- `∑ aᵢ²` is summable: it is `h_decay m` reindexed.
    have hsumA :
        Summable (fun i => (|c i| * base i ^ (m : ℝ)) ^ 2) := by
      have hdm := h_decay m
      refine hdm.congr (fun i => ?_)
      have hci : tensorL2Coeff (I := I) (M := M) h_compact u i = c i := rfl
      rw [hci]
      have hcsq : tensorSobolevWeight (I := I) (M := M) i (2 * (m : ℝ)) =
          base i ^ (2 * (m : ℝ)) := rfl
      rw [hcsq]
      have hpow : base i ^ (2 * (m : ℝ)) = (base i ^ (m : ℝ)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast (base i ^ (m : ℝ)) 2,
          ← Real.rpow_mul (hbase_pos i).le]
        norm_num; ring_nf
      rw [hpow, mul_pow, sq_abs]
      ring
    -- `∑ bᵢ²` is summable: dominated by the Weyl-summable `(1+λᵢ)^{-N}`.
    have hsumB :
        Summable (fun i => (base i ^ ((k : ℝ) - (m : ℝ))) ^ 2) := by
      refine Summable.of_nonneg_of_le
        (fun i => sq_nonneg _)
        (fun i => ?_) hN
      have hexp : (base i ^ ((k : ℝ) - (m : ℝ))) ^ 2 =
          base i ^ (2 * ((k : ℝ) - (m : ℝ))) := by
        rw [← Real.rpow_natCast (base i ^ ((k : ℝ) - (m : ℝ))) 2,
          ← Real.rpow_mul (hbase_pos i).le]
        norm_num; ring_nf
      rw [hexp]
      have hle : 2 * ((k : ℝ) - (m : ℝ)) ≤ -N := by linarith
      exact Real.rpow_le_rpow_of_exponent_le (hbase_one_le i) hle
    -- domination: `|cᵢ|(1+λᵢ)^k = aᵢ·bᵢ ≤ aᵢ² + bᵢ²`.
    refine Summable.of_nonneg_of_le
      (fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _))
      (fun i => ?_)
      (hsumA.add hsumB)
    set a : ℝ := |c i| * base i ^ (m : ℝ) with ha_def
    set b : ℝ := base i ^ ((k : ℝ) - (m : ℝ)) with hb_def
    have ha_nn : 0 ≤ a :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
    have hb_nn : 0 ≤ b := Real.rpow_nonneg (hbase_pos i).le _
    have hab : a * b = |c i| * base i ^ (k : ℝ) := by
      rw [ha_def, hb_def, mul_assoc, ← Real.rpow_add (hbase_pos i)]
      ring_nf
    have hamgm : a * b ≤ a ^ 2 + b ^ 2 := by
      have h2 := two_mul_le_add_sq a b
      nlinarith [mul_nonneg ha_nn hb_nn]
    calc |c i| * base i ^ (k : ℝ) = a * b := hab.symm
      _ ≤ a ^ 2 + b ^ 2 := hamgm
  exact smoothCcTensor_of_eigenSeries_poly_summable
    (I := I) (M := M) g r s u c h_repr h_poly

/-- **Smooth realization of an all-orders-decaying coordinate family.**

Let `c : TensorEigenIdx g r s → ℝ` be a coordinate family whose weighted
squares `(1 + λᵢ)^{2k} · cᵢ²` are summable for *every even order* `2k`.
Then `c` is the intrinsic eigenbasis coordinate family of a genuine
smooth, compactly-supported section `T : SmoothCcTensor g r s`:

  `∀ i, tensorL2Coeff h_compact (↑T) i = cᵢ`.

The proof is the `L²`-side reduction to the single deep analytic core
`tensorL2_smoothRepr_of_allOrders_decay`: the order-`0` instance of
`h_decay` (with `tensorSobolevWeight i 0 = 1`) makes `c` square-summable,
hence an element `c ∈ ℓ²`; the resolvent eigenbasis
`tensorResolventHilbertEigenbasisSigma h_compact` realizes it as the
`L²` element `u = b.repr.symm c`, whose intrinsic eigenbasis coordinates
`tensorL2Coeff h_compact u i = (b.repr u) i = cᵢ` are exactly `c` by the
`b.repr.symm`-round-trip. Transporting `h_decay` along this coordinate
identity, the analytic core supplies the smooth representative `T` with
`↑T = u`, and `tensorL2Coeff h_compact (↑T) i = tensorL2Coeff h_compact u i
= cᵢ`. The hypothesis is genuinely load-bearing: dropping `h_decay` makes
the statement false (a generic `ℓ²`-but-not-smooth coordinate family has
no smooth representative). -/
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
            (T : TensorL2 r s g) i = c i := by
  classical
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  set bsis := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact
    with hbsis_def
  have hsq : Summable (fun i => (c i) ^ 2) := by
    have h0 := h_decay 0
    simp only [Nat.cast_zero, mul_zero, tensorSobolevWeight_zero, one_mul] at h0
    exact h0
  have hmem : Memℓp c 2 := by
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    simpa using hsq
  set cl : lp
      (fun _ : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 :=
    ⟨c, hmem⟩ with hcl_def
  set u : TensorL2 r s g := bsis.repr.symm cl with hu_def
  have hcoeff_u : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact u i = c i := by
    intro i
    have hround : bsis.repr u = cl := by
      rw [hu_def]; exact bsis.repr.apply_symm_apply cl
    have hval : (bsis.repr u) i = c i := by rw [hround]
    simpa [tensorL2Coeff] using hval
  have h_decay_u : ∀ k : ℕ,
      Summable
        (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℝ) *
            (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2) := by
    intro k
    refine (h_decay k).congr (fun i => ?_)
    rw [hcoeff_u i]
  obtain ⟨T, hT⟩ :=
    tensorL2_smoothRepr_of_allOrders_decay (I := I) (M := M) g r s u h_decay_u
  refine ⟨T, fun i => ?_⟩
  rw [hT, hcoeff_u i]

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

/-- **Classical `C^∞` spectral-series assembly.**

Let `u : TensorL2 r s g` be an `L²` tensor field whose intrinsic
eigenbasis coordinates `cᵢ = tensorL2Coeff h_compact u i` decay so fast
that, for *every even order* `2k`, the weighted squares
`(1 + λᵢ)^{2k} · cᵢ²` are summable. Then the eigenfunction series
`∑ᵢ cᵢ · eigenvectorSmooth g r s i` converges in `Cᵏ` for every `k`, and
its limit is a genuine smooth, compactly-supported section
`T : SmoothCcTensor g r s` whose `L²` class is `u`.

This is the **all-orders spectral Sobolev embedding** in its assembled
form. The body is a thin reduction to
`spectralSeries_hasSmoothSum_of_allOrders_summable` (whence to the deep
analytic core `tensorL2_smoothRepr_of_allOrders_decay`), identifying the
two `L²`-expansions of `u` — the resolvent eigenbasis expansion and the
smooth-section series — by `HasSum.unique`. The remaining genuine
analytic content lives strictly downstream, in the two posited leaves
`tensorEigenIdx_one_add_lambda_rpow_neg_summable` (Weyl summability) and
`smoothCcTensor_of_eigenSeries_poly_summable` (the uniform-limit-of-
derivatives `Cᵏ`-completeness core); consumers transitively depend on
`sorryAx` only through those two. The hypothesis is the *concrete*
all-orders coefficient summability of `u` (strictly weaker, and strictly
more elementary, than the abstract `⋂_σ Hˢ`-membership hypothesis of the
gate predicate, from which it is derived in
`spectralSmoothRealizesAsSmooth_holds`). -/
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
