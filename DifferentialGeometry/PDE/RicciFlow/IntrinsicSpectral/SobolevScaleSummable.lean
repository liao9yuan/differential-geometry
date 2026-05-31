import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Defs
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Inclusion
import DifferentialGeometry.Integral.Connection.TensorConnLapGreenDivergenceIdentityGeneral
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothToL2

/-!
# Weighted Sobolev-scale summability of spectral coordinates

For a closed Riemannian manifold `(M, g)` and a smooth, compactly-supported
`(0, 2)`-tensor field `T`, this file develops the spectral-side infrastructure
showing that the eigenbasis (resolvent eigenbasis) coordinates of `T` are
*weighted* square-summable at the Sobolev weight `(1 + λᵢ)^a` for arbitrary real
`a` — the standard "smooth ⇒ in every `Hˢ`" elliptic-regularity statement, read
purely on the spectral side.

The key intrinsic operator is the **smooth one-minus-connection-Laplacian**
`oneMinusConnLapSmooth g r s T := T - rawTensorConnLapSmooth g r s T`, a map
`SmoothCcTensor g r s → SmoothCcTensor g r s` (the geometer Laplacian sign
convention `Δ_∇ = -∇*∇`, so the resolvent is `(1 - Δ_∇)⁻¹`).

## Main definitions

* `oneMinusConnLapSmooth g r s T` — the bundled `SmoothCcTensor → SmoothCcTensor`
  operator `T ↦ T - Δ_∇ T`.
* `oneMinusConnLapSmoothIter g r s k T` — its `k`-fold iterate.

## Main results

* `oneMinusConnLapSmooth_toL2_inner_eq_h1` — the unconditional **Green / H¹
  bridge**: for smooth compactly-supported `(0, 2)`-tensors `T, v`,
  `⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪⟦T⟧, ⟦v⟧⟫_{H¹}`, where `⟦·⟧` is the canonical
  embedding into the `H¹` completion. This is integration by parts:
  `⟪T, v⟫_{L²} - ⟪Δ_∇ T, v⟫_{L²} = ⟪T, v⟫_{L²} + ⟪∇T, ∇v⟫_{L²}`.
* `tensorParseval_l2Coeff_ofCompact_sq` — the Parseval norm identity restated for
  the eigenbasis coordinate functional `tensorL2Coeff`:
  `∑ᵢ (tensorL2Coeff h_compact u i)² = ‖u‖²_{L²}`.
* `summable_tensorSobolevWeight_of_even` — the **even-order domination /
  monotonicity reduction** (Step 1): for any `a ≤ 2k`, weighted summability at the
  even integer weight `2k` implies weighted summability at `a`.

## Status

This file provides the complete, unconditional spectral-side scaffolding for the
weighted-summability headline. The remaining ingredient — the per-step
eigen-coordinate identity
`tensorL2Coeff h_compact ((1 - Δ_∇) T) i =
  (1 + λᵢ) · tensorL2Coeff h_compact T i` —
requires identifying the smooth eigenvector's `H¹`-completion embedding with the
resolvent eigenvector `eigenvectorResolvent i` up to the scalar
`μ = i.fst.val`, which in turn requires injectivity of the `H¹`-to-`L²`
completion inclusion `TensorH1ComplToTensorL2` (only its dense range is currently
on disk). See the module note at the end for the precise missing signature.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The smooth one-minus-connection-Laplacian `(1 - Δ_∇)` -/

/-- **The smooth one-minus-connection-Laplacian** on compactly-supported smooth
`(r, s)`-tensor sections: `T ↦ T - Δ_∇ T`, where `Δ_∇ = rawTensorConnLapSmooth`
is the rough connection Laplacian (geometer sign convention). As a map
`SmoothCcTensor g r s → SmoothCcTensor g r s` it keeps the input smooth and
compactly supported. The associated resolvent is `(1 - Δ_∇)⁻¹`. -/
noncomputable def oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  T - rawTensorConnLapSmooth (I := I) g r s T

/-- The underlying section of `oneMinusConnLapSmooth` is the pointwise difference
of `T` and `rawTensorConnLap T`. -/
@[simp] lemma oneMinusConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (oneMinusConnLapSmooth (I := I) g r s T).toSection x =
      T.toSection x -
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold oneMinusConnLapSmooth
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    rawTensorConnLapSmooth_toSection_apply]

/-! ## The `k`-fold iterate of `(1 - Δ_∇)` -/

/-- **`k`-fold iterate of the smooth one-minus-connection-Laplacian.** Defined by
recursion on `k`: `0 ↦ identity`; `(k+1) ↦ apply `(1 - Δ_∇)` once to the `k`-th
iterate. -/
noncomputable def oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => oneMinusConnLapSmooth (I := I) g r s
                  (oneMinusConnLapSmoothIter g r s k T)

/-- The zero-th iterate is the input. -/
@[simp] theorem oneMinusConnLapSmoothIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 0 T = T := rfl

/-- The `(k+1)`-th iterate is `(1 - Δ_∇)` applied to the `k`-th iterate. -/
@[simp] theorem oneMinusConnLapSmoothIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (k + 1) T =
      oneMinusConnLapSmooth (I := I) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k T) := rfl

/-! ## The Green / `H¹` bridge for `(1 - Δ_∇)` at rank `(0, 2)`

The defining integration-by-parts identity: for smooth compactly-supported
`(0, 2)`-tensors `T, v`, the `L²` pairing of `(1 - Δ_∇) T` with `v` equals the
`H¹` pairing of the completion embeddings of `T` and `v`. Concretely
`⟪T, v⟫_{L²} - ⟪Δ_∇ T, v⟫_{L²} = ⟪T, v⟫_{L²} + ⟪∇T, ∇v⟫_{L²}` by the
connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two`. -/

/-- **The Green / `H¹` bridge for `(1 - Δ_∇)`.** For smooth compactly-supported
`(0, 2)`-tensors `T, v`,
`⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪⟦T⟧, ⟦v⟧⟫_{H¹}`,
where `⟦·⟧ = smoothToTensorH1Compl` is the canonical `H¹`-completion embedding.

The proof is integration by parts. By the (unconditional) connection-Laplacian
Green identity, `⟪∇T, ∇v⟫_{L²} = -⟪Δ_∇ T, v⟫_{L²}`; the `H¹` inner product of
the smooth embeddings decomposes as the `L²` pairing plus this gradient pairing,
so `⟪⟦T⟧, ⟦v⟧⟫_{H¹} = ⟪T, v⟫_{L²} - ⟪Δ_∇ T, v⟫_{L²} = ⟪(1 - Δ_∇) T, v⟫_{L²}`. -/
theorem oneMinusConnLapSmooth_toL2_inner_eq_h1
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
          TensorL2 0 2 g),
        (v : TensorL2 0 2 g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ := by
  -- The `H¹` pairing of the two smooth embeddings decomposes as the `L²`
  -- pairing plus the integrated covariant-gradient (Dirichlet) pairing.
  -- `⟪⟦T⟧, ⟦v⟧⟫_{H¹} = ⟪⟨T⟩, ⟨v⟩⟫_{SmoothCcTensorH1}` (completion inner-coe),
  -- which is `tensorH1Inner` of the underlying sections.
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    -- `⟨T⟩.toCcTensor = T`, `⟨v⟩.toCcTensor = v` definitionally; identify the
    -- `L²` part with the completion-inner-product of the coercions.
    rw [show tensorL2Inner (I := I) (M := M) g 0 2
            (⟨T⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  -- The Dirichlet integral equals the `L²` self-pairing of the covariant
  -- gradients, by the metric-isometry bridge.
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 2 T v).symm
  -- The connection-Laplacian Green identity:
  -- `⟪∇T, ∇v⟫_{L²} = -⟪Δ_∇ T, v⟫_{L²}`.
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
      (I := I) (M := M) g T v
  -- The LHS `L²` pairing of `(1 - Δ_∇) T` with `v` unfolds via `inner_def`.
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g),
          (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  -- `(1 - Δ_∇) T = T - Δ_∇ T`, so its `L²` pairing splits by bilinearity.
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
              TensorL2 0 2 g),
            (v : TensorL2 0 2 g)⟫_ℝ =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
                TensorL2 0 2 g),
              (v : TensorL2 0 2 g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) =
            T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

/-! ## Parseval restated for the `_ofCompact` coordinate functional

The Parseval identity `tensorParseval_norm_sq` is restated in terms of
the coordinate functional `tensorL2Coeff`, which is the exact
coordinate the spectral Sobolev scale `tensorHs` and the weighted-summability
headline consume. -/

/-- **Parseval for `tensorL2Coeff`.** For any `L²` tensor field `u`,
the sum of the squared chart-locality-free eigenbasis coordinates equals the
squared `L²` norm of `u`. -/
theorem tensorParseval_l2Coeff_ofCompact_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : TensorL2 r s g) :
    ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
        (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2 =
      ‖u‖ ^ 2 := by
  rw [tensorParseval_norm_sq (I := I) (M := M) h_compact u]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact u i,
    Real.norm_eq_abs, sq_abs]

/-- **Weighted square-summability of the `_ofCompact` coordinates.** For any
`L²` tensor field `u`, the eigenbasis-coordinate family is square-summable; this
is `tensorL2Coeff_summable_sq`, re-exported here for use in the
domination argument. -/
theorem tensorL2Coeff_ofCompact_summable_sq'
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : TensorL2 r s g) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2) :=
  tensorL2Coeff_summable_sq (I := I) (M := M) h_compact u

/-! ## Step 1: even-order domination / monotonicity reduction

The Sobolev weight `tensorSobolevWeight i a = (1 + λᵢ)^a` is monotone increasing
in the exponent (since `1 + λᵢ ≥ 1`). Therefore weighted summability at an even
integer order `2k ≥ a` dominates weighted summability at `a`: every weighted term
at exponent `a` is bounded above by the corresponding term at exponent `2k`, and
the terms are non-negative. -/

/-- **Even-order domination (Step 1).** If `a ≤ 2k` and the coordinate family
`c` is weighted-square-summable at the even integer exponent `2k`, then it is
weighted-square-summable at `a`. The terms at exponent `a` are dominated by the
terms at exponent `2k` because the Sobolev weight is monotone in the exponent
(its base `1 + λᵢ ≥ 1`), and all terms are non-negative. -/
theorem summable_tensorSobolevWeight_of_even
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    {a : ℝ} {k : ℕ} (hak : a ≤ (2 * k : ℕ))
    (h2k : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) * (c i) ^ 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i a * (c i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h2k
  · -- The exponent-`a` weighted terms are non-negative.
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i a
    positivity
  · -- Each exponent-`a` term is dominated by the exponent-`2k` term.
    have hmono :
        tensorSobolevWeight (I := I) (M := M) i a ≤
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) :=
      tensorSobolevWeight_mono (I := I) (M := M) i hak
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

/-! ## Module note: the precise remaining ingredient

The weighted-summability headline

```
theorem smoothCcTensor_tensorL2Coeff_weighted_summable
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i a *
        (tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2)
```

reduces — via `summable_tensorSobolevWeight_of_even` (Step 1) and
`tensorParseval_l2Coeff_ofCompact_sq` (Parseval, applied to
`u = SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter g 0 2 k T)`) — to the single
**per-step eigen-coordinate identity**

```
tensorL2Coeff h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmooth g 0 2 T)) i
  = (1 + TensorEigenIdx.lambda i) *
      tensorL2Coeff h_compact (SmoothCcTensor.toL2 T) i,
```

equivalently `⟪⟦T⟧, ⟦eᵢ⟧⟫_{H¹} = (1 + λᵢ) · ⟪T, eᵢ⟫_{L²}` for the smooth
eigenvector `eᵢ = eigenvectorSmooth i`, which is provided here as
the Green / `H¹` bridge `oneMinusConnLapSmooth_toL2_inner_eq_h1` together with the
eigenvector identification

```
smoothToTensorH1Compl g 0 2 ⟨eigenvectorSmooth i⟩
  = (i.fst.val)⁻¹ • eigenvectorResolvent i.
```

That eigenvector identification is the one fact not yet on disk. Both sides have
the same image under `TensorH1ComplToTensorL2` (namely `eigenvectorSmooth i`
in `L²`, by `eigenvectorSmooth_toL2` and
`eigenvector_eq_resolvent_smul`), so it follows once
`TensorH1ComplToTensorL2 g 0 2` is known to be **injective** — currently only its
dense range (`denseRange_TensorH1ComplToTensorL2`) is established. The required
missing lemma is therefore:

```
theorem TensorH1ComplToTensorL2_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)
```

(the faithful Sobolev `H¹ ↪ L²` embedding for tensor fields). This is a genuine
Sobolev-embedding theorem, not packaging; it is the precise prerequisite the
headline awaits.
-/

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
