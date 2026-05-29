import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.SobolevScaleSummable
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Spectrum

/-!
# Closability of the covariant gradient: the faithful `H¹ ↪ L²` embedding

For a closed Riemannian manifold `(M, g)` the canonical continuous linear map
`TensorH1ComplToTensorL2 g r s : TensorH1Compl g r s →L[ℝ] TensorL2 r s g`
extends the inclusion of smooth compactly-supported tensor sections (carrying
the `H¹` inner product `⟪T, v⟫_{H¹} = ⟪T, v⟫_{L²} + ⟪∇T, ∇v⟫_{L²}`) into the
tensor `L²` Hilbert space. So far only its dense range was known.

This file proves the map is **injective** — equivalently, the covariant gradient
`∇` is a *closable* operator: a sequence of smooth sections that is `H¹`-Cauchy
and tends to `0` in `L²` already tends to `0` in `H¹`. The closability content
is the integration-by-parts (Green) identity
`⟪∇T, ∇v⟫_{L²} = -⟪Δ_∇ T, v⟫_{L²}`, which expresses the `H¹` inner product as
the `L²` pairing against the symmetric operator `(1 - Δ_∇)`.

## Main results

* `oneMinusConnLapSmooth_toL2_inner_eq_h1_general` — the rank-`(0, s)` Green / `H¹`
  bridge from a `LoweringIntertwiner g s` witness: for smooth compactly-supported
  `(0, s)`-tensors `T, v`,
  `⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪⟦T⟧, ⟦v⟧⟫_{H¹}`.
* `TensorH1ComplToTensorL2_injective_of_green` — the closability headline at rank
  `(0, s)`, conditional on the `LoweringIntertwiner g s` witness.
* `TensorH1ComplToTensorL2_injective_two`, `..._three` — the unconditional
  injectivity at ranks `(0, 2)` and `(0, 3)`, discharging the witness with
  `loweringIntertwiner_two` / `loweringIntertwiner_three`.
* `smoothToTensorH1Compl_eigenvectorSmooth_eq` — the eigenvector identification
  `⟦eᵢ⟧ = μ⁻¹ • eigenvectorResolvent_unconditional i` in the `H¹` completion,
  obtained from the `(0, 2)` injectivity.
* `tensorL2Coeff_ofCompact_oneMinusConnLapSmooth` — the per-step eigen-coordinate
  identity `cᵢ((1 - Δ_∇) T) = (1 + λᵢ) · cᵢ(T)`.
* `smoothCcTensor_tensorL2Coeff_weighted_summable` — the headline: the eigenbasis
  coordinates of a smooth compactly-supported `(0, 2)`-tensor are weighted
  square-summable at every real Sobolev order `a`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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

/-! ## The rank-`(0, s)` Green / `H¹` bridge from an intertwiner witness

The committed `oneMinusConnLapSmooth_toL2_inner_eq_h1` is the rank-`(0, 2)`
specialisation of the identity below; we reprove the identity for arbitrary
covariant rank `s` from the rank-generic Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general`, given a
`LoweringIntertwiner g s` witness. -/

/-- **The rank-`(0, s)` Green / `H¹` bridge.** Given a metric-lowering intertwiner
witness at rank `s`, for smooth compactly-supported `(0, s)`-tensors `T, v` the
`L²` pairing of `(1 - Δ_∇) T` with `v` equals the `H¹` pairing of the completion
embeddings of `T` and `v`:
`⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪⟦T⟧, ⟦v⟧⟫_{H¹}`.

The proof is integration by parts. The `H¹` pairing decomposes as the `L²`
pairing plus the Dirichlet (integrated covariant-gradient) pairing; by the
connection-Laplacian Green identity the Dirichlet pairing equals
`-⟪Δ_∇ T, v⟫_{L²}`, and `(1 - Δ_∇) T = T - Δ_∇ T` splits the `L²` pairing of
the left-hand side accordingly. -/
theorem oneMinusConnLapSmooth_toL2_inner_eq_h1_general
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        (v : TensorL2 0 s g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ := by
  -- The `H¹` pairing of the two smooth embeddings is the `L²` pairing plus the
  -- integrated covariant-gradient (Dirichlet) pairing.
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    rw [show tensorL2Inner (I := I) (M := M) g 0 s
            (⟨T⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 s).toCcTensor.toFun =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  -- The Dirichlet integral equals the `L²` self-pairing of the covariant
  -- gradients.
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 s T v).symm
  -- The connection-Laplacian Green identity: `⟪∇T, ∇v⟫_{L²} = -⟪Δ_∇ T, v⟫_{L²}`.
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T).toFun
          (covGrad (I := I) (M := M) g 0 s v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_general
      (I := I) (M := M) g s hint T v
  -- The LHS `L²` pairing of `(1 - Δ_∇) T` with `v`.
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g),
          (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s
            (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  -- `(1 - Δ_∇) T = T - Δ_∇ T`, so its `L²` pairing splits.
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmooth (I := I) g 0 s T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
              TensorL2 0 s g),
            (v : TensorL2 0 s g)⟫_ℝ =
          ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
                TensorL2 0 s g),
              (v : TensorL2 0 s g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) =
            T - rawTensorConnLapSmooth (I := I) g 0 s T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
            TensorL2 0 s g), (v : TensorL2 0 s g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

/-! ## Closability: injectivity of `TensorH1ComplToTensorL2` (general rank `(0, s)`)

The Green / `H¹` bridge says, for smooth `T, v`,
`⟪⟦T⟧, ⟦v⟧⟫_{H¹} = ⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪toL2 ((1 - Δ_∇) T), F ⟦v⟧⟫_{L²}`,
where `F = TensorH1ComplToTensorL2 g 0 s` and `F ⟦v⟧ = v` in `L²`.

Both sides, viewed as functions of the second `H¹`-completion argument `w`, are
continuous linear functionals; they agree on the dense range of the smooth
embedding, hence everywhere:
`⟪⟦T⟧, w⟫_{H¹} = ⟪toL2 ((1 - Δ_∇) T), F w⟫_{L²}` for all `w`.

If `F w = 0`, the right-hand side vanishes, so `⟪⟦T⟧, w⟫_{H¹} = 0` for every
smooth `T`. By density of the smooth embeddings in the `H¹` completion (and
continuity of `v ↦ ⟪v, w⟫`), `⟪v, w⟫_{H¹} = 0` for all `v`, hence `w = 0`. -/

/-- **The `H¹`-completion `L²`-adjoint pairing.** For a smooth `(0, s)`-tensor `T`
and *any* `H¹`-completion element `w`,
`⟪⟦T⟧, w⟫_{H¹} = ⟪toL2 ((1 - Δ_∇) T), F w⟫_{L²}`,
where `F = TensorH1ComplToTensorL2 g 0 s`.

Both sides are continuous in `w` and agree on the dense range of
`smoothToTensorH1Compl`, where the identity is exactly the Green / `H¹` bridge
combined with `F ⟦v⟧ = v` in `L²`. -/
theorem inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : SmoothCcTensor g 0 s) (w : TensorH1Compl g 0 s) :
    ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ =
      ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ := by
  -- Two continuous functions of `w`, equal on the dense smooth range.
  set A : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩, w⟫_ℝ with hA
  set B : TensorH1Compl g 0 s → ℝ :=
    fun w => ⟪((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g),
        TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s w⟫_ℝ with hB
  have hA_cont : Continuous A := by
    rw [hA]
    exact (innerSL ℝ
      (smoothToTensorH1Compl (I := I) (M := M) g 0 s ⟨T⟩)).continuous
  have hB_cont : Continuous B := by
    rw [hB]
    exact ((innerSL ℝ
        ((oneMinusConnLapSmooth (I := I) g 0 s T : SmoothCcTensor g 0 s) :
          TensorL2 0 s g)).comp
      (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s)).continuous
  -- Agreement on the dense range of the coercion `(↑) : SmoothCcTensorH1 → …`.
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        B ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) := by
    funext V
    -- `↑V = smoothToTensorH1Compl V`.
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    simp only [Function.comp_apply, hA, hB, hcoe]
    -- `A (⟦V⟧) = ⟪⟦T⟧, ⟦V⟧⟫_{H¹}` and `B (⟦V⟧) = ⟪(1-Δ)T, V.toCcTensor⟫_{L²}`.
    -- Restate `V` as a wrapped smooth section to use the Green / `H¹` bridge.
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by
      cases V; rfl
    rw [hV]
    -- RHS: `F ⟦V⟧ = V.toCcTensor` in `L²`.
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
    -- Now both sides are pairings of smooth sections.
    rw [← oneMinusConnLapSmooth_toL2_inner_eq_h1_general
      (I := I) (M := M) g s hint T V.toCcTensor]
  -- Dense range of the smooth coercion.
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_AB : A = B := h_dense.equalizer hA_cont hB_cont h_eq_on
  exact congr_fun h_AB w

/-- **Closability of the covariant gradient (general rank `(0, s)`).** Given a
metric-lowering intertwiner witness at rank `s`, the canonical `H¹ → L²`
inclusion `TensorH1ComplToTensorL2 g 0 s` is injective: a kernel element pairs to
`0` against every smooth `H¹` test class, hence vanishes by density. -/
theorem TensorH1ComplToTensorL2_injective_of_green
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 s) := by
  -- Reduce to triviality of the kernel.
  rw [injective_iff_map_eq_zero]
  intro w hw
  -- `⟪v, w⟫_{H¹} = 0` for every `v`, via density and the adjoint pairing.
  refine ext_inner_left ℝ ?_
  -- Show `⟪v, w⟫ = ⟪v, 0⟫` for all `v`, by `DenseRange.equalizer`.
  intro v
  rw [inner_zero_right]
  -- Two continuous functions of `v`: `v ↦ ⟪v, w⟫` and the constant `0`.
  set A : TensorH1Compl g 0 s → ℝ := fun v => ⟪v, w⟫_ℝ with hA
  have hA_cont : Continuous A := by
    rw [hA]
    exact Continuous.inner continuous_id continuous_const
  have h_eq_on :
      A ∘ ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) =
        (fun _ : SmoothCcTensorH1 g 0 s => (0 : ℝ)) := by
    funext V
    simp only [Function.comp_apply, hA]
    have hcoe : (V : TensorH1Compl g 0 s) =
        smoothToTensorH1Compl (I := I) (M := M) g 0 s V := rfl
    rw [hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : SmoothCcTensorH1 g 0 s) := by cases V; rfl
    rw [hV]
    -- The adjoint pairing kills `⟪⟦V.toCcTensor⟧, w⟫` via `F w = 0`.
    rw [inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green
      (I := I) (M := M) g s hint V.toCcTensor w]
    rw [hw, inner_zero_right]
  have h_dense :
      DenseRange ((↑) : SmoothCcTensorH1 g 0 s → TensorH1Compl g 0 s) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq :
      A = (fun _ : TensorH1Compl g 0 s => (0 : ℝ)) :=
    h_dense.equalizer hA_cont continuous_const h_eq_on
  have := congr_fun h_eq v
  rw [hA] at this
  exact this

/-- **Closability of the covariant gradient at rank `(0, 2)` (unconditional).**
The faithful `H¹ ↪ L²` embedding for `(0, 2)`-tensor fields. -/
theorem TensorH1ComplToTensorL2_injective_two
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 2) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 2
    (loweringIntertwiner_two (I := I) (M := M) g)

/-- **Closability of the covariant gradient at rank `(0, 3)` (unconditional).**
The faithful `H¹ ↪ L²` embedding for `(0, 3)`-tensor fields. -/
theorem TensorH1ComplToTensorL2_injective_three
    (g : SmoothRiemannianMetric I M) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g 0 3) :=
  TensorH1ComplToTensorL2_injective_of_green (I := I) (M := M) g 3
    (loweringIntertwiner_three (I := I) (M := M) g)

/-! ## The eigenvector identification

With injectivity at rank `(0, 2)` in hand, the smooth eigenvector's `H¹`-completion
embedding is the rescaled eigenvector resolvent: both sides have the same image
under `TensorH1ComplToTensorL2`, so they are equal. -/

/-- **The smooth eigenvector's `H¹` embedding is the rescaled resolvent
eigenvector.** For the smooth representative `eᵢ = eigenvectorSmooth_unconditional i`
of the resolvent eigenbasis vector at index `i`,
`⟦eᵢ⟧ = (i.fst.val)⁻¹ • eigenvectorResolvent_unconditional i`
in the `H¹` completion. Both sides have the same image
`tensorResolventEigenbasisVec_ofCompact i` under the injective `H¹ → L²` map. -/
theorem smoothToTensorH1Compl_eigenvectorSmooth_eq
    (g : SmoothRiemannianMetric I M)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    smoothToTensorH1Compl (I := I) (M := M) g 0 2
        ⟨eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent_unconditional (I := I) (M := M) g 0 2 i := by
  apply TensorH1ComplToTensorL2_injective_two (I := I) (M := M) g
  -- LHS image: `F ⟦eᵢ⟧ = (eᵢ : L²) = tensorResolventEigenbasisVec_ofCompact i`.
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
  -- `(⟨eᵢ⟩ : SmoothCcTensorH1).toCcTensor = eᵢ`.
  change (eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i :
        TensorL2 0 2 g) =
      TensorH1ComplToTensorL2 (I := I) (M := M) g 0 2
        ((i.fst.val)⁻¹ •
          eigenvectorResolvent_unconditional (I := I) (M := M) g 0 2 i)
  rw [eigenvectorSmooth_toL2_unconditional (I := I) (M := M) g 0 2 i,
    map_smul]
  -- RHS image: `(i.fst.val)⁻¹ • F (eigenvectorResolvent_unconditional i)`, which
  -- by `eigenvector_eq_resolvent_smul_unconditional` equals the eigenvector.
  exact eigenvector_eq_resolvent_smul_unconditional (I := I) (M := M) g 0 2 i

/-! ## The resolvent-to-Laplacian eigenvalue translation

`λᵢ = (1 - μ)/μ` with `μ = i.fst.val ∈ (0, 1]`, so `1 + λᵢ = μ⁻¹`. -/

/-- The resolvent eigenvalue `μ = i.fst.val` is positive. -/
theorem tensorEigenIdx_val_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

/-- `1 + λᵢ = (i.fst.val)⁻¹`. -/
theorem one_add_lambda_eq_inv_val
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s) :
    1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) i = (i.fst.val)⁻¹ := by
  have hpos : 0 < i.fst.val := tensorEigenIdx_val_pos (I := I) (M := M) i
  change 1 + tensorLaplacianEigenvalueOf i.fst.val = (i.fst.val)⁻¹
  rw [tensorLaplacianEigenvalueOf]
  field_simp
  ring

/-! ## The per-step eigen-coordinate identity

`cᵢ((1 - Δ_∇) T) = (1 + λᵢ) · cᵢ(T)`, the spectral statement that `(1 - Δ_∇)`
acts diagonally with eigenvalue `(1 + λᵢ)` on the eigenbasis coordinate. -/

/-- **The per-step eigen-coordinate identity.** Applying the smooth
one-minus-connection-Laplacian scales the `i`-th eigenbasis coordinate by
`(1 + λᵢ)`:
`cᵢ((1 - Δ_∇) T) = (1 + λᵢ) · cᵢ(T)`. -/
theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) :
    tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g 0 2 T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  classical
  -- The eigenbasis coordinate is `⟪bᵢ, ·⟫` with `bᵢ = (eᵢ : L²)` the smooth
  -- eigenvector's `L²` image.
  have hb :
      tensorResolventHilbertEigenbasisSigma_ofCompact (I := I) (M := M) h_compact i =
        (eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i :
          TensorL2 0 2 g) := by
    rw [tensorResolventHilbertEigenbasisSigma_ofCompact_apply,
      eigenvectorSmooth_toL2_unconditional (I := I) (M := M) g 0 2 i]
  -- Rewrite both coordinates as inner products against `bᵢ = (eᵢ : L²)`.
  rw [tensorL2Coeff_ofCompact_eq_inner, tensorL2Coeff_ofCompact_eq_inner, hb,
    SmoothCcTensor.toL2_apply, SmoothCcTensor.toL2_apply]
  -- Step 1: commute the `L²` pairing (the LHS occurrence) and apply the
  -- Green / `H¹` bridge.
  rw [real_inner_comm
    ((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
      TensorL2 0 2 g)
    (eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i : TensorL2 0 2 g),
    oneMinusConnLapSmooth_toL2_inner_eq_h1_general (I := I) (M := M) g 2
      (loweringIntertwiner_two (I := I) (M := M) g) T
      (eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i)]
  -- Step 2: the eigenvector identification and `inner_smul_right`.
  rw [smoothToTensorH1Compl_eigenvectorSmooth_eq (I := I) (M := M) g i,
    inner_smul_right]
  -- Step 3: commute the `H¹` pairing and apply the weak eigen-equation.
  rw [real_inner_comm
    (eigenvectorResolvent_unconditional (I := I) (M := M) g 0 2 i)
    (smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩),
    eigenvectorSmooth_weak_eigen_unconditional (I := I) (M := M) g 0 2 i ⟨T⟩]
  -- Step 4: `⟨T⟩.toCcTensor = T`, real symmetry, and `1 + λ = μ⁻¹`.
  rw [show ((⟨T⟩ : SmoothCcTensorH1 g 0 2).toCcTensor : TensorL2 0 2 g) =
        (T : TensorL2 0 2 g) from rfl,
    real_inner_comm
      (eigenvectorSmooth_unconditional (I := I) (M := M) g 0 2 i : TensorL2 0 2 g)
      (T : TensorL2 0 2 g),
    one_add_lambda_eq_inv_val (I := I) (M := M) i]

/-! ## The headline: weighted Sobolev-scale summability

Iterating the per-step identity `k` times gives
`cᵢ((1 - Δ_∇)^k T) = (1 + λᵢ)^k · cᵢ(T)`, hence Parseval bounds
`∑ (1 + λᵢ)^{2k} cᵢ(T)² = ‖(1 - Δ_∇)^k T‖²_{L²} < ∞`, and the even-order
domination reduction extends this to every real Sobolev order `a`. -/

/-- The iterated per-step identity: `cᵢ((1 - Δ_∇)^k T) = (1 + λᵢ)^k · cᵢ(T)`. -/
theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2) (k : ℕ) :
    tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ k *
        tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
          (I := I) (M := M) g h_compact (oneMinusConnLapSmoothIter (I := I) g 0 2 k T) i,
        ih, pow_succ]
      ring

/-- **Even-order weighted summability.** At an even integer order `2k`, the
weighted eigenbasis coordinates of a smooth `(0, 2)`-tensor are square-summable,
since `∑ (1 + λᵢ)^{2k} cᵢ(T)² = ‖toL2 ((1 - Δ_∇)^k T)‖²_{L²}` by the iterated
per-step identity and Parseval. -/
theorem smoothCcTensor_tensorL2Coeff_weighted_summable_even
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
        (tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  -- The weighted term equals the squared coordinate of `(1 - Δ_∇)^k T`.
  have h_term :
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
          (tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 T) i) ^ 2) =
        fun i => (tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g 0 2 k T)) i) ^ 2 := by
    funext i
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
      (I := I) (M := M) g h_compact T i k]
    -- `(1 + λᵢ)^{2k} = ((1 + λᵢ)^k)^2`, and `tensorSobolevWeight i (2k) = (1+λ)^(2k)`.
    rw [mul_pow]
    congr 1
    -- `tensorSobolevWeight i (2k) = (1 + λᵢ)^{2k} = ((1+λ)^k)^2`.
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [h_term]
  -- Parseval: the sum of squared coordinates is the squared `L²` norm, finite.
  have h_parseval := tensorParseval_l2Coeff_ofCompact_sq
    (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))
  -- The coordinate family is square-summable (Parseval / Bessel).
  exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g 0 2 k T))

/-- **The weighted Sobolev-scale summability headline.** For a closed Riemannian
manifold `(M, g)` and a smooth compactly-supported `(0, 2)`-tensor field `T`, the
eigenbasis coordinates of `T` are weighted square-summable at *every* real Sobolev
order `a`: `∑ᵢ (1 + λᵢ)^a · cᵢ(T)² < ∞`.

This is the spectral-side statement "smooth ⇒ in every `Hˢ`". The proof reduces
to an even integer order `2k ≥ a` by the monotone domination
`summable_tensorSobolevWeight_of_even`, where the iterated per-step identity plus
Parseval gives finiteness. -/
theorem smoothCcTensor_tensorL2Coeff_weighted_summable
    (g : SmoothRiemannianMetric I M) (a : ℝ) (T : SmoothCcTensor g 0 2)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i a *
        (tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 T) i) ^ 2) := by
  -- Choose an even integer `2k ≥ a`.
  obtain ⟨k, hk⟩ := exists_nat_ge (a / 2)
  have hak : a ≤ (2 * k : ℕ) := by
    have : a / 2 ≤ (k : ℝ) := hk
    push_cast
    linarith
  exact summable_tensorSobolevWeight_of_even
    (I := I) (M := M)
    (fun i => tensorL2Coeff_ofCompact (I := I) (M := M) h_compact
      (SmoothCcTensor.toL2 T) i)
    hak
    (smoothCcTensor_tensorL2Coeff_weighted_summable_even
      (I := I) (M := M) g k T h_compact)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
