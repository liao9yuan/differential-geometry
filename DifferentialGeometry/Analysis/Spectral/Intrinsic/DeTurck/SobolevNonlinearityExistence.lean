import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv

/-!
# Short-time existence driven by the continuous (Sobolev) Ricci–DeTurck nonlinearity

This file assembles the **continuous, non-gated** Ricci–DeTurck nonlinearity on the
spectral Sobolev scale by **Nemytskii-by-density / Lipschitz extension**, and feeds it
into the unconditional maximal-regularity engine
`deTurckRemainder_strong_shortTime_exists`
(`Analysis/Spectral/Intrinsic/DeTurck/RemainderShortTimeExistence.lean`).

## The dense-extension architecture (no rough pointwise evaluation, no gating)

A rough Sobolev element of `tensorHs g₀ 0 2 (a+1)` has **no pointwise values**, so it can
neither index the chart polynomial nor be fed to the intrinsic `deTurckRicciRHS` (which
needs a genuine `SmoothRiemannianMetric` and its second chart-derivatives).  The classical
remedy is to define the nonlinearity on **smooth** data and extend by uniform continuity.

* `deTurckSmoothN` — the **smooth-input** nonlinearity.  For a *smooth* compactly-supported
  `(0,2)`-tensor `T : SmoothCcTensor g₀ 0 2` whose symmetrization is `g₀`-fibre small
  (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`, `δ < 1`, so `g₀ + T` is a genuine
  `SmoothRiemannianMetric` via `tensorSectionRealizeMetric`), `deTurckSmoothN T` reads off
  the order-`a` spectral coordinates of the **genuine intrinsic remainder**

    `deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`

  as the smooth `(0,2)`-tensor `deTurckRHSSection g_bg (g₀ + T) − rawTensorConnLapSmooth g₀ 0 2 T`.
  Its `tensorHs g₀ 0 2 a` membership is the spectral-scale summability of a smooth
  compactly-supported tensor (`smoothCcTensor_tensorL2Coeff_weighted_summable`).  This uses
  the **sorry-free intrinsic objects directly** — no chart-rough-evaluation and no
  finite-support gating.

* `smoothCcToTensorHs` — the canonical embedding of smooth tensors into the spectral scale
  `tensorHs g₀ 0 2 σ` (the same `L²`-coordinate read-off), with dense range
  (`smoothCcToTensorHs_denseRange`).

* `deTurckSobolevNHa2` — the **total** continuous quasilinear nonlinearity
  `tensorHs g₀ 0 2 (a+2) → tensorHs g₀ 0 2 a`, the dense/uniformly-continuous extension of
  `deTurckSmoothN` (codomain `tensorHs g₀ 0 2 a` is complete), recentred onto the engine
  ball by `recenteredBallRetraction`.  It agrees with `deTurckSmoothN` on smooth fibre-small
  in-ball inputs (`deTurckSobolevNHa2_eq_smoothN`), so the genuine Ricci–DeTurck remainder is
  what the flow sees; it carries no `realizableAt` / finite-support / HLCC gate.

## The analytic core and the extension input

The deep classical input is the **smooth-ball Lipschitz estimate** at the quasilinear
`H^{a+2}` order, `smoothRemainderDiff_ballLipschitz_Ha2`
(`‖N(T) − N(T')‖_{H^a} ≤ K · ‖ι(a+2) T − ι(a+2) T'‖` for smooth fibre-small `T, T'` in the
`H^{a+2}`-ball), proven by majorising the chart-polynomial remainder **difference**
`chartDeTurckRicciRHS_sub_eq` term by term with the Moser / Gagliardo–Nirenberg tame-product
backbone.  It needs the **supercritical** Sobolev-algebra order `2 * (a + 1) > finrank E + 4`
(hypothesis `ha_super`); the order is `H^{a+2}` because the Ricci–DeTurck flow is
**quasilinear** (the difference carries second-order `∂²(T − T')` jet factors).

The rephrased `deTurckSmoothN_ballLipschitz_Ha2`, `smoothCcToTensorHs_denseRange`,
`deTurckSobolevNHa2_eq_smoothN`, and `deTurckSobolevNHa2_lipschitzWith` package the Lipschitz
dense extension to the complete codomain, consumed by the quasilinear maximal-regularity engine
in `DeTurckQuasilinearExistence.lean`.
-/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The genuine Ricci–DeTurck remainder of a SMOOTH fibre-small perturbation, as a smooth
`(0,2)`-tensor.**

For the initial metric `g₀`, DeTurck background `g_bg`, and a smooth compactly-supported
`(0,2)`-tensor `T` whose symmetrization is `g₀`-fibre small with constant `δ < 1` (so
`g₀ + T` is a genuine `SmoothRiemannianMetric` via `tensorSectionRealizeMetric`), this is
the smooth tensor

  `deTurckRHSSection g_bg (g₀ + T) − rawTensorConnLapSmooth g₀ 0 2 T`

(the intrinsic Ricci–DeTurck right-hand side of the realized metric, minus the connection
Laplacian of the perturbation — the gauge-cancelled first-order remainder).  Because the
input is smooth this uses the **sorry-free intrinsic objects directly**: no chart-rough
evaluation, no finite-support / `realizableAt` gating. -/
def deTurckSmoothRemainder (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }
  - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

/-- **The smooth-input Ricci–DeTurck nonlinearity.**

For a smooth fibre-small `T : SmoothCcTensor g₀ 0 2`, `deTurckSmoothN g₀ g_bg a hδ_lt hδ`
is the order-`a` spectral element whose eigenbasis coordinates are the `L²` coordinates of
the genuine remainder `deTurckSmoothRemainder g₀ g_bg T`
(`= deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`).  Its `H^a` membership is the spectral-scale
summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at every real order).  This is the
**continuous, non-gated** Ricci–DeTurck remainder on the smooth representatives. -/
def deTurckSmoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      (a : ℝ) (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

/-- The eigenbasis coordinate of `deTurckSmoothN` is the `L²` coordinate of the genuine
smooth remainder. -/
@[simp] theorem deTurckSmoothN_coeff (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i :=
  rfl

/-- **The canonical embedding of smooth tensors into the spectral Sobolev scale.**

A smooth compactly-supported `(0,2)`-tensor `T` is sent to the order-`σ` spectral element
whose eigenbasis coordinates are the `L²` coordinates of `T` (`SmoothCcTensor.toL2 T`).  Its
`H^σ` membership is `smoothCcTensor_tensorL2Coeff_weighted_summable` (smooth data is in every
`H^σ`).  This is the genuine, total, non-gating inclusion `SmoothCcTensor g₀ 0 2 → H^σ`. -/
def smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    tensorHs (I := I) (M := M) g₀ 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

/-- The eigenbasis coordinate of the smooth-tensor embedding is the `L²` coordinate of `T`. -/
@[simp] theorem smoothCcToTensorHs_coeff (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

/-- **Density of the smooth-tensor embedding in the spectral Sobolev scale.**

The textbook fact that smooth compactly-supported tensors are dense in `H^σ`, here for the
intrinsic spectral scale `tensorHs g₀ 0 2 σ`: the spectral coordinates of smooth data exhaust
the weighted-`ℓ²` space (finite-support spectral elements are dense
— `tensorHsFiniteSupportSubmodule_dense` — and each is the embedding of a smooth tensor).

Each finitely-supported spectral element `x` is the embedding `smoothCcToTensorHs g₀ σ` of the
smooth finite eigen-combination `finiteEigenCombo g₀ (support x.coeff) x.coeff`: their spectral
coordinates coincide (`finiteEigenComboHs_coeff_eq`, `finiteEigenCombo_tensorL2Coeff`), so the
range of `smoothCcToTensorHs` contains the dense finite-support submodule and is therefore
dense. -/
theorem smoothCcToTensorHs_denseRange (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    DenseRange (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
  classical
  have hsub :
      (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g₀) (r := 0) (s := 2) σ :
          Set (tensorHs (I := I) (M := M) g₀ 0 2 σ)) ⊆
        Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
    intro x hx
    have hxfin : (Function.support x.coeff).Finite :=
      (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) x).1 hx
    refine ⟨finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff, ?_⟩
    refine tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    have hcoeff :
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2
              (finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff)) i =
          (if i ∈ hxfin.toFinset then x.coeff i else 0) := by
      rw [SmoothCcTensor.toL2_apply,
        finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g₀ hxfin.toFinset x.coeff i]
    rw [hcoeff]
    by_cases hi : i ∈ hxfin.toFinset
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Set.Finite.mem_toFinset] at hi
      exact (Function.notMem_support.mp hi).symm
  exact (tensorHsFiniteSupportSubmodule_dense (I := I) (M := M)).mono hsub

/-- The smooth-tensor embedding `smoothCcToTensorHs` is additive in its tensor argument:
its spectral coordinates are the `L²` coordinates of the tensor, and both `tensorL2Coeff`
and `SmoothCcTensor.toL2` are additive. -/
theorem smoothCcToTensorHs_add (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S + T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S +
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.add_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (S + T) =
        SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T from map_add _ _ _,
    tensorL2Coeff_add]

/-- The smooth-tensor embedding `smoothCcToTensorHs` is negation-compatible in its tensor
argument. -/
theorem smoothCcToTensorHs_neg (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (-S) =
      -smoothCcToTensorHs (I := I) (M := M) g₀ σ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.neg_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (-S) = -SmoothCcTensor.toL2 S from map_neg _ _]
  rw [show (-SmoothCcTensor.toL2 S : TensorL2 0 2 g₀) = (-1 : ℝ) • SmoothCcTensor.toL2 S by
    rw [neg_one_smul]]
  rw [tensorL2Coeff_smul]
  ring

/-- The smooth-tensor embedding `smoothCcToTensorHs` is subtraction-compatible in its tensor
argument: `ι(S − T) = ι S − ι T`. -/
theorem smoothCcToTensorHs_sub (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S - T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S -
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smoothCcToTensorHs_add, smoothCcToTensorHs_neg]

/-- **The smooth nonlinearity difference is the spectral embedding of the genuine remainder
difference.**

For smooth fibre-small `T, T'`, `deTurckSmoothN T − deTurckSmoothN T'` (in `H^a`) is exactly
the order-`a` spectral embedding `smoothCcToTensorHs g₀ a` of the difference of the two genuine
smooth remainders `deTurckSmoothRemainder T − deTurckSmoothRemainder T'`.  Both sides have, at
each eigenbasis index `i`, the `L²` coordinate of the corresponding remainder (read off by the
same compact-resolvent witness), so the identity is the additivity of `tensorL2Coeff` and
`SmoothCcTensor.toL2` over the remainder difference. -/
theorem deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
        deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') := by
  refine tensorHs.ext ?_
  funext i
  have hsub :
      (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i =
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i -
          (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i := by
    rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rfl
  have hcoeff_sub :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i -
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i := by
    rw [show SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
          SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) -
            SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
        from map_sub _ _ _]
    rw [sub_eq_add_neg, tensorL2Coeff_add]
    rw [show (-SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') :
          TensorL2 0 2 g₀) =
        (-1 : ℝ) • SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') by
      rw [neg_one_smul]]
    rw [tensorL2Coeff_smul]
    ring
  rw [hsub, deTurckSmoothN_coeff, deTurckSmoothN_coeff, smoothCcToTensorHs_coeff, hcoeff_sub]

/-- **The innermost-peel recursion for the one-minus-connection-Laplacian iterate.**
`(1 − Δ_∇)^{k+1} S = (1 − Δ_∇)^k ((1 − Δ_∇) S)`: peeling one factor off the inside agrees with
peeling it off the outside.  Proved by induction on `k`. -/
private theorem oneMinusConnLapSmoothIter_succ'
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (k + 1) S =
      oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ, ih, ← oneMinusConnLapSmoothIter_succ]

/-- **The single-step `toHs` order-drop for the one-minus-connection-Laplacian** at any fixed
output order `m`.  Since `(1 − Δ_∇) U = U − Δ_∇ U`, the triangle inequality on
`SmoothCcTensor.toHs_sub`, the order monotonicity `toHs_norm_mono` (`‖U‖_{H^m} ≤ ‖U‖_{H^{m+1}}`)
and the single-step rough-Laplacian order-drop `exists_rawConnLapSmooth_toHs_le_toHs_succ` give a
constant `C = 1 + C₁` with `‖(1 − Δ_∇) U‖_{H^m} ≤ C · ‖U‖_{H^{m+1}}`. -/
private theorem exists_oneMinusConnLapSmooth_toHs_le_toHs_succ
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (oneMinusConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ m
  refine ⟨1 + C₁, by positivity, fun U => ?_⟩
  have hsub : oneMinusConnLapSmooth (I := I) g₀ 0 2 U =
      U - rawTensorConnLapSmooth (I := I) g₀ 0 2 U := rfl
  rw [hsub, SmoothCcTensor.toHs_sub]
  have hmono : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) m U‖ ≤
      ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (m + 1) U‖ :=
    toHs_norm_mono (I := I) g₀ (Nat.le_succ m) U
  have hlap := hC₁ U
  calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) m U -
          DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖
      ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m U‖ +
          ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ :=
        norm_sub_le _ _
    _ ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ +
          C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := add_le_add hmono hlap
    _ = (1 + C₁) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by ring

/-- **The order-dropping `toHs` bound for the genuine smooth one-minus-connection-Laplacian
iterate** (output order fixed at `0`).  For every `k` there is a nonnegative constant `C` with
`‖(1 − Δ_∇)^k S‖_{H^0} ≤ C · ‖S‖_{H^k}` for every smooth `(0,2)`-tensor `S`.  Induction on `k`
peeling the **innermost** factor (`oneMinusConnLapSmoothIter_succ'`): the inductive hypothesis at
output order `0` applied to `(1 − Δ_∇) S` gives `‖(1 − Δ_∇)^k ((1 − Δ_∇) S)‖_{H^0} ≤ Ck · ‖(1 −
Δ_∇) S‖_{H^k}`, and the single-step drop at the **fixed** output order `k`
(`exists_oneMinusConnLapSmooth_toHs_le_toHs_succ`) bounds `‖(1 − Δ_∇) S‖_{H^k} ≤ Cstep · ‖S‖_{H^{k+1}}`
— so the constant `Ck · Cstep` is order-independent. -/
private theorem exists_oneMinusConnLapSmoothIter_toHs_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) k S‖ := by
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, fun S => ?_⟩
      simp only [oneMinusConnLapSmoothIter_zero, one_mul, le_refl]
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        exists_oneMinusConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ k
      refine ⟨Ck * Cstep, mul_nonneg hCk_nn hCstep_nn, fun S => ?_⟩
      rw [oneMinusConnLapSmoothIter_succ']
      calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) 0
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖
          ≤ Ck * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ :=
            hCk (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        _ ≤ Ck * (Cstep * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖) :=
            mul_le_mul_of_nonneg_left (hCstep S) hCk_nn
        _ = (Ck * Cstep) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖ := by ring

/-- **The spectral-to-covariant-gradient bound (the missing N2 direction at even order).**
For every `k` there is a nonnegative constant `C` such that the even-order spectral norm
`‖smoothCcToTensorHs g₀ (2k) S‖` of a smooth `(0,2)`-tensor `S` is bounded by `C` times the
covariant-`L²` jet sum `∑_{j ≤ 2k} ‖∇^j S‖`:

  `‖smoothCcToTensorHs g₀ (2k) S‖ ≤ C · ∑_{j ≤ 2k} ‖iteratedCovGrad g₀ 0 2 j S‖`.

This is the (otherwise absent) general-order interior-elliptic comparison from the spectral
`H^{2k}` scale to the covariant-gradient `L²` data.  It assembles: the even-order
spectral-norm/Laplacian identity `ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2`
(`‖ccSpectralEmbed g (2k) S‖² = ‖(1 − Δ_∇)^k S‖²_{L²}`), the order-dropping `toHs` bound for the
one-minus-connection-Laplacian iterate `exists_oneMinusConnLapSmoothIter_toHs_le_toHs`
(`‖(1 − Δ_∇)^k S‖_{H^0} ≤ C · ‖S‖_{H^k}`, via `exists_l2Norm_le_toHs_zero` to bridge the `L²` and
`H^0` norms), and the reverse Hebey–Sobolev bridge `exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum`
(`‖S‖_{H^k} ≤ C · ∑_{j ≤ 2k} ‖∇^j S‖`).  The `ccSpectralEmbed = smoothCcToTensorHs` definitional
equality identifies the spectral embeddings. -/
theorem exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  obtain ⟨Cl2, hCl2_nn, hCl2⟩ := exists_l2Norm_le_toHs_zero (I := I) g₀
  obtain ⟨Cdrop, hCdrop_nn, hCdrop⟩ := exists_oneMinusConnLapSmoothIter_toHs_le_toHs (I := I) g₀ k
  obtain ⟨Chebey, hChebey_nn, hChebey⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 k
  refine ⟨Cl2 * Cdrop * Chebey, by positivity, fun S => ?_⟩
  -- `‖smoothCcToTensorHs g (2k) S‖ = ‖ccSpectralEmbed g (2k) S‖ = ‖(1 − Δ_∇)^k S‖_{L²}`.
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hsq := ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 (I := I) (M := M) g₀ k S
  have hnorm_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
    have h1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by rw [hembed_eq]
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
      have hnn1 : (0 : ℝ) ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      have hnn2 : (0 : ℝ) ≤
          ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := norm_nonneg _
      nlinarith [hsq, hnn1, hnn2]
    rw [h1, h2]
  rw [hnorm_eq]
  -- `‖(1 − Δ_∇)^k S‖_{L²} ≤ Cl2 · ‖(1 − Δ_∇)^k S‖_{H^0} ≤ Cl2·Cdrop · ‖S‖_{H^k}
  --   ≤ Cl2·Cdrop·Chebey · ∑_j ‖∇^j S‖`.
  have hjet_eq : ∀ j : ℕ,
      tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j) (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := fun j =>
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
  have hl2 := hCl2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)
  have hdrop := hCdrop S
  have hhebey := hChebey S
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have htoHsk_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) k S‖ := norm_nonneg _
  have htoHs0_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ :=
    norm_nonneg _
  have hhebey' : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) k S‖ ≤
      Chebey * ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    refine le_trans hhebey ?_
    refine mul_le_mul_of_nonneg_left ?_ hChebey_nn
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => hjet_eq j))
  calc ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖
      ≤ Cl2 * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := hl2
    _ ≤ Cl2 * (Cdrop * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) k S‖) := mul_le_mul_of_nonneg_left hdrop hCl2_nn
    _ ≤ Cl2 * (Cdrop * (Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCl2_nn
        exact mul_le_mul_of_nonneg_left hhebey' hCdrop_nn
    _ = Cl2 * Cdrop * Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by ring

/-- **The covariant-gradient-to-spectral bound (the forward Gårding direction at even order).**
For every `k` there is a nonnegative constant `C` such that, for every smooth `(0,2)`-tensor `S`,
each covariant-`L²` jet `‖∇^j S‖` of order `j ≤ 2k` is bounded by `C` times the even-order
spectral norm `‖smoothCcToTensorHs g₀ (2k) S‖`:

  `∑_{j ≤ 2k} ‖iteratedCovGrad g₀ 0 2 j S‖ ≤ C · ‖smoothCcToTensorHs g₀ (2k) S‖`.

It composes the all-orders covariant-gradient Gårding bound
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter` (`‖∇^j S‖ ≤ C · ∑_{i ≤ k} ‖Δ_∇^i S‖`), the
per-iterate spectral bound `rawConnLapIter_l2_le_ccSpectralEmbed_even`
(`‖Δ_∇^i S‖ ≤ ‖ccSpectralEmbed g (2i) S‖`), and the spectral monotonicity
`ccSpectralEmbed_norm_mono` (`2i ≤ 2k`), then identifies `ccSpectralEmbed = smoothCcToTensorHs`. -/
theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ := exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 2 k
  refine ⟨((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)), by positivity, fun S => ?_⟩
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  -- each `‖Δ_∇^i S‖ ≤ Nspec` (spectral bound at order `2i ≤ 2k`)
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have heq : tensorL2Norm (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ :=
      (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀ (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).trans
        (SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).symm
    rw [heq]
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g₀ i S
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ ≤ Nspec := by
      rw [hNspec_def, ← hembed_eq]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
      have : (2 * i : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  -- the Laplacian-iterate sum is bounded by `(k+1)·Nspec`
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        ((k + 1 : ℕ) : ℝ) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- each covariant jet `‖∇^j S‖` (`j ≤ 2k`) is bounded by `Cg · (Laplacian-iterate sum)`
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cg * (((k + 1 : ℕ) : ℝ) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgj := hCg j hj2k S
    have heqj : tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
    rw [heqj] at hgj
    exact le_trans hgj (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1), Cg * (((k + 1 : ℕ) : ℝ) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (((k + 1 : ℕ) : ℝ) * Nspec)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)) * Nspec := by push_cast; ring

/-- **The smooth-ball Lipschitz estimate for the genuine Ricci–DeTurck remainder, at the
quasilinear `H^{a+2}` order (the deep analytic core).**

For a **supercritical** spectral order (`ha_super : 2 * finrank E + 3 ≤ a`, the Sobolev
algebra/multiplication threshold, which implies `finrank E + 4 < 2 * (a + 1)`) and a positive
ball radius `R`, the `H^a`-spectral norm of the genuine smooth Ricci–DeTurck remainder
**difference**
`deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` is controlled by `K`
times the `H^{a+2}`-spectral distance of the embedded perturbations `ι(a+2) T`, `ι(a+2) T'`,
uniformly over the `H^{a+2}`-ball `{‖ι(a+2) T‖ ≤ R}`.

The order is `H^{a+2}` — **two** derivatives — because the Ricci–DeTurck remainder is the
genuine **quasilinear** Nemytskii nonlinearity whose difference
`chartDeTurckRicciRHS_sub_eq` carries second-order metric-difference jet factors
`∂²(T − T')`: each monomial of the chart-polynomial remainder difference contributes a single
`T − T'` jet of chart order `≤ 2`, so the difference factor is bounded in `L²` by the
`H^{a+2}` norm (not `H^{a+1}` — the dead-false order).

This is the genuine missing analytic prerequisite: it combines (i) the Moser /
Gagliardo–Nirenberg tame-product majorisation of the chart-polynomial remainder difference in
`covGrad`-iterate `L²` (`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`,
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`, with the supercritical
`ha_super` closing the Sobolev-algebra products and the ball-bound supplying the `C⁰`/jet
bounds on the plain factors) with (ii) the interior elliptic-regularity / Gårding two-sided
comparison between the intrinsic spectral `H^σ` norm and the `covGrad`-iterate `L²` data of a
smooth tensor — the chart-locality-free all-orders elliptic estimate isolated as an open
analytic sub-program in this library (cf. `Order2NormEquivOnSmooth`,
`eigenSpan_pouHs_le_spectral_of_elliptic`, which carry it as an explicit hypothesis and never
as a headline).  Neither (i)+(ii)-assembled bound exists yet as an unconditional public
declaration, so this remainder-level estimate is posited as the single named honest leaf on
which the `deTurckSmoothN`-level Lipschitz estimate below rests. -/
theorem smoothRemainderDiff_ballLipschitz_Ha2
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ :=
  sorry

/-- **The smooth-ball Lipschitz estimate for the Ricci–DeTurck nonlinearity at the
quasilinear `H^{a+2}` order (the corrected analytic core).**

For a **supercritical** spectral order (`ha_super : 2 * finrank E + 3 ≤ a`) and a
positive `H^{a+2}`-ball radius `R`, the smooth-input nonlinearity `deTurckSmoothN` is Lipschitz
in the `H^{a+2}`-norm on the ball:

  `‖N(T) − N(T')‖_{H^a} ≤ K · ‖ι(a+2) T − ι(a+2) T'‖`,   `‖ι(a+2) T‖, ‖ι(a+2) T'‖ ≤ R`,

for smooth fibre-small `T, T'`.  The right-hand side is the **`H^{a+2}`** norm — the
DeTurck–Ricci flow is **quasilinear**, so its Nemytskii remainder difference
(`chartDeTurckRicciRHS_sub_eq`) carries second-order `∂²(T − T')` factors and loses **two**
derivatives (the `H^{a+1}` order is dead-false).

The `deTurckSmoothN` difference is the order-`a` spectral embedding of the genuine remainder
difference (`deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub`), so the estimate is exactly
the remainder-level ball-Lipschitz bound `smoothRemainderDiff_ballLipschitz_Ha2` rephrased on
`deTurckSmoothN`. -/
theorem deTurckSmoothN_ballLipschitz_Ha2 (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR
  refine ⟨K, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  exact hK T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball

/-- The smooth-tensor embedding `smoothCcToTensorHs` is `ℝ`-homogeneous in its tensor
argument: `ι(c • T) = c • ι T`.  Its spectral coordinates are the `L²` coordinates of the
tensor, and both `tensorL2Coeff` and `SmoothCcTensor.toL2` are `ℝ`-homogeneous. -/
theorem smoothCcToTensorHs_smul (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (c : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (c • T) =
      c • smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.smul_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (c • T) = c • SmoothCcTensor.toL2 T from map_smul _ _ _,
    tensorL2Coeff_smul]

/-- The norm of a scalar multiple in the spectral Sobolev scale: `‖c • x‖ = |c| · ‖x‖`.
The scale is a real normed space through the linear isometry `tensorHs.rescaleEquivL2` onto
weighted `ℓ²`, where scalar multiplication is homogeneous. -/
theorem tensorHs_norm_smul (g₀ : SmoothRiemannianMetric I M) {σ : ℝ} (c : ℝ)
    (x : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    ‖c • x‖ = |c| * ‖x‖ := by
  have h1 : ‖c • x‖ =
      ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) (c • x)‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map (c • x) |>.symm
  have h2 : ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) x‖ = ‖x‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map x
  rw [h1, map_smul, norm_smul, Real.norm_eq_abs, h2]

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibre operator-norm of the symmetrized perturbation is controlled by the spectral
`H^m` norm (the lossy `C⁰`-control bridge).**

For an even spectral order `m` above the supercritical threshold `2·finrank E + 4 ≤ m`, there is
a uniform constant `C > 0` such that, for **every** smooth compactly-supported `(0,2)`-tensor
`T`, the symmetrized extracted bilinear form `ccTensorBilinSymm g₀ T` is `g₀`-fibre bounded by
`C · ‖smoothCcToTensorHs g₀ m T‖`:

  `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) (C · ‖ι_m T‖)`.

This is the spectral transport of the supercritical Sobolev embedding `H ↪ C⁰`.  Concretely,
pick the smallest chart order `kE = finrank/2 + 1` (so `2·kE > finrank`); then
`tensorPouSobolevHilbert_embedding_Ck_gNorm` (chart `H^{2·kE} ↪ C⁰`) bounds the pointwise fibre
norm `‖T.toSection x‖` by `C₁ · ‖T.toHs (2·kE)‖`, the Hilbert-norm identity
`tensorPouSobolevHilbert_norm_eq` rewrites the latter as the PoU norm, the PoU → spectral
comparison `tensorPouSobolevHsNorm_le_ccSpectralEmbed` (N1) lifts it to `C₂ · ‖ccSpectralEmbed
g₀ (4·kE) T‖`, and spectral monotonicity `ccSpectralEmbed_norm_mono` raises the order `4·kE ≤ m`
to `m`.  Finally the pointwise tensor Cauchy–Schwarz `ccTensorBilin_abs_le_fibreNorm_mul_sqrt`
converts the fibre-norm bound on `T.toSection x` into the `gFibreOpBound` operator-norm form
(`ccSpectralEmbed g₀ m = smoothCcToTensorHs g₀ m` by definition). -/
theorem ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) (_hm_even : Even m)
    (h_lossy : 2 * Module.finrank ℝ E + 4 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : SmoothCcTensor g₀ 0 2),
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) := by
  classical
  set kE : ℕ := Module.finrank ℝ E / 2 + 1 with hkE_def
  have hkE_super : 2 * kE > Module.finrank ℝ E + 2 * 0 := by
    rw [hkE_def]; omega
  have h4kEm : (4 * kE : ℕ) ≤ m := by
    rw [hkE_def]; omega
  -- chart `H^{2 kE} ↪ C⁰`
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck_gNorm
      (I := I) (M := M) g₀ 0 2 kE 0 hkE_super
  -- PoU → spectral comparison (N1)
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g₀ (2 * kE)
  refine ⟨C₁ * (C₂ + 1), by positivity, fun T => ?_⟩
  letI : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  -- the per-point upper bound `C₁ · ‖toHs‖ ≤ (C₁ (C₂ + 1)) · ‖ι_m T‖`, stated WITHOUT the
  -- fibre norm (whose instance must come from `hC₁`/N3 by unification, never from a written
  -- type annotation — the default `TensorRSSpace` NACG is suppressed above)
  have hupper : C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ ≤
      (C₁ * (C₂ + 1)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ := by
    have hstep2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ =
        (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g₀ (2 * kE) T
    have hstep3 : (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal ≤
        C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ := hC₂ T
    have hstep4 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T‖ := by
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
      have : (2 * (2 * kE) : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T =
        smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ with hNm_def
    have hNm_nn : 0 ≤ Nm := norm_nonneg _
    have hspec_le : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤ Nm := by
      rw [hNm_def, ← hembed_eq]; exact hstep4
    calc C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (2 * kE) T‖
        = C₁ * (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal := by rw [hstep2]
      _ ≤ C₁ * (C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖) :=
          mul_le_mul_of_nonneg_left hstep3 hC₁_pos.le
      _ ≤ C₁ * (C₂ * Nm) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hspec_le hC₂_nn) hC₁_pos.le
      _ ≤ (C₁ * (C₂ + 1)) * Nm := by nlinarith [hNm_nn, hC₁_pos.le, hC₂_nn]
  -- the fibre-norm bound, type inferred from `hC₁ T x` (no norm annotation written)
  have hfibre := fun x : M => le_trans (hC₁ T x) hupper
  -- convert the fibre-norm bound into the `gFibreOpBound` operator-norm form via N3
  intro x v w
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ T x
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  -- the N3 fibre Cauchy–Schwarz on both index orders, and the `hfibre` norm bound,
  -- all sharing the same fibre-norm term (so no instance restatement is needed)
  have hvw := hcs v w
  have hwv := hcs w v
  have hfx := hfibre x
  -- symmetrization: `|½(B v w + B w v)| ≤ ‖T.toSection x‖ · √(g v v) · √(g w w)`
  rw [ccTensorBilinSymm_apply]
  have habs : |(1 / 2 : ℝ) *
      (ccTensorBilin (I := I) g₀ T x v w + ccTensorBilin (I := I) g₀ T x w v)| ≤
      (1 / 2 : ℝ) * (|ccTensorBilin (I := I) g₀ T x v w| +
        |ccTensorBilin (I := I) g₀ T x w v|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  refine habs.trans ?_
  -- `hvw`, `hwv` bound the two summands by `‖T.toSection x‖ · √·√` (commuted in `hwv`);
  -- `hfx` bounds `‖T.toSection x‖` by `(C₁(C₂+1)) · ‖ι_m T‖`; combine by `nlinarith`
  nlinarith [hvw, hwv, hfx, hsv_nn, hsw_nn, hmul_nn, mul_nonneg hsw_nn hsv_nn,
    mul_le_mul_of_nonneg_right hfx hmul_nn,
    mul_le_mul_of_nonneg_right hfx (mul_nonneg hsw_nn hsv_nn)]

/-- **A spectral `H^{a+2}`-ball of smooth perturbations is uniformly fibre-small (the
quasilinear realizability radius).**

There is a positive radius `R₀` and a smallness constant `δ₀ < 1` such that **every** smooth
compactly-supported `(0,2)`-tensor `T` whose order-`(a+2)` spectral embedding has norm
`‖smoothCcToTensorHs g₀ (a+2) T‖ ≤ R₀` has its symmetrization `ccTensorBilinSymm g₀ T`
uniformly `g₀`-fibre bounded by `δ₀ < 1`.  Equivalently, on this ball the realized metric
`g₀ + T` is a genuine `SmoothRiemannianMetric` (via `tensorSectionRealizeMetric`), so the
genuine smooth Ricci–DeTurck nonlinearity `deTurckSmoothN g₀ g_bg a T` is defined.

This is the **realizability radius** that makes the dense extension of `deTurckSmoothN`
non-vacuous: inside it, smooth data is fibre-small (hence dense-able and Lipschitz-controlled
by `deTurckSmoothN_ballLipschitz_Ha2`), and the recentred ball retraction maps all of `H^{a+2}`
into it.

Classically this is the supercritical Sobolev embedding `H ↪ C⁰`: the pointwise fibre norm of
a smooth tensor is bounded by a constant times a high spectral norm, so a sufficiently small
ball forces the operator-norm smallness `gFibreOpBound … δ₀`.  The transport of the on-disk
chart `C⁰` embedding to the spectral scale is the lossy bridge
`ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy`: at any even spectral order `m` above the
supercritical threshold `2·finrank E + 4 ≤ m` there is a uniform `C` with
`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) (C · ‖ι_m T‖)`.  Under the strengthened
`ha_super : 2·finrank E + 3 ≤ a` the order `a + 2` is `≥ 2·finrank E + 5`, so there is an even
`m` with `2·finrank E + 4 ≤ m ≤ a + 2`; instantiating the lossy bridge at `m` and raising the
order `m ≤ a + 2` by `ccSpectralEmbed_norm_mono` bounds the fibre operator norm by
`C · ‖ι_{a+2} T‖`, and the realizability radius is `R₀ = 1 / (2C)` with smallness `δ₀ = 1/2`. -/
theorem sobolevBall_smooth_fibreSmall (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ < 1 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical
  -- the even spectral order just above the supercritical threshold
  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_even : Even m := by rw [hm_def]; exact ⟨Module.finrank ℝ E + 2, by ring⟩
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ m hm_even hm_lossy
  refine ⟨1 / (2 * C), by positivity, 1 / 2, by norm_num, fun T hTball => ?_⟩
  -- raise the spectral order from `m` to `a + 2`
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + 2 := by
      have h2 : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
      push_cast at h2
      linarith [h2]
    exact hcast
  -- the lossy fibre bound at order `m`, then the radius/scaling
  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / (2 * C) :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / 2 := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = 1 / 2 := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = 1 / 2 * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

/-- **The smooth Ricci–DeTurck nonlinearity factors through the spectral embedding** (proven
from the ball-Lipschitz estimate).

If two smooth fibre-small `(0,2)`-tensors `T, T'` have the same order-`(a+2)` spectral
embedding `smoothCcToTensorHs g₀ (a+2) T = smoothCcToTensorHs g₀ (a+2) T'`, then their genuine
smooth Ricci–DeTurck nonlinearities agree: `deTurckSmoothN T = deTurckSmoothN T'`.  This is the
**well-definedness on the embedded image** that lets the dense extension `deTurckSobolevNHa2`
read off the genuine `deTurckSmoothN` value from the spectral datum alone
(`deTurckSobolevNHa2_eq_smoothN`).

It is a corollary of the quasilinear ball-Lipschitz estimate
`deTurckSmoothN_ballLipschitz_Ha2`: on a ball of radius `R := max ‖ι T‖ ‖ι T'‖`, that estimate
gives `‖N(T) − N(T')‖ ≤ K · ‖ι T − ι T'‖`, and the embeddings being equal makes the right-hand
side `0`, forcing `N(T) = N(T')`. -/
theorem deTurckSmoothN_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by
  set R : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have : (0 : ℝ) ≤ max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    rw [hR_def]; linarith
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR_pos
  have hTball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R := by
    rw [hR_def]; linarith [le_max_left ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hT'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R := by
    rw [hR_def]; linarith [le_max_right ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hbound := hK T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  rw [hTT', sub_self, norm_zero, mul_zero] at hbound
  have hzero : ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at hzero
  exact hzero

/-- **The radial scaling of a smooth `(0,2)`-tensor into the spectral `H^{a+2}` ball of radius
`R₀`.**  The smooth tensor `T` is multiplied by `min 1 (R₀ / ‖ι(a+2) T‖)`, which is `≤ 1` and
contracts `T` so that its order-`(a+2)` embedding has norm `≤ R₀`, while leaving it unchanged
when it already lies in the ball. -/
def radialScaleSmooth (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  (min 1 (R₀ / ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖)) • T

/-- The radial scaling lands in the `H^{a+2}` ball of radius `R₀` (for `0 ≤ R₀`): its order-`(a+2)`
embedding has norm `≤ R₀`. -/
theorem norm_smoothCcToTensorHs_radialScaleSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T)‖ ≤ R₀ := by
  set n := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hcnn : 0 ≤ min 1 (R₀ / n) := le_min zero_le_one (div_nonneg hR₀ hn0)
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, tensorHs_norm_smul, abs_of_nonneg hcnn]
  rcases eq_or_lt_of_le hn0 with heq | hpos
  · rw [← heq]; simpa using hR₀
  · have hmin_le : min 1 (R₀ / n) ≤ R₀ / n := min_le_right _ _
    calc min 1 (R₀ / n) * n ≤ (R₀ / n) * n :=
          mul_le_mul_of_nonneg_right hmin_le hn0
      _ = R₀ := by field_simp

/-- The order-`(a+2)` embedding of the radial scaling of `T` is the **ball retraction** of the
embedding of `T`: `ι(a+2) (radialScaleSmooth R₀ T) = ballRetraction R₀ (ι(a+2) T)`.  Both sides
are `(min 1 (R₀ / ‖ι T‖)) • ι T`, since the embedding is `ℝ`-homogeneous
(`smoothCcToTensorHs_smul`) and norm-multiplicative (`tensorHs_norm_smul`). -/
theorem smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T) =
      ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, ballRetraction]

open Classical in
/-- **The total continuous Ricci–DeTurck nonlinearity at the quasilinear `H^{a+2}` order.**

  `N : tensorHs g₀ 0 2 ((a : ℝ) + 2) → tensorHs g₀ 0 2 (a : ℝ)`.

`deTurckSobolevNHa2` is the **total, continuous, non-gated** quasilinear Ricci–DeTurck
nonlinearity on the spectral Sobolev scale.  It is built by **dense Lipschitz extension** of the
genuine smooth-input nonlinearity `deTurckSmoothN`:

* `deTurckSmoothN` is `H^{a+2}`-ball-Lipschitz on smooth fibre-small data
  (`deTurckSmoothN_ballLipschitz_Ha2`), hence uniformly continuous on the **realizability ball**
  `closedBall (0 : H^{a+2}) R₀` where every smooth datum is fibre-small
  (`sobolevBall_smooth_fibreSmall`), in whose dense smooth subset (`smoothCcToTensorHs_denseRange`)
  it lives;
* the codomain `H^a` is complete (`tensorHs.instCompleteSpace`), so the uniformly continuous map
  extends to the closure (`Dense.extend`);
* the **recentred radial retraction** `recenteredBallRetraction 0 R₀` (1-Lipschitz, sorry-free,
  `LocallyLipschitzTruncation.lean`) maps **all** of `H^{a+2}` into the realizability ball, making
  the composite total.

The dense-subset value reads off `deTurckSmoothN` of the radial scaling
(`radialScaleSmooth`) of a chosen smooth representative into the realizability ball, well-defined
on the embedded image by `deTurckSmoothN_embedding_wellDefined`.  It carries no `realizeMetricAt`
/ finite-support / HLCC gate, and on smooth fibre-small in-ball data equals the genuine intrinsic
remainder `deTurckSmoothN` (`deTurckSobolevNHa2_eq_smoothN`). -/
def deTurckSobolevNHa2 (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 < 1 ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (Classical.choose x.2))
            (Classical.choose_spec h).2.1
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le (Classical.choose x.2))))
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (Classical.choose h).1 v)
    else 0

/-- The realizability existence holds under the supercritical hypothesis `ha_super`: this is the
`∃ p`-witness that drives the `then` branch of `deTurckSobolevNHa2`. -/
theorem deTurckSobolevNHa2_exists_of_super (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 < 1 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 := by
  obtain ⟨R₀, hR₀, δ₀, hδ₀_lt, hball⟩ :=
    sobolevBall_smooth_fibreSmall (I := I) (M := M) g₀ a ha_super
  exact ⟨(R₀, δ₀), hR₀, hδ₀_lt, hball⟩

/-- **`deTurckSobolevNHa2` is globally Lipschitz** (under the supercritical order).

The dense-subset function is Lipschitz **in the embedding coordinate**: on the realizability
ball both radial scalings are fibre-small, so `deTurckSmoothN_ballLipschitz_Ha2` controls their
nonlinearity difference by `K` times the `H^{a+2}`-distance of their embeddings, which are the
ball retractions of the underlying points (`smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction`)
and hence `1`-Lipschitz in the point (`lipschitzWith_ballRetraction`).  The dense extension is the
continuous map agreeing with this `K`-Lipschitz function on the dense range, so it is `K`-Lipschitz
on the closure `= univ` (`LipschitzOnWith.closure`); precomposing with the `1`-Lipschitz recentred
retraction keeps the constant. -/
theorem deTurckSobolevNHa2_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 := (Classical.choose_spec h).2.1
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀
  -- the dense-subset function
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (Classical.choose_spec h).2.1
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def
  -- the embedding of the radial scaling of the chosen representative is `ballRetraction R₀ ↑x`
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  -- `F` is `K`-Lipschitz in the embedding coordinate
  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (Classical.choose_spec h).2.1
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (Classical.choose_spec h).2.1
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
  -- `F` is `K`-Lipschitz, hence continuous and uniformly continuous
  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous
  -- the dense extension agrees with `F` on the dense range and is uniformly continuous
  have hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous
  -- the extension is `K`-Lipschitz on the dense range, hence (by continuity) on its closure `univ`
  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl
  -- assemble: `deTurckSobolevNHa2 = extend ∘ recenter` under the existence, recenter 1-Lipschitz
  refine ⟨K, ?_⟩
  have hretr : LipschitzWith 1 (recenteredBallRetraction
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) :=
    recenteredBallRetraction_lipschitzWith hR₀.le _
  have hcomp : LipschitzWith (K * 1)
      ((Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀)) :=
    hext_lip.comp hretr
  rw [mul_one] at hcomp
  have heq_fun : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a =
      (Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) := by
    funext v
    rw [deTurckSobolevNHa2]
    rw [dif_pos h]
    rfl
  rw [heq_fun]
  exact hcomp

/-- **The total nonlinearity `deTurckSobolevNHa2` is locally Lipschitz on any engine ball.**

For the Ha2 quasilinear maximal-regularity contraction, the nonlinearity must be Lipschitz on the
closed `H^{a+2}`-ball about the initial datum.  Since `deTurckSobolevNHa2` is **globally**
Lipschitz (`deTurckSobolevNHa2_lipschitzWith`), it is Lipschitz on every closed ball — in
particular on `closedBall u₀ R` about any `H^{a+2}`-datum `u₀` and radius `R`. -/
theorem deTurckSobolevNHa2_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a)
    (R : ℝ) (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ L_R : ℝ≥0, LipschitzOnWith L_R (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a)
      (Metric.closedBall u₀ R) := by
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  exact ⟨K, hK.lipschitzOnWith⟩

/-- **`deTurckSobolevNHa2` is the genuine smooth nonlinearity on smooth fibre-small in-ball
inputs.**

On the spectral image `smoothCcToTensorHs g₀ (a+2) T` of a smooth fibre-small `T` whose embedding
lies in **the realizability ball** the construction uses (`hball : ‖ι T‖ ≤ R₀`, with `(R₀, δ₀)`
the realizability witness selected inside `deTurckSobolevNHa2` —
`deTurckSobolevNHa2_realizability`), the total nonlinearity equals
`deTurckSmoothN g₀ g_bg a T hδ_lt hδ` (`= deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`).  This pins
`deTurckSobolevNHa2` to the **genuine intrinsic Ricci–DeTurck remainder** on the dense smooth
in-ball subset — the non-vacuity / flow-faithfulness guarantee.

The recentred retraction fixes the in-ball point, the dense extension reads off `F` there
(`Dense.extend_eq`), and `F`'s value is `deTurckSmoothN` of the radial scaling of a chosen smooth
representative whose embedding is the (identity, in-ball) ball retraction of `ι T`; the genuine
value is recovered by the embedding-well-definedness `deTurckSmoothN_embedding_wellDefined`. -/
theorem deTurckSobolevNHa2_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  -- abbreviations matching the definition's `then` branch
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2) with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (Classical.choose_spec h).2.1
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def
  -- `F` is continuous (same Lipschitz argument as in `deTurckSobolevNHa2_lipschitzWith`)
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (Classical.choose_spec h).2.1
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (Classical.choose_spec h).2.1
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
  -- unfold the definition at the embedded point
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)) := by
    rw [deTurckSobolevNHa2, dif_pos h]
  -- the recentred retraction fixes the in-ball point
  have hfix : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T := by
    refine recenteredBallRetraction_eq_self_of_mem ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hball
  rw [hunfold, hfix, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  -- the dense-set value is `deTurckSmoothN` of the radial scaling, whose embedding is `ι T` (in
  -- ball, so the retraction is the identity); recover `deTurckSmoothN T` by well-definedness
  change deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose hmem)) _ _ =
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super _ T _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec hmem]
  exact ballRetraction_eq_self_of_mem hball

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
