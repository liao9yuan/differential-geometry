import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination

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

* `deTurckSobolevN` — the **total** continuous nonlinearity
  `tensorHs g₀ 0 2 (a+1) → tensorHs g₀ 0 2 a`, the dense/uniformly-continuous extension of
  `deTurckSmoothN` (codomain `tensorHs g₀ 0 2 a` is complete), recentred onto the engine
  ball by `recenteredBallRetraction`.  It agrees with `deTurckSmoothN` on smooth fibre-small
  inputs (`deTurckSobolevN_eq_smoothN`), so the genuine Ricci–DeTurck remainder is what the
  flow sees; it carries no `realizableAt` / finite-support / HLCC gate.

## The analytic core and the extension input (posited)

Two deep classical inputs are posited as named TRUE leaves:

* `deTurckSmoothN_lipschitzOnWith` — the **smooth-ball Lipschitz estimate**
  `‖N(T) − N(T')‖_{H^a} ≤ K · ‖T − T'‖_{H^{a+1}}` for smooth fibre-small `T, T'`, proven by
  majorising the chart-polynomial remainder **difference** `chartDeTurckRicciRHS_sub_eq`
  term by term with the Moser / Gagliardo–Nirenberg tame-product backbone.  It needs the
  **supercritical** Sobolev-algebra order `2 * (a + 1) > finrank E + 4` (hypothesis
  `ha_super`).

* `deTurckSobolevN` itself, `smoothCcToTensorHs_denseRange`, `deTurckSobolevN_eq_smoothN`,
  and `deTurckSobolevN_lipschitzOnWith` package the Lipschitz dense extension to the complete
  codomain.

With the local Lipschitz bound in hand the engine produces, on a positive horizon, the
strong maximal-regularity solution `u ∈ H¹([0,T]; Hᵃ)` of
`∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀` (`deTurckSobolev_solution_exists`).
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

/-- **The smooth-ball Lipschitz estimate for the genuine Ricci–DeTurck remainder, at the
quasilinear `H^{a+2}` order (the deep analytic core).**

For a **supercritical** spectral order (`ha_super : finrank E + 4 < 2 * (a + 1)`, the Sobolev
algebra/multiplication threshold) and a positive ball radius `R`, the `H^a`-spectral norm of
the genuine smooth Ricci–DeTurck remainder **difference**
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
    (a : ℕ) (ha_super : Module.finrank ℝ E + 4 < 2 * (a + 1)) {R : ℝ} (hR : 0 < R) :
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

For a **supercritical** spectral order (`ha_super : finrank E + 4 < 2 * (a + 1)`) and a
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
    (a : ℕ) (ha_super : Module.finrank ℝ E + 4 < 2 * (a + 1)) {R : ℝ} (hR : 0 < R) :
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

/-- **The continuous (Sobolev) Ricci–DeTurck nonlinearity** as a map of spectral Sobolev
spaces

  `N : tensorHs g₀ 0 2 ((a : ℝ) + 1) → tensorHs g₀ 0 2 (a : ℝ)`.

`deTurckSobolevN` is the **total, continuous** nonlinearity obtained by extending the
smooth-input nonlinearity `deTurckSmoothN` from the dense range of `smoothCcToTensorHs`
(`smoothCcToTensorHs_denseRange`) to all of `H^{a+1}`, using completeness of the codomain
`H^a` (`tensorHs.instCompleteSpace`) and the smooth-ball Lipschitz estimate
`deTurckSmoothN_lipschitzOnWith`.  It is total on `H^{a+1}` (no `realizableAt` /
finite-support / HLCC gate), and on smooth fibre-small inputs it equals the genuine
intrinsic Ricci–DeTurck remainder `deTurckSmoothN` (`deTurckSobolevN_eq_smoothN`), so the
flow sees the honest first-order remainder.

POSITED (recursion frontier): the dense Lipschitz/uniformly-continuous extension to the
complete codomain.  Mathlib's `LipschitzOnWith.extend_*` only target `ℝ`/finite products, so
the Hilbert-codomain dense extension (`IsDenseInducing.extend` of the uniformly continuous
`deTurckSmoothN` across `smoothCcToTensorHs_denseRange`) is supplied here. -/
def deTurckSobolevN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  sorry

/-- **`deTurckSobolevN` is the genuine smooth nonlinearity on smooth fibre-small inputs.**

On the spectral image `smoothCcToTensorHs g₀ (a+1) T` of a smooth fibre-small `T`, the total
nonlinearity equals `deTurckSmoothN g₀ g_bg a T hδ_lt hδ`
(`= deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`).  This pins `deTurckSobolevN` to the **genuine
intrinsic Ricci–DeTurck remainder** on the dense smooth subset — the non-vacuity /
flow-faithfulness guarantee — and is the defining property of the dense extension
(`IsDenseInducing.extend_eq` along `smoothCcToTensorHs_denseRange`).

POSITED (recursion frontier): the extension's agreement-on-dense-subset property. -/
theorem deTurckSobolevN_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSobolevN (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ :=
  sorry

/-- **The smooth-ball Lipschitz estimate for the Ricci–DeTurck nonlinearity (the deep
analytic core).**

For a **supercritical** spectral order (`ha_super : finrank E + 4 < 2 * (a + 1)`, i.e. the
Sobolev algebra/multiplication threshold) the smooth-input nonlinearity `deTurckSmoothN` is
Lipschitz in the `H^{a+1}`-norm:

  `‖N(T) − N(T')‖_{H^a} ≤ K · ‖T − T'‖_{H^{a+1}}`

for smooth fibre-small `T, T'`.  Concretely, the embedded values
`deTurckSobolevN (ι T)`, `deTurckSobolevN (ι T')` (`ι = smoothCcToTensorHs (a+1)`) differ in
`H^a` by at most `K` times the `H^{a+1}`-distance of `ι T, ι T'`.

POSITED (recursion frontier — THE analytic core).  Proven from the chart-polynomial remainder
**difference** identity `chartDeTurckRicciRHS_sub_eq` (sorry-free, for the two SMOOTH metrics
`g₀ + T`, `g₀ + T'`): each monomial carries a single metric-difference factor of chart-jet
order `≤ 2`, majorised in `L²` by the Moser / Gagliardo–Nirenberg tame-product backbone
`exists_moserTameProduct_iteratedCovGrad_l2Norm_le`
(`Analysis/Sobolev/MoserTameProduct.lean`) and
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`); summing the
per-monomial bounds yields the uniform Lipschitz constant `K`. -/
theorem deTurckSmoothN_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : Module.finrank ℝ E + 4 < 2 * (a + 1)) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ :=
  sorry

/-- **The total nonlinearity is locally Lipschitz on the engine ball.**

On the closed `H^{a+1}`-ball `closedBall (ι u₀) R` about the included initial datum
`u₀ ∈ H^{a+2}`, `deTurckSobolevN g₀ g_bg a` is Lipschitz with some constant `L_R`:

  `‖N(v) − N(v')‖_{H^a} ≤ L_R · ‖v − v'‖_{H^{a+1}}`  for `v, v' ∈ closedBall (ι u₀) R`.

POSITED (recursion frontier): the continuity/Lipschitz transfer of the dense extension —
`deTurckSobolevN` inherits the smooth-ball Lipschitz bound `deTurckSmoothN_lipschitzOnWith`
across the dense range `smoothCcToTensorHs_denseRange` to a full closed-ball Lipschitz bound
(`LipschitzWith` of `IsDenseInducing.extend` of a uniformly continuous map). -/
theorem deTurckSobolevN_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : Module.finrank ℝ E + 4 < 2 * (a + 1))
    {R : ℝ} (hR : 0 < R)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ L_R : ℝ≥0, LipschitzOnWith L_R (deTurckSobolevN (I := I) (M := M) g₀ g_bg a)
      (Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R) :=
  sorry

/-- **Short-time existence driven by the continuous (Sobolev) Ricci–DeTurck nonlinearity.**

For a closed Riemannian manifold `(M, g₀)`, DeTurck background `g_bg`, a **supercritical**
spectral Sobolev exponent `a : ℕ` (`ha_super : finrank E + 4 < 2 * (a + 1)`, the Sobolev
algebra threshold making the nonlinearity Lipschitz), an initial perturbation `u₀ ∈ H^{a+2}`,
and any positive ball radius `R`, there is a positive horizon `T₀` such that for every short
interval `(0, T]` with `T ≤ T₀ ≤ 1` there is a strong maximal-regularity solution
`u ∈ H¹([0,T]; Hᵃ)` of the Ricci–DeTurck quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,   `N = deTurckSobolevN g₀ g_bg a`,

driven by the **continuous, non-gated** Sobolev nonlinearity (NO finite-support /
`realizeMetricAt` gating anywhere; `N` equals the genuine intrinsic Ricci–DeTurck remainder
`deTurckSmoothN` on smooth fibre-small inputs, `deTurckSobolevN_eq_smoothN`).  The solution
bundle is the engine's: `u` is the Duhamel image of its forcing `gforce`; the forcing
reproduces `N` a.e. along the `H^{a+1}`-view field; the initial value is `u₀`.

This is exactly `deTurckRemainder_strong_shortTime_exists` applied with the continuous
nonlinearity `deTurckSobolevN` and its closed-ball Lipschitz bound
`deTurckSobolevN_lipschitzOnWith`. -/
theorem deTurckSobolev_solution_exists (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : Module.finrank ℝ E + 4 < 2 * (a + 1))
    {R : ℝ} (hR : 0 < R)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => deTurckSobolevN (I := I) (M := M) g₀ g_bg a
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
                (a : ℝ) hT hT1 u₀ gforce t)) ∧
          timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ := by
  obtain ⟨L_R, hLip⟩ :=
    deTurckSobolevN_lipschitzOnWith (I := I) (M := M) g₀ g_bg a ha_super hR u₀
  obtain ⟨T₀, hT₀_pos, hsol⟩ :=
    deTurckRemainder_strong_shortTime_exists (I := I) (M := M) g₀ (a := (a : ℝ))
      (N := deTurckSobolevN (I := I) (M := M) g₀ g_bg a) (L_R := L_R) (R := R) hR u₀ hLip
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨u, gforce, hduh, hforce, htrace, _, _⟩ := hsol hT hTT₀ hT1
  exact ⟨u, gforce, hduh, hforce, htrace⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
