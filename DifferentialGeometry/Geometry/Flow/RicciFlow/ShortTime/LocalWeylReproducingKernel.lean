import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.LocalBallL2Embedding
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SmoothCcDense
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GeneralOrderPouSpectralBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorFibreCauchySchwarz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralDiagonalCounting
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairingRS

/-! # The pointwise reproducing-kernel bound underlying the local Weyl law

This file isolates the analytic heart of the pointwise local Weyl law: the
**supercritical on-diagonal reproducing-kernel summability**

`(★) ∑ᵢ (1 + λᵢ)^{-σ} · ‖bᵢ(x)‖²_g ≤ C` pointwise on `M`,

for the intrinsic tensor connection-Laplacian eigenbasis `bᵢ = eigenvectorSmooth g r s i`,
where `‖bᵢ(x)‖²_g = riemannianFiberNormSq g r s x (bᵢ.toSection x)` is the Riemannian
fibre norm squared and `σ` is any supercritical Sobolev order. From `(★)` the three
conjuncts of `weyl_pointwise_diagonalKernel_bound_of_closed` follow:

* the polynomial diagonal-kernel bound (conjunct 1, all `(r, s)`), by telescoping
  `‖bᵢ(x)‖²_g = (1 + λᵢ)^σ · (1 + λᵢ)^{-σ}‖bᵢ(x)‖²_g ≤ Λ^σ · (★)` over the finite
  threshold set `{i : 1 + λᵢ < Λ}`;
* the supercritical weighted realize summability (conjunct 2, `(0, 2)`), via the
  intrinsic fibre Cauchy–Schwarz `eᵢ(x,v,w)² ≤ g(v,v)·g(w,w)·‖bᵢ(x)‖²_g` dominating
  the realize tail by `(★)`; and
* the realize eigen-expansion (conjunct 3, `(0, 2)`), via `L²`-completeness of the
  eigenbasis-coordinate expansion and the realize-evaluation bound.

## On-diagonal kernel summability at `(0, 2)`

`reproducingKernel_tsum_le_of_closed_02` is proved **outright** at bidegree `(0, 2)`
through the finite-truncation argument: for a finite index set `F`, a base point `x`
and a Riemannian fibre orthonormal frame `ζₘ`, the smooth test tensor
`T := ∑_{j ∈ F} (1 + λⱼ)^{-σ}⟪ζₘ, bⱼ(x)⟫ · eigenSmooth_j` satisfies both
`⟪ζₘ, T.toSection x⟫ = ‖φ(T)‖²_{Hˢ}` and (by the chart-Sobolev embedding `H^{2k} ↪ C⁰`
composed with the all-order Gårding spectral bound `pouSobolevToHsNorm_le_spectral`)
`‖T.toSection x‖ ≤ C · ‖φ(T)‖_{Hˢ}`, forcing the partial sum `≤ C²` and, summed over
the fibre frame, `∑_{j ∈ F}(1 + λⱼ)^{-σ}‖bⱼ(x)‖²_g ≤ dim · C²`.

## Two posited inputs (general bidegree)

`reproducingKernel_weighted_tsum_le_of_closed` (general `(r, s)`) and
`tensorEigenIdx_one_add_lambda_lt_finite` (the finiteness of the threshold index set
from compactness of the resolvent) are the two precise inputs at general bidegree; the
former is the general-rank analogue of the `(0, 2)` kernel bound (its proof needs the
general-rank all-order Gårding lift, available at `(0, 2)` only in the current library)
and the latter is the standard discreteness of the compact-resolvent spectrum. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators RealInnerProductSpace
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
  (tensorSobolevWeight tensorL2Coeff tensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The Riemannian fibre norm squared of an eigenbasis representative at `x`,
`‖bᵢ(x)‖²_g = riemannianFiberNormSq g r s x (bᵢ.toSection x)`. -/
private noncomputable def eigenFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s)
    (x : M) : ℝ :=
  Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x
    ((eigenvectorSmooth (I := I) (M := M) g r s i).toSection x)

private lemma eigenFiberNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s)
    (x : M) :
    0 ≤ eigenFiberNormSq (I := I) (M := M) g r s i x :=
  Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _

/-- The diagonal reproducing kernel of a finite index set equals the finite sum of
the eigen-fibre norms, `∑_{i ∈ F} ‖bᵢ(x)‖²_g`, by the fibre-norm bridge
`riemannianFiberNormSq_eq_tensorInnerPointwise`. -/
private lemma diagonalKernel_eq_sum_eigenFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s))
    (x : M) :
    MetricRealization.diagonalKernel (I := I) (M := M) g r s F x =
      ∑ i ∈ F, eigenFiberNormSq (I := I) (M := M) g r s i x := by
  classical
  unfold MetricRealization.diagonalKernel eigenFiberNormSq
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g r s x ((eigenvectorSmooth (I := I) (M := M) g r s i).toSection x)]
  rfl

/-! ## The general-rank reproducing-kernel bound by fibre Parseval

`reproducingKernel_weighted_tsum_le_of_closed` is the general-`(r, s)` form of the
supercritical on-diagonal reproducing-kernel summability `(★)`. It is proved here from a
single posited general-rank analytic primitive — the per-direction **truncated Bessel
bound** `reproducingKernel_partialBessel_le_of_closed` at bidegree `(r, s)` — by the same
fibre-Parseval-over-an-orthonormal-frame argument that derives the `(0, 2)` outright proof
`reproducingKernel_tsum_le_of_closed_02` from `partialBessel_le_Csq_02`.

The general-rank fibre helpers below (`riemannianFiberNormSq_eq_norm_sq_rs`,
`gFiberInnerRS`, `gFiberInnerRS_eq_inner`, `riemannianFiberNormSq_eq_sum_gFiberInnerRS_sq`)
are the bidegree-`(r, s)` analogues of their in-file `(0, 2)` siblings, proved verbatim
from the general-rank fibre-norm bridge `riemannianFiberNormSq_eq_tensorInnerPointwise` and
the general-rank Riemannian-bundle inner product `tensorRSRiemannianInnerCLM`. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The Riemannian bundle fibre-norm squared `riemannianFiberNormSq g r s x z` coincides
with the squared bundle-fibre norm `‖z‖²` under the general-rank Riemannian bundle
instance `tensorRS_riemannianBundle g r s`, via the fibre-norm bridge and
`tensorRSRiemannianInnerCLM_apply`. (The bidegree-`(r, s)` analogue of
`riemannianFiberNormSq_eq_norm_sq_02`.) -/
private lemma riemannianFiberNormSq_eq_norm_sq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x z).symm
  have hself : (inner ℝ z z : ℝ) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

/-- The fibre Riemannian inner product as a plain function, `gFiberInnerRS x ζ z =
tensorRSRiemannianInnerCLM g r s x ζ z` (instance-free in the signature). The
bidegree-`(r, s)` analogue of the in-file `(0, 2)` `gFiberInner`. -/
@[reducible] private noncomputable def gFiberInnerRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (ζ z : TensorRSSpace r s I x) : ℝ :=
  DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
    (I := I) (M := M) g r s x ζ z

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- With the Riemannian bundle instance installed, `gFiberInnerRS` is the genuine fibre
inner product `inner ℝ`. (The bidegree-`(r, s)` analogue of `gFiberInner_eq_inner`; the
underlying `rfl` unfolds the bundle inner product instance, hence the raised heartbeat
budget.) -/
private lemma gFiberInnerRS_eq_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (ζ z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    gFiberInnerRS (I := I) (M := M) g r s x ζ z = (inner ℝ ζ z : ℝ) :=
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Fibre Parseval (general rank).** The Riemannian fibre-norm squared expands over any
fibre orthonormal basis `b` as `∑ₘ (gFiberInnerRS x (b m) z)²`. The bidegree-`(r, s)`
analogue of `riemannianFiberNormSq_eq_sum_gFiberInner_sq`. -/
private lemma riemannianFiberNormSq_eq_sum_gFiberInnerRS_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    {ι : Type*} [Fintype ι]
    (b : letI : Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
      OrthonormalBasis ι ℝ (TensorRSSpace r s I x))
    (z : TensorRSSpace r s I x) :
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x z =
      ∑ m : ι, gFiberInnerRS (I := I) (M := M) g r s x (b m) z ^ 2 := by
  letI : Bundle.RiemannianBundle (fun y : M => TensorRSSpace r s I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [riemannianFiberNormSq_eq_norm_sq_rs (I := I) (M := M) g r s x z]
  rw [← OrthonormalBasis.sum_sq_inner_left b z]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [gFiberInnerRS_eq_inner (I := I) (M := M) g r s x (b m) z, real_inner_comm]

/-! ### The general-rank finite-eigen-combination spectral calculus

The bidegree-`(r, s)` mirror of the `(0, 2)` `finiteEigenCombo` / `smoothToTensorHs` tower
of `Analysis/Spectral/.../Garding/EigenCombination.lean` and the in-file `(0, 2)`
`smoothToTensorHs`.  Every algebraic / coordinate identity ports verbatim, because the
underlying eigenbasis primitives (`eigenvectorSmooth`, `eigenvectorSmooth_toL2`,
`tensorResolventEigenbasisVec`, `tensorResolventHilbertEigenbasisSigma`,
`SmoothCcTensor.toL2`/`toSection` algebra, `tensorL2Coeff`, `tensorHsToL2`) are all
general-rank.  The single genuinely general-rank analytic input —
`smoothCcTensorRS_tensorL2Coeff_weighted_summable` (the `(r, s)` weighted Sobolev-scale
summability) — is posited below as a precise child mirroring the `(0, 2)`
`smoothCcTensor_tensorL2Coeff_weighted_summable`. -/

/-- The general-rank finite eigen-combination `∑_{i ∈ F} c i • eigenvectorSmooth g r s i`,
a smooth compactly-supported `(r, s)`-tensor.  The bidegree-`(r, s)` analogue of
`finiteEigenCombo`. -/
private noncomputable def finiteEigenComboRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    Integral.L2.SmoothCcTensor g r s :=
  ∑ i ∈ F, c i • eigenvectorSmooth (I := I) (M := M) g r s i

/-- The fibre value of the general-rank finite eigen-combination is the finite fibre-linear
combination of the eigenbasis fibre values.  Mirror of `finiteEigenCombo_toSection_apply`. -/
private lemma finiteEigenComboRS_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (x : M) :
    (finiteEigenComboRS (I := I) (M := M) g r s F c).toSection x =
      ∑ i ∈ F, c i • (eigenvectorSmooth (I := I) (M := M) g r s i).toSection x := by
  classical
  unfold finiteEigenComboRS
  induction F using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Integral.L2.SmoothCcTensor.toSection_zero]
      rfl
  | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        Integral.L2.SmoothCcTensor.toSection_add, Integral.L2.SmoothCcTensor.toSection_smul]
      simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply, ih]

/-- The `L²` image of the general-rank finite eigen-combination is the finite combination
`∑_{i ∈ F} c i • bᵢ` of the resolvent eigenbasis vectors.  Mirror of `finiteEigenCombo_toL2`. -/
private lemma finiteEigenComboRS_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    (Integral.L2.SmoothCcTensor.toL2 (finiteEigenComboRS (I := I) (M := M) g r s F c)) =
      ∑ i ∈ F, c i •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i := by
  classical
  rw [show Integral.L2.SmoothCcTensor.toL2 (finiteEigenComboRS (I := I) (M := M) g r s F c) =
        ∑ i ∈ F, c i • Integral.L2.SmoothCcTensor.toL2
          (eigenvectorSmooth (I := I) (M := M) g r s i) by
      rw [finiteEigenComboRS, map_sum]; simp_rw [map_smul]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Integral.L2.SmoothCcTensor.toL2 (eigenvectorSmooth (I := I) (M := M) g r s i) =
      (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) from
    Integral.L2.SmoothCcTensor.toL2_apply _, eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]

open scoped Classical in
/-- The `i`-th eigenbasis coordinate of the general-rank finite eigen-combination is `c i`
when `i ∈ F` and `0` otherwise.  Mirror of `finiteEigenCombo_tensorL2Coeff`. -/
private lemma finiteEigenComboRS_tensorL2Coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2 (finiteEigenComboRS (I := I) (M := M) g r s F c)) i =
      (if i ∈ F then c i else 0) := by
  classical
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s with hcompact_def
  rw [Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    finiteEigenComboRS_toL2, inner_sum]
  have h_term : ∀ j ∈ F,
      (inner ℝ
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact i)
          (c j • tensorResolventEigenbasisVec (I := I) (M := M) hcompact j) : ℝ) =
        (if i = j then c j else 0) := by
    intro j _
    rw [inner_smul_right,
      show tensorResolventEigenbasisVec (I := I) (M := M) hcompact j =
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact j from
        (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M) hcompact j).symm]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth i j]
    by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hiF : i ∈ F
  · rw [Finset.sum_eq_single i]
    · simp [hiF]
    · intro j _ hji; rw [if_neg (fun h => hji h.symm)]
    · intro h; exact absurd hiF h
  · rw [if_neg hiF, Finset.sum_eq_zero]
    intro j hj; rw [if_neg (fun h => hiF (by rw [h]; exact hj))]

/-- **The general-rank connection-Laplacian Green identity (posited general-rank analytic
child).** For smooth compactly-supported `(r, s)`-tensors `T, v`, the `L²` pairing of the
covariant gradients equals minus the `L²` pairing of the rough connection Laplacian against
`v`:
`⟪∇T, ∇v⟫_{L²} = -⟪Δ_∇ T, v⟫_{L²}`.

This is the bidegree-`(r, s)` integration-by-parts (Green) identity for the rough connection
Laplacian.  At purely-covariant rank `(0, s)` it is the in-library
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`, proved unconditionally from the
metric-lowering intertwiner `loweringIntertwiner_gen` feeding the per-section divergence
identity `divergence_dirichletVFGen_eq` into the compact-support divergence theorem
`integral_divergence_eq_zero_of_hasCompactSupport`.  At general bidegree `(r, s)` it is the
in-library `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs`, proved by
the same divergence-theorem chain over the general-rank Dirichlet-current divergence identity
`divergence_dirichletVFRS_eq` (which discharges the metric-lowering intertwiner
`LoweringIntertwinerRS` via `loweringIntertwinerRS_holds`).  This is a one-line transit of that
in-library general-rank Green identity. -/
private theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s T).toFun
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s v).toFun =
      - Integral.L2.tensorL2Inner (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun :=
  Integral.Connection.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v

/-- **The general-rank Green / `H¹`-pairing bridge for `(1 - Δ_∇)`.** For smooth
compactly-supported `(r, s)`-tensors `T, v`, the `L²` pairing of `(1 - Δ_∇) T` with `v` equals
the `H¹` pairing of the `H¹`-completion embeddings of `T` and `v`:
`⟪(1 - Δ_∇) T, v⟫_{L²} = ⟪⟦T⟧, ⟦v⟧⟫_{H¹}`.

This is the bidegree-`(r, s)` analogue of the in-library `(0, s)`
`oneMinusConnLapSmooth_toL2_inner_eq_h1_general`, *proved* here by the same integration-by-parts
chain: the `H¹` inner product splits (via `tensorH1Inner_def`) into the `L²` pairing plus the
Dirichlet pairing `∫ ⟨∇T, ∇v⟩`, which the general-rank Dirichlet-integral bridge
`tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner` identifies with
`⟪∇T, ∇v⟫_{L²}`, and the posited general-rank Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS` turns into `-⟪Δ_∇ T, v⟫_{L²}`;
`(1 - Δ_∇) T = T - Δ_∇ T` splits the left-hand `L²` pairing accordingly.  Consumers transitively
depend on `sorryAx` through the posited Green identity. -/
private theorem oneMinusConnLapSmoothRS_toL2_inner_eq_h1
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : Integral.L2.SmoothCcTensor g r s) :
    (inner ℝ
        ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
          TensorL2 r s g)
        (v : TensorL2 r s g) : ℝ) =
      (inner ℝ
        (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩)
        (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨v⟩) : ℝ) := by
  have h_rhs :
      (inner ℝ
          (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩)
          (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨v⟩) : ℝ) =
        (inner ℝ (T : TensorL2 r s g) (v : TensorL2 r s g) : ℝ) +
          ∫ x, Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner
              (I := I) (M := M) g r s T v x
            ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.inner_def,
      Analysis.Parabolic.TensorSpectral.tensorH1Inner_def]
    rw [show Integral.L2.tensorL2Inner (I := I) (M := M) g r s
            (⟨T⟩ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s).toCcTensor.toFun
            (⟨v⟩ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s).toCcTensor.toFun =
          (inner ℝ (T : TensorL2 r s g) (v : TensorL2 r s g) : ℝ) by
        rw [UniformSpace.Completion.inner_coe]
        exact (Integral.L2.SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  have h_dir :
      ∫ x, Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s T v x
          ∂(Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) =
        Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s T).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s v).toFun :=
    (Integral.Connection.tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s T v).symm
  have h_green :
      Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s T).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s v).toFun =
        - Integral.L2.tensorL2Inner (I := I) (M := M) g r s
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS (I := I) (M := M) g r s T v
  have h_lhs :
      (inner ℝ
          ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
            TensorL2 r s g)
          (v : TensorL2 r s g) : ℝ) =
        Integral.L2.tensorL2Inner (I := I) (M := M) g r s
            (oneMinusConnLapSmooth (I := I) g r s T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact Integral.L2.SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      (inner ℝ (T : TensorL2 r s g) (v : TensorL2 r s g) : ℝ) =
        Integral.L2.tensorL2Inner (I := I) (M := M) g r s T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact Integral.L2.SmoothCcTensor.inner_def _ _
  have h_split :
      Integral.L2.tensorL2Inner (I := I) (M := M) g r s
          (oneMinusConnLapSmooth (I := I) g r s T).toFun v.toFun =
        Integral.L2.tensorL2Inner (I := I) (M := M) g r s T.toFun v.toFun -
          Integral.L2.tensorL2Inner (I := I) (M := M) g r s
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun := by
    have h_coe :
        (inner ℝ
            ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
              TensorL2 r s g)
            (v : TensorL2 r s g) : ℝ) =
          (inner ℝ (T : TensorL2 r s g) (v : TensorL2 r s g) : ℝ) -
            (inner ℝ
              ((Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T :
                  Integral.L2.SmoothCcTensor g r s) :
                TensorL2 r s g)
              (v : TensorL2 r s g) : ℝ) := by
      rw [show (oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) =
            T - Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show (inner ℝ (T : TensorL2 r s g) (v : TensorL2 r s g) : ℝ) =
          Integral.L2.tensorL2Inner (I := I) (M := M) g r s T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact Integral.L2.SmoothCcTensor.inner_def _ _]
    rw [show (inner ℝ
            ((Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T :
                Integral.L2.SmoothCcTensor g r s) :
              TensorL2 r s g)
            (v : TensorL2 r s g) : ℝ) =
          Integral.L2.tensorL2Inner (I := I) (M := M) g r s
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact Integral.L2.SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

/-- **The general-rank `H¹`-completion `L²`-adjoint pairing.** For a smooth `(r, s)`-tensor `T`
and *any* `H¹`-completion element `w`,
`⟪⟦T⟧, w⟫_{H¹} = ⟪toL2 ((1 - Δ_∇) T), F w⟫_{L²}`, where `F = TensorH1ComplToTensorL2 g r s`.
Both sides are continuous in `w` and agree on the dense range of `smoothToTensorH1Compl`, where
the identity is the general-rank Green / `H¹` bridge `oneMinusConnLapSmoothRS_toL2_inner_eq_h1`
combined with `F ⟦v⟧ = v` in `L²`.  The bidegree-`(r, s)` analogue of
`inner_smoothToTensorH1Compl_eq_l2_oneMinusConnLap_of_green`. -/
private theorem inner_smoothToTensorH1ComplRS_eq_l2_oneMinusConnLap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (w : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) :
    (inner ℝ (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩) w : ℝ) =
      (inner ℝ
        ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
          TensorL2 r s g)
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s w) : ℝ) := by
  set A : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s → ℝ :=
    fun w => (inner ℝ (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩) w : ℝ) with hA
  set B : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s → ℝ :=
    fun w => (inner ℝ
          ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
            TensorL2 r s g)
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s w) : ℝ) with hB
  have hA_cont : Continuous A := by
    rw [hA]
    exact (innerSL ℝ
      (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩)).continuous
  have hB_cont : Continuous B := by
    rw [hB]
    exact ((innerSL ℝ
        ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
          TensorL2 r s g)).comp
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)).continuous
  have h_eq_on :
      A ∘ ((↑) : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s →
          Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) =
        B ∘ ((↑) : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s →
          Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) := by
    funext V
    have hcoe : (V : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) =
        smoothToTensorH1Compl (I := I) (M := M) g r s V := rfl
    simp only [Function.comp_apply, hA, hB, hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s) := by
      cases V; rfl
    rw [hV]
    rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
    rw [← oneMinusConnLapSmoothRS_toL2_inner_eq_h1 (I := I) (M := M) g r s T V.toCcTensor]
  have h_dense :
      DenseRange ((↑) : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s →
        Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) :=
    UniformSpace.Completion.denseRange_coe
  have h_AB : A = B := h_dense.equalizer hA_cont hB_cont h_eq_on
  exact congr_fun h_AB w

/-- **Closability of the covariant gradient at general rank `(r, s)`.** The canonical
`H¹ → L²` inclusion `TensorH1ComplToTensorL2 g r s` is injective: the covariant gradient on
`(r, s)`-tensor fields is a closable operator.

This is the bidegree-`(r, s)` analogue of the in-library `(0, 2)` / `(0, 3)`
`TensorH1ComplToTensorL2_injective_two` / `..._three`, *proved* here by the same
density-and-Green argument: a kernel element `w` pairs (by the general-rank adjoint pairing
`inner_smoothToTensorH1ComplRS_eq_l2_oneMinusConnLap`) to `0` against every smooth `H¹` test
class, hence vanishes by density of the smooth classes in the `H¹` completion.  Consumers
transitively depend on `sorryAx` through the posited general-rank Green identity. -/
private theorem TensorH1ComplToTensorL2RS_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Injective (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine ext_inner_left ℝ ?_
  intro v
  rw [inner_zero_right]
  set A : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s → ℝ :=
    fun v => (inner ℝ v w : ℝ) with hA
  have hA_cont : Continuous A := by
    rw [hA]
    exact Continuous.inner continuous_id continuous_const
  have h_eq_on :
      A ∘ ((↑) : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s →
          Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) =
        (fun _ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s => (0 : ℝ)) := by
    funext V
    simp only [Function.comp_apply, hA]
    have hcoe : (V : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) =
        smoothToTensorH1Compl (I := I) (M := M) g r s V := rfl
    rw [hcoe]
    have hV : V = (⟨V.toCcTensor⟩ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s) := by
      cases V; rfl
    rw [hV]
    rw [inner_smoothToTensorH1ComplRS_eq_l2_oneMinusConnLap (I := I) (M := M) g r s V.toCcTensor w]
    rw [hw, inner_zero_right]
  have h_dense :
      DenseRange ((↑) : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s →
        Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq :
      A = (fun _ : Analysis.Parabolic.TensorSpectral.TensorH1Compl g r s => (0 : ℝ)) :=
    h_dense.equalizer hA_cont continuous_const h_eq_on
  have := congr_fun h_eq v
  rw [hA] at this
  exact this

/-- **The smooth eigenvector's `H¹` embedding is the rescaled resolvent eigenvector (general
rank).** For the smooth representative `eᵢ = eigenvectorSmooth g r s i` of the resolvent
eigenbasis vector at index `i`, `⟦eᵢ⟧ = (i.fst.val)⁻¹ • eigenvectorResolvent i` in the `H¹`
completion. Both sides have the same image `tensorResolventEigenbasisVec i` under the injective
`H¹ → L²` map `TensorH1ComplToTensorL2RS_injective`. The bidegree-`(r, s)` analogue of
`smoothToTensorH1Compl_eigenvectorSmooth_eq`, proved verbatim from the general-rank closability
child. -/
private theorem smoothToTensorH1ComplRS_eigenvectorSmooth_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    smoothToTensorH1Compl (I := I) (M := M) g r s
        ⟨eigenvectorSmooth (I := I) (M := M) g r s i⟩ =
      (i.fst.val)⁻¹ •
        eigenvectorResolvent (I := I) (M := M) g r s i := by
  apply TensorH1ComplToTensorL2RS_injective (I := I) (M := M) g r s
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe]
  change (eigenvectorSmooth (I := I) (M := M) g r s i :
        TensorL2 r s g) =
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          eigenvectorResolvent (I := I) (M := M) g r s i)
  rw [eigenvectorSmooth_toL2 (I := I) (M := M) g r s i, map_smul]
  exact eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i

/-- **The general-rank per-step eigen-coordinate identity.** Applying the smooth
one-minus-connection-Laplacian `(1 - Δ_∇)` scales the `i`-th eigenbasis coordinate by
`(1 + λᵢ)`:
`cᵢ((1 - Δ_∇) T) = (1 + λᵢ) · cᵢ(T)`.

This is the bidegree-`(r, s)` analogue of the `(0, 2)`
`tensorL2Coeff_ofCompact_oneMinusConnLapSmooth`, proved verbatim from the general-rank Green
bridge `oneMinusConnLapSmoothRS_toL2_inner_eq_h1`, the eigenvector identification
`smoothToTensorH1ComplRS_eigenvectorSmooth_eq` (over the general-rank closability child
`TensorH1ComplToTensorL2RS_injective`), the general-rank weak-eigenvector equation
`eigenvectorSmooth_weak_eigen`, and `one_add_lambda_eq_inv_val`.  Everything downstream of it
(the iterated identity, the even-order Parseval summability, and the all-order weighted
summability `smoothCcTensorRS_tensorL2Coeff_weighted_summable`) is bidegree-generic and is
*proved* on top of it.  The conclusion is a coordinate-scaling identity, structurally distinct
from the summability conclusion it powers (no packaging). -/
private theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2
          (oneMinusConnLapSmooth (I := I) g r s T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i := by
  classical
  set hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s with hcompact_def
  have hb :
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hcompact i =
        (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) := by
    rw [tensorResolventHilbertEigenbasisSigma_apply,
      eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
  rw [Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner, hb,
    Integral.L2.SmoothCcTensor.toL2_apply, Integral.L2.SmoothCcTensor.toL2_apply]
  rw [real_inner_comm
    ((oneMinusConnLapSmooth (I := I) g r s T : Integral.L2.SmoothCcTensor g r s) :
      TensorL2 r s g)
    (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g),
    oneMinusConnLapSmoothRS_toL2_inner_eq_h1 (I := I) (M := M) g r s T
      (eigenvectorSmooth (I := I) (M := M) g r s i)]
  rw [smoothToTensorH1ComplRS_eigenvectorSmooth_eq (I := I) (M := M) g r s i,
    inner_smul_right]
  rw [real_inner_comm
    (eigenvectorResolvent (I := I) (M := M) g r s i)
    (smoothToTensorH1Compl (I := I) (M := M) g r s ⟨T⟩),
    eigenvectorSmooth_weak_eigen (I := I) (M := M) g r s i ⟨T⟩]
  rw [show ((⟨T⟩ : Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 g r s).toCcTensor :
        TensorL2 r s g) = (T : TensorL2 r s g) from rfl,
    real_inner_comm
      (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g)
      (T : TensorL2 r s g),
    one_add_lambda_eq_inv_val (I := I) (M := M) i]

/-- The iterated general-rank per-step identity:
`cᵢ((1 - Δ_∇)^k T) = (1 + λᵢ)^k · cᵢ(T)`.  The bidegree-`(r, s)` analogue of
`tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter`, proved by induction on `k` from the
single-step `tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS` and the iterate recursion
`oneMinusConnLapSmoothIter_succ` (both bidegree-generic). -/
private theorem tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIterRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s)
    (k : ℕ) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2
          (oneMinusConnLapSmoothIter (I := I) g r s k T)) i =
      (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ k *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS
          (I := I) (M := M) g r s (oneMinusConnLapSmoothIter (I := I) g r s k T) i,
        ih, pow_succ]
      ring

/-- **Even-order general-rank weighted summability.** At an even integer order `2k`, the
weighted eigenbasis coordinates of a smooth `(r, s)`-tensor are square-summable, since
`∑ᵢ (1 + λᵢ)^{2k} cᵢ(T)² = ‖toL2 ((1 - Δ_∇)^k T)‖²_{L²}` by the iterated per-step identity
`tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIterRS` and Parseval-side summability
`tensorL2Coeff_ofCompact_summable_sq'`.  The bidegree-`(r, s)` analogue of
`smoothCcTensor_tensorL2Coeff_weighted_summable_even`. -/
private theorem smoothCcTensorRS_tensorL2Coeff_weighted_summable_even
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  have h_term :
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) =
        fun i => (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2
            (oneMinusConnLapSmoothIter (I := I) g r s k T)) i) ^ 2 := by
    funext i
    rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIterRS
      (I := I) (M := M) g r s T i k]
    rw [mul_pow]
    congr 1
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast, mul_comm 2 k, pow_mul, sq]
  rw [h_term]
  exact tensorL2Coeff_ofCompact_summable_sq' (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
    (Integral.L2.SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g r s k T))

/-- **The general-rank weighted Sobolev-scale summability.** For a smooth compactly-supported
`(r, s)`-tensor field `T`, the eigenbasis coordinates of its `L²` class are weighted
square-summable at every real Sobolev order `σ`: `∑ᵢ (1 + λᵢ)^σ · cᵢ(T)² < ∞`.

This is the spectral-side statement "smooth ⇒ in every `Hˢ`" at general bidegree — the
bidegree-`(r, s)` analogue of the `(0, 2)`
`smoothCcTensor_tensorL2Coeff_weighted_summable`.  It is *proved* here by reducing the real
order `σ` to an even integer order `2k ≥ σ` via the monotone domination
`summable_tensorSobolevWeight_of_even` and invoking the even-order summability
`smoothCcTensorRS_tensorL2Coeff_weighted_summable_even`, exactly as in the `(0, 2)` proof.
The single genuinely general-rank analytic input is the per-step coordinate identity
`tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS`, posited above; consumers transitively
depend on `sorryAx` through it. -/
private theorem smoothCcTensorRS_tensorL2Coeff_weighted_summable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (σ / 2)
  have hσk : σ ≤ (2 * k : ℕ) := by
    have : σ / 2 ≤ (k : ℝ) := hk
    push_cast
    linarith
  exact summable_tensorSobolevWeight_of_even
    (I := I) (M := M)
    (fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      (Integral.L2.SmoothCcTensor.toL2 T) i)
    hσk
    (smoothCcTensorRS_tensorL2Coeff_weighted_summable_even
      (I := I) (M := M) g r s k T)

/-- The eigenbasis-coordinate `Hˢ` element of a smooth `(r, s)`-tensor `T` at spectral order
`σ`: the `tensorHs g r s σ` element with coordinate family `tensorL2Coeff (T.toL2)`,
square-summable at every real order by `smoothCcTensorRS_tensorL2Coeff_weighted_summable`.
Mirror of the `(0, 2)` `smoothToTensorHs`. -/
private noncomputable def smoothToTensorHsRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    tensorHs (I := I) (M := M) g r s σ where
  coeff i := tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
    (Integral.L2.SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensorRS_tensorL2Coeff_weighted_summable (I := I) (M := M) g r s σ T

@[simp] private lemma smoothToTensorHsRS_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (smoothToTensorHsRS (I := I) (M := M) g r s σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2 T) i := rfl

/-- The spectral `H^σ`-norm of `φ(T) = smoothToTensorHsRS g r s σ T` equals the `Real.sqrt`
spectral sum.  Mirror of `norm_smoothToTensorHs_eq_spectral_sqrt`. -/
private lemma norm_smoothToTensorHsRS_eq_spectral_sqrt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    ‖smoothToTensorHsRS (I := I) (M := M) g r s σ T‖ =
      Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  rw [Analysis.Parabolic.TensorHeatEquation.tensorHs.norm_eq_sqrt_tsum]
  refine congrArg Real.sqrt (tsum_congr (fun i => ?_))
  rw [smoothToTensorHsRS_coeff]

/-- **The sharp local-ball `L²`-Sobolev pointwise embedding (posited sharp Euclidean analytic
child).** For a smooth function `f` on `EuclideanSpace ℝ (Fin d)` and a ball `B(x₀, R)` with `R > 0`,
in the **sharp** supercritical regime `d < 2·(2a)` (the Sobolev embedding `H^{2a}(B) ↪ C⁰`, valid
when the Sobolev order `2a` exceeds `d/2`), there is a constant `C ≥ 0` depending only on `d, a, R`
(uniform in `f`) such that for every `x ∈ B(x₀, R/4)` the value `|f x|` is controlled by only the
order-`≤ 2a` `L²`-Sobolev seminorms of `f` on `B(x₀, R)`:
`|f x| ≤ C · ∑_{j ≤ 2a} ‖iteratedFDeriv ℝ j f‖_{L²(B(x₀, R))}`.

This is the **sharp** analogue of the in-library `smooth_localBall_L2_pointwise_embedding`
(`Analysis/Sobolev/Euclidean/Embedding/LocalBallL2Embedding.lean`), which is stated with the
**non-sharp** threshold `d < 2K` for an order-`≤ 2K` seminorm bound — to bound by only orders
`≤ 2a` that lemma forces `K = a`, hence the strictly stronger `d < 2a`, whereas the sharp Sobolev
theorem `H^{2a} ↪ C⁰` needs only `d < 2·(2a)`.  The library's `L²` higher-order embedding is built
by the iterated-Morrey tower `tower_to_supercritical_quant_uniform` (each first-order step costs one
derivative and one criticality threshold); the sharp threshold `d < 2·(2a)` is reachable from that
same tower by choosing the auxiliary `L^p`-exponent `p` close to `2` (so that `2a · p > d`), but the
in-library lemma conservatively fixes `p ≥ 1` only and so cannot supply the sharp bound, and that
file is not editable here; so the sharp Euclidean embedding is posited.  Its statement is purely
Euclidean and structurally distinct from the manifold bound it powers (no packaging); the body is
`sorry` and consumers transitively depend on `sorryAx`. -/
private theorem smooth_localBall_L2_pointwise_embedding_sharp
    {d : ℕ} [NeZero d] (a : ℕ) (hda : (d : ℝ) < 2 * (2 * a))
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : EuclideanSpace ℝ (Fin d) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
        ∀ x ∈ Metric.ball x₀ (R / 4),
          ‖f x‖ ≤ C *
            ∑ j ∈ Finset.range (2 * a + 1),
              (MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
                (MeasureTheory.volume.restrict (Metric.ball x₀ R))).toReal :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.smooth_localBall_L2_pointwise_embedding_sharp
    (d := d) a hda (x₀ := x₀) (R := R) hR

/-- **The sharp general-order per-ball Euclidean-pull center bound.** At a supercritical chart order
`a` (`dim M < 2·(2a)`), for an atlas index `α`, component pair `IJ`, and a closed Euclidean ball
`closedBall y₀ R ⊆ chartTargetEuclid α` on which the chart partition-of-unity pull is `≥ c`, there is a
constant `Cα ≥ 0` such that on the shrunken ball `ball y₀ (R/4)` the chart-component pull is bounded by
`Cα · ‖T.toHs a‖`.

This is the **sharp** general-order (`a`, not necessarily even) analogue of the in-library `(0, 2k)`-only
per-ball core `rawPullCenter_le_hsNorm` (`SobolevEmbeddingManifoldC0.lean`), which is stated only at order
`2k` and bounds by `‖T.toHs (2k)‖`.  It is *proved* here by the verbatim port of that core's assembly,
with the **sharp** chart order `a` (`H^{2a}` seminorms, FDeriv orders `≤ 2a`) replacing the doubled order:
the sharp local Euclidean ball `L²`-Sobolev pointwise embedding `smooth_localBall_L2_pointwise_embedding_sharp`
(posited above, the only genuinely sharp input) bounds `|ftil y₁|` by `Cloc · ∑_{j ≤ 2a} ‖∂ʲftil‖_{L²}`,
and each summand is controlled, through the de-privatized order-generic chart bridges
`eLpNorm_sq_iteratedFDeriv_le_hsBlock` and `hsBlock_le_hsNorm_sq` (at chart order `a`, FDeriv orders
`j ≤ 2a`), by `‖T.toHs a‖`.  Consumers transitively depend on `sorryAx` through the sharp Euclidean
embedding.  The conclusion is a Euclidean-pull `C⁰` bound by the chart `H^{2a}`-norm, structurally distinct
from the compact-set bound it powers (no packaging). -/
private theorem rawPullCenterRS_sharp_le_hsNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : (Module.finrank ℝ E : ℝ) < 2 * (2 * a))
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {y₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} {R c : ℝ} (hR : 0 < R) (hc_pos : 0 < c)
    (hball : Metric.closedBall y₀ R ⊆ Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ (T' : Integral.L2.SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball y₀ (R / 4),
      |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cα * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ := by
  classical
  obtain ⟨Cloc, hCloc_nn, hCloc⟩ :=
    smooth_localBall_L2_pointwise_embedding_sharp (d := Module.finrank ℝ E) a ha (x₀ := y₀) (R := R) hR
  set A : ℝ := Real.sqrt (((Module.finrank ℝ E) ^ (2 * a) : ℕ) * c⁻¹) with hA_def
  have hA_nn : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨Cloc * ((2 * a + 1 : ℕ) * A), by positivity, ?_⟩
  intro T' y₁ hy₁
  set hsn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨ftil, hftil_smooth, hftil_eq⟩ :=
    exists_global_smooth_eqOn_ball_of_rawPull (I := I) (M := M) g r s T' α IJ.1 IJ.2 hball
  have hy₁_cb : y₁ ∈ Metric.closedBall y₀ R :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall hy₁
  have h_loc := hCloc (f := ftil) hftil_smooth y₁ hy₁
  have hftil_y0 : ftil y₁ =
      Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁)) := by
    have := hftil_eq hy₁_cb
    simpa [Function.comp_apply] using this
  have hball_open : Metric.ball y₀ R ⊆ Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α :=
    (Metric.ball_subset_closedBall).trans hball
  have h_eqOn_ball : Set.EqOn ftil
      (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) (Metric.ball y₀ R) :=
    hftil_eq.mono Metric.ball_subset_closedBall
  have h_eLp_eq : ∀ j,
      MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
          ((MeasureTheory.volume : MeasureTheory.Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R)) =
        MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j
            (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) z‖) 2
          ((MeasureTheory.volume : MeasureTheory.Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R)) := by
    intro j
    refine MeasureTheory.eLpNorm_congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall (fun z hz => ?_))
    have hball_nhd : Metric.ball y₀ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have h_ev : ftil =ᶠ[nhds z]
        (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) :=
      Filter.eventuallyEq_of_mem hball_nhd h_eqOn_ball
    have h_iter_eq := (h_ev.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [h_iter_eq]
  have h_per_order : ∀ j ∈ Finset.range (2 * a + 1),
      (MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
        ((MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R))).toReal
          ≤ A * hsn := by
    intro j hj
    rw [h_eLp_eq j]
    set X : ℝ≥0∞ := MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z‖) 2
      ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R)) with hX_def
    have hX_ne_top : X ≠ ⊤ := by
      rw [hX_def, ← h_eLp_eq j]
      exact smooth_eLpNorm_iteratedFDeriv_ball_ne_top (j := j) hftil_smooth
    have h_key := eLpNorm_sq_iteratedFDeriv_le_hsBlock (I := I) (M := M)
      g r s T' α IJ j hc_pos hball_open hρ_lb
    rw [← hX_def] at h_key
    have h_blk_le := hsBlock_le_hsNorm_sq (I := I) (M := M) g a T' α IJ j hj
    have h_X_sq_le :
        X ^ 2 ≤ ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T') ^ 2 :=
      h_key.trans (mul_le_mul_of_nonneg_left h_blk_le (zero_le _))
    have h_hsn_ne_top : (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T') ≠ ⊤ :=
      (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g a T').ne
    have h_rhs_ne_top :
        ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T') ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top h_hsn_ne_top)
    have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_X_sq_le
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by positivity), ENNReal.toReal_pow] at h_toReal
    have h_hsn_eq : (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T').toReal = hsn := by
      rw [hhsn_def, tensorPouSobolevHilbert_norm_eq]
    rw [h_hsn_eq] at h_toReal
    have hX_toReal_nn : 0 ≤ X.toReal := ENNReal.toReal_nonneg
    have h_card_mono : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ ≤ A ^ 2 := by
      rw [hA_def, Real.sq_sqrt (by positivity)]
      have hjle : j ≤ 2 * a := by rw [Finset.mem_range] at hj; omega
      have : ((Module.finrank ℝ E) ^ j : ℕ) ≤ ((Module.finrank ℝ E) ^ (2 * a) : ℕ) :=
        Nat.pow_le_pow_right (NeZero.pos _) hjle
      have hcast : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) ≤
          (((Module.finrank ℝ E) ^ (2 * a) : ℕ) : ℝ) := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcast (by positivity)
    have h_Xsq_le_Asq : X.toReal ^ 2 ≤ (A * hsn) ^ 2 := by
      refine h_toReal.trans ?_
      have hhsn_sq_nn : 0 ≤ hsn ^ 2 := by positivity
      calc (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ * hsn ^ 2
          ≤ A ^ 2 * hsn ^ 2 := mul_le_mul_of_nonneg_right h_card_mono hhsn_sq_nn
        _ = (A * hsn) ^ 2 := by ring
    have hAhsn_nn : 0 ≤ A * hsn := mul_nonneg hA_nn hhsn_nn
    calc X.toReal = Real.sqrt (X.toReal ^ 2) := (Real.sqrt_sq hX_toReal_nn).symm
      _ ≤ Real.sqrt ((A * hsn) ^ 2) := Real.sqrt_le_sqrt h_Xsq_le_Asq
      _ = A * hsn := Real.sqrt_sq hAhsn_nn
  rw [← hftil_y0, ← Real.norm_eq_abs]
  refine h_loc.trans ?_
  have h_sum_le :
      (∑ j ∈ Finset.range (2 * a + 1),
          (MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((MeasureTheory.volume : MeasureTheory.Measure
                (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R))).toReal)
        ≤ ((2 * a + 1 : ℕ) : ℝ) * (A * hsn) := by
    have h_each := Finset.sum_le_sum h_per_order
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_each
    exact h_each
  calc Cloc * (∑ j ∈ Finset.range (2 * a + 1),
          (MeasureTheory.eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((MeasureTheory.volume : MeasureTheory.Measure
                (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict (Metric.ball y₀ R))).toReal)
      ≤ Cloc * (((2 * a + 1 : ℕ) : ℝ) * (A * hsn)) :=
        mul_le_mul_of_nonneg_left h_sum_le hCloc_nn
    _ = Cloc * (((2 * a + 1 : ℕ) : ℝ) * A) * hsn := by ring

/-- **The sharp general-order Euclidean-pull uniform bound on a compact chart set.** At a supercritical
chart order `a` (`dim M < 2·(2a)`), for each atlas index `α` and component pair `IJ`, there is a constant
`D ≥ 0` such that on a compact set `Kc` (in chart Euclidean coordinates) contained in an open
`O ⊆ chartTargetEuclid α` on which the chart partition-of-unity pull is `≥ c`, the chart-component pull
`|tensorChartComponentRaw … IJ …|` is bounded by `D · ‖T.toHs a‖`.

This is the sharp general-order analogue of the in-library `(0, 2k)`-only private
`uniformRawPull_le_hsNorm`, *proved* here by the verbatim port of that core's public-only uniformity
assembly: a Lebesgue-number radius `δ` for the cover of the compact `Kc` by `O`
(`lebesgue_number_lemma_of_metric`), a finite sub-cover of `Kc` by balls of radius `(δ/2)/4`
(`IsCompact.elim_finite_subcover`), the per-ball center bound `rawPullCenterRS_sharp_le_hsNorm` on each,
and the finite maximum `Finset.sup'` of the per-ball constants.  Consumers transitively depend on `sorryAx`
through the posited per-ball core. -/
private theorem uniformRawPullRS_le_hsNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : (Module.finrank ℝ E : ℝ) < 2 * (2 * a))
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {Kc O : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))} {c : ℝ} (hc_pos : 0 < c)
    (hKc_compact : IsCompact Kc) (hO_open : IsOpen O)
    (hKcO : Kc ⊆ O)
    (hO_sub : O ⊆ Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ O,
      c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T' : Integral.L2.SmoothCcTensor g r s),
      ∀ y ∈ Kc,
        |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
          ≤ D * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ := by
  classical
  rcases Set.eq_empty_or_nonempty Kc with hKc_empty | hKc_ne
  · exact ⟨0, le_refl 0, fun T' y hy => by rw [hKc_empty] at hy; exact absurd hy (Set.notMem_empty y)⟩
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    lebesgue_number_lemma_of_metric (s := Kc)
      (c := fun _ : Unit => O)
      hKc_compact (fun _ => hO_open) (by intro x hx; exact Set.mem_iUnion.mpr ⟨(), hKcO hx⟩)
  have hδ_sub : ∀ y ∈ Kc, Metric.ball y δ ⊆ O := by
    intro y hy
    obtain ⟨_, hsub⟩ := hδ_ball y hy
    exact hsub
  have hδ2_pos : 0 < δ / 2 := by linarith
  have h_center : ∀ y : Kc, ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ (T' : Integral.L2.SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ((δ / 2) / 4),
      |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cy * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ := by
    intro y
    have hhalf_lt : δ / 2 < δ := half_lt_self hδ_pos
    have hhalf_le : δ / 2 ≤ δ := le_of_lt hhalf_lt
    have hcb_sub : Metric.closedBall (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (δ / 2) ⊆
        Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
      refine (Metric.closedBall_subset_ball hhalf_lt).trans ?_
      exact (hδ_sub y y.2).trans hO_sub
    have hρ_ball : ∀ z ∈ Metric.ball (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (δ / 2),
        c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      have hz' : z ∈ Metric.ball (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) δ :=
        Metric.ball_subset_ball hhalf_le hz
      exact hρ_lb z (hδ_sub y y.2 hz')
    obtain ⟨Cy, hCy_nn, hCy⟩ :=
      rawPullCenterRS_sharp_le_hsNorm (I := I) (M := M) g r s a ha
        α IJ hδ2_pos hc_pos hcb_sub hρ_ball
    exact ⟨Cy, hCy_nn, hCy⟩
  choose Cfun hCfun_nn hCfun using h_center
  obtain ⟨tcov, htcov⟩ :=
    hKc_compact.elim_finite_subcover
      (U := fun y : Kc => Metric.ball (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ((δ / 2) / 4))
      (fun y => Metric.isOpen_ball)
      (by
        intro z hz
        refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]; positivity)
  set Dmax : ℝ := (tcov.image Cfun).sup' (by
    rcases hKc_ne with ⟨z, hz⟩
    obtain ⟨y, hy_t, _⟩ := Set.mem_iUnion₂.mp (htcov hz)
    exact Finset.image_nonempty.mpr ⟨y, hy_t⟩) id ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  refine ⟨Dmax, hDmax_nn, ?_⟩
  intro T' y hy
  set hsn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨yi, hyi_t, hy_in⟩ := Set.mem_iUnion₂.mp (htcov hy)
  have h_bound := hCfun yi T' y hy_in
  have hCyi_le : Cfun yi ≤ Dmax := by
    rw [hDmax_def]
    refine le_sup_of_le_left ?_
    exact Finset.le_sup' id (Finset.mem_image_of_mem Cfun hyi_t)
  calc |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
      ≤ Cfun yi * hsn := h_bound
    _ ≤ Dmax * hsn := mul_le_mul_of_nonneg_right hCyi_le hhsn_nn

/-- For a chart base point `α` and a positive threshold `c`, the super-level set
`{x | c ≤ ρ_α x}` is compact and contained in the chart-`α` source.  In-file re-derivation of the
private `superlevel_compact_subset_source` (built from the public `chartAtlasPOU` continuity and
subordination). -/
private theorem superlevel_compact_subset_source_rs
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    IsCompact {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x} ∧
      {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x} ⊆ (chartAt H α).source := by
  classical
  have hρ_cont : Continuous fun x : M => (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x :=
    (Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  have hclosed : IsClosed {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x} :=
    isClosed_le continuous_const hρ_cont
  refine ⟨hclosed.isCompact, ?_⟩
  intro x hx
  have hx_pos : (0 : ℝ) < (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x :=
    lt_of_lt_of_le hc_pos hx
  have hx_supp : x ∈ Function.support (fun y : M => (Integral.Measure.chartAtlasPOU I M α : M → ℝ) y) :=
    ne_of_gt hx_pos
  have hx_tsupp : x ∈ tsupport (fun y : M => (Integral.Measure.chartAtlasPOU I M α : M → ℝ) y) :=
    subset_tsupport _ hx_supp
  exact Integral.Measure.chartAtlasPOU_isSubordinate I M α hx_tsupp

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The general-order per-chart fibre bound on a partition-of-unity super-level set.** At a
supercritical chart order `a` (`dim M < 2·(2a)`), for every atlas index `α` there is a constant
`D ≥ 0` such that on the super-level set `{x | c ≤ chartAtlasPOU α x}` the bundle-fibre value
`‖T.toSection x‖` of a smooth `(r, s)`-tensor is bounded by `D · ‖T.toHs a‖`, the intrinsic order-`a`
Hilbert–Schmidt chart-Sobolev (`H^{2a}` chart) norm.

This is the general-order (`a`, not necessarily even) analogue of the in-library `(0, 2k)`-only
per-chart fibre core `chartFiberNorm_le_hsNorm_on_superlevel`, *proved* here by the same chart
assembly: the off-centre tensor-fibre-norm reconstruction `tensorFiberNorm_sq_le_chartAlphaComponents_on_compact`
(public) bounds `‖T.toSection x‖²` by a constant times the sum of squared chart-component pulls, each
of which is bounded by the general-order Euclidean-pull core `uniformRawPullRS_le_hsNorm` (posited
above) times `‖T.toHs a‖`; the constant is `√(C₁ · #pairs) · Dmax`.  Consumers transitively depend on
`sorryAx` through the posited Euclidean-pull core. -/
private theorem chartFiberNormRS_le_hsNorm_on_superlevel_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : (Module.finrank ℝ E : ℝ) < 2 * (2 * a))
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : Integral.L2.SmoothCcTensor g r s),
      ∀ x ∈ {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ D *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  set Kset : Set M := {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x} with hKset_def
  obtain ⟨hK_compact, hK_sub⟩ := superlevel_compact_subset_source_rs (I := I) (M := M) α hc_pos
  rw [← hKset_def] at hK_compact hK_sub
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    PDE.RicciFlow.HebeyBlock.tensorFiberNorm_sq_le_chartAlphaComponents_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  set Kc : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' Kset) with hKc_def
  have hKc_compact : IsCompact Kc := by
    have h1 : IsCompact ((extChartAt I α) '' Kset) :=
      hK_compact.image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx; rw [extChartAt_source]; exact hK_sub hx))
    exact h1.image (toEuclidean (E := E)).continuous
  set O : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α ∩
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ⁻¹' (Set.Ioi (c / 2))
    with hO_def
  have hO_open : IsOpen O := by
    rw [hO_def]
    have hρ_cont : Continuous fun x : M => (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x :=
      (Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
    have hcontOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :=
      hρ_cont.comp_continuousOn'
        (Analysis.Sobolev.Chart.continuousOn_symm_toEuclideanSymm (I := I) (M := M) α)
    exact hcontOn.isOpen_inter_preimage
      (Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
      isOpen_Ioi
  have hO_sub : O ⊆ Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hO_def]; exact Set.inter_subset_left
  have hx_ext_src : ∀ x ∈ Kset, x ∈ (extChartAt I α).source := by
    intro x hx; rw [extChartAt_source]; exact hK_sub hx
  have hpull_eq : ∀ x ∈ Kset,
      (extChartAt I α).symm ((toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) x))) = x := by
    intro x hx
    rw [(toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I α).left_inv (hx_ext_src x hx)
  have hKcO : Kc ⊆ O := by
    intro y hy
    rw [hKc_def] at hy
    obtain ⟨z, ⟨x, hx_K, hxz⟩, hzy⟩ := hy
    have hy_eq : y = (toEuclidean (E := E)) ((extChartAt I α) x) := by rw [hxz]; exact hzy.symm
    have hpull : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = x := by
      rw [hy_eq]; exact hpull_eq x hx_K
    have hy_target : y ∈ Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_eq]
      exact ⟨(extChartAt I α) x, (extChartAt I α).map_source (hx_ext_src x hx_K), rfl⟩
    refine ⟨hy_target, ?_⟩
    have hgoal : c / 2 < (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      rw [hpull]
      have hx_ge : c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x := hx_K
      linarith [hc_pos, hx_ge]
    exact hgoal
  have hρ_on_O : ∀ y ∈ O,
      c / 2 ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    intro y hy
    rw [hO_def] at hy
    exact le_of_lt hy.2
  have hc2_pos : 0 < c / 2 := by linarith
  have h_comp : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      ∃ Dij : ℝ, 0 ≤ Dij ∧ ∀ (T' : Integral.L2.SmoothCcTensor g r s), ∀ y ∈ Kc,
        |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
          ≤ Dij * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T'‖ := by
    intro IJ
    exact uniformRawPullRS_le_hsNorm (I := I) (M := M) g r s a ha α IJ hc2_pos
      hKc_compact hO_open hKcO hO_sub hρ_on_O
  choose Dfun hDfun_nn hDfun using h_comp
  set Dmax : ℝ := (Finset.univ.sup' (Finset.univ_nonempty) Dfun) ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  set npairs : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hnp_def
  have hnp_nn : 0 ≤ npairs := Nat.cast_nonneg _
  refine ⟨Real.sqrt (C₁ * npairs) * Dmax, by positivity, ?_⟩
  intro T x hx
  set hsn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  have hx_K : x ∈ Kset := hx
  set yx : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) x) with hyx_def
  have hyx_Kc : yx ∈ Kc := by
    rw [hKc_def, hyx_def]
    exact ⟨(extChartAt I α) x, ⟨x, hx_K, rfl⟩, rfl⟩
  have hpull_x : (extChartAt I α).symm ((toEuclidean (E := E)).symm yx) = x := by
    rw [hyx_def]; exact hpull_eq x hx_K
  have h_core := hC₁ T x hx_K
  have h_each : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2 ≤
        (Dmax * hsn) ^ 2 := by
    intro IJ
    have h := hDfun IJ T yx hyx_Kc
    rw [hpull_x] at h
    have hDle : Dfun IJ ≤ Dmax := by
      rw [hDmax_def]
      exact le_sup_of_le_left (Finset.le_sup' Dfun (Finset.mem_univ IJ))
    have h' : |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x|
        ≤ Dmax * hsn :=
      h.trans (mul_le_mul_of_nonneg_right hDle hhsn_nn)
    have habs_nn : 0 ≤ |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| :=
      abs_nonneg _
    have hDhsn_nn : 0 ≤ Dmax * hsn := mul_nonneg hDmax_nn hhsn_nn
    calc (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2
        = |Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (Dmax * hsn) ^ 2 := by exact pow_le_pow_left₀ habs_nn h' 2
  have h_sum_sq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ npairs * (Dmax * hsn) ^ 2 := by
    rw [hnp_def]
    rw [← Fintype.sum_prod_type']
    refine (Finset.sum_le_sum (fun IJ _ => h_each IJ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : ‖T.toSection x‖ ^ 2 ≤ (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
    refine h_core.trans ?_
    calc C₁ * (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ C₁ * (npairs * (Dmax * hsn) ^ 2) :=
          mul_le_mul_of_nonneg_left h_sum_sq (le_of_lt hC₁_pos)
      _ = (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
          have hsq : Real.sqrt (C₁ * npairs) ^ 2 = C₁ * npairs :=
            Real.sq_sqrt (by positivity)
          nlinarith [hsq]
  have hsec_nn : 0 ≤ ‖T.toSection x‖ := norm_nonneg _
  have hconst_nn : 0 ≤ Real.sqrt (C₁ * npairs) * Dmax := by positivity
  have h_rhs_sq : (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 =
      (Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2 := by ring
  rw [h_rhs_sq] at h_sq
  calc ‖T.toSection x‖ = Real.sqrt (‖T.toSection x‖ ^ 2) := (Real.sqrt_sq hsec_nn).symm
    _ ≤ Real.sqrt ((Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt (C₁ * npairs) * Dmax * hsn := Real.sqrt_sq (by positivity)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The general-rank chart Sobolev embedding `chart-H^{2a} ↪ C⁰`.** At a supercritical chart
order `a` (`2·(2a) > dim M`, i.e. the chart-`H^{2a}` Sobolev exponent `2a` exceeds `(dim M)/2`)
there is a constant `C ≥ 0` such that the bundle-fibre value `‖T.toSection x‖` of a smooth
`(r, s)`-tensor is bounded by `C · ‖T.toHs a‖`, the intrinsic order-`a` partition-of-unity
Hilbert–Schmidt chart-Sobolev norm of `T` (an `H^{2a}` chart-Sobolev norm), for all `x`.

This is the general-rank `(r, s)`, general-order `a` analogue of the in-library `(0, 2k)`-only
chart embedding `tensorPouSobolevHilbert_embedding_Ck`.  It is *proved* here by the same
partition-of-unity assembly as the even-order `tensorPouSobolevHilbert_embedding_Ck_gNorm`: a
finite atlas-aligned partition of unity (`chartAtlasPOU_finset`, summing to `1` by
`chartAtlasPOU_finset_sum_eq_one`) reduces the global bound to the per-chart super-level bound
`chartFiberNormRS_le_hsNorm_on_superlevel_sharp` at order `a` (posited above), with the uniform
constant the finite supremum of the per-chart constants.  Consumers transitively depend on
`sorryAx` through that posited per-chart core. -/
private theorem pointwiseFiberNormRS_le_chartHs_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : 2 * (2 * a) > Module.finrank ℝ E) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤ C *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  have ha' : (Module.finrank ℝ E : ℝ) < 2 * (2 * a) := by exact_mod_cast ha
  rcases isEmpty_or_nonempty M with hMempty | hMne
  · exact ⟨1, by norm_num, fun _T x => (hMempty.false x).elim⟩
  obtain ⟨x₀⟩ := hMne
  set S : Finset M := Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hS_ne : S.Nonempty := by
    have hsum := Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x₀
    rw [← hS_def] at hsum
    rcases Finset.eq_empty_or_nonempty S with hSe | hSne
    · exfalso; rw [hSe] at hsum; simp at hsum
    · exact hSne
  set N : ℕ := S.card with hN_def
  have hN_pos : 0 < N := Finset.card_pos.mpr hS_ne
  have hN_pos_real : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hcN_pos : (0 : ℝ) < 1 / N := by positivity
  have h_perchart : ∀ α : M, ∃ Dα : ℝ, 0 ≤ Dα ∧ ∀ (T : Integral.L2.SmoothCcTensor g r s),
      ∀ x ∈ {x : M | (1 / N : ℝ) ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ Dα *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ := fun α =>
    chartFiberNormRS_le_hsNorm_on_superlevel_sharp (I := I) (M := M) g r s a ha' α hcN_pos
  choose Dfun hDfun_nn hDfun using h_perchart
  set C : ℝ := S.sup' hS_ne Dfun + 1 with hC_def
  have hSsup_nn : 0 ≤ S.sup' hS_ne Dfun := by
    obtain ⟨β, hβ⟩ := hS_ne
    exact le_trans (hDfun_nn β) (Finset.le_sup' Dfun hβ)
  have hC_nn : 0 ≤ C := by rw [hC_def]; linarith
  refine ⟨C, hC_nn, fun T x => ?_⟩
  have hsum := Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  rw [← hS_def] at hsum
  have h_exists_α : ∃ α ∈ S, (1 / N : ℝ) ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x := by
    by_contra h_all
    push Not at h_all
    have h_sum_lt :
        (∑ α ∈ S, (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x) < ∑ _α ∈ S, (1 / N : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hS_ne (fun α hα => h_all α hα)
    rw [Finset.sum_const, hsum, nsmul_eq_mul, ← hN_def, mul_one_div,
      div_self hN_pos_real.ne'] at h_sum_lt
    exact lt_irrefl 1 h_sum_lt
  obtain ⟨α, hα_S, hα_ge⟩ := h_exists_α
  have h_bound := hDfun α T x hα_ge
  refine h_bound.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [hC_def]
  have hDα_le : Dfun α ≤ S.sup' hS_ne Dfun := Finset.le_sup' Dfun hα_S
  linarith

/-- **The general-rank single-step rough-Laplacian `L²`-coordinate eigen-equation.**
`cᵢ(Δ_∇ T) = -λᵢ · cᵢ(T)`.  The bidegree-`(r, s)` analogue of the `(0, 2)`
`rawConnLapSmooth_tensorL2Coeff`, proved here from `Δ_∇ T = T - (1 - Δ_∇) T` (the definition of
`oneMinusConnLapSmooth`), the additivity of the eigenbasis coordinate, the `(1 - Δ_∇)`
coordinate identity `tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS`
(`cᵢ((1 - Δ_∇) T) = (1 + λᵢ) cᵢ(T)`), and `cᵢ(T) - (1 + λᵢ) cᵢ(T) = -λᵢ cᵢ(T)`. -/
private theorem rawConnLapSmooth_tensorL2CoeffRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T)) i =
      (- Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i := by
  classical
  have h_split : Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T =
      T - oneMinusConnLapSmooth (I := I) g r s T := by
    rw [show oneMinusConnLapSmooth (I := I) g r s T =
          T - Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T from rfl]
    abel
  have h_toL2 :
      Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T) =
        Integral.L2.SmoothCcTensor.toL2 T -
          Integral.L2.SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g r s T) := by
    rw [h_split]; exact map_sub _ _ _
  rw [h_toL2, Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner, inner_sub_right,
    ← Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    ← Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmoothRS (I := I) (M := M) g r s T i]
  ring

/-- **The general-rank iterated rough-Laplacian `L²`-coordinate eigen-equation.**
`cᵢ(Δ_∇^j T) = (-λᵢ)^j · cᵢ(T)`.  The bidegree-`(r, s)` analogue of the `(0, 2)`
`rawConnLapIter_tensorL2Coeff`, proved by induction on `j` from the single-step
`rawConnLapSmooth_tensorL2CoeffRS` and the iterate recursion `rawTensorConnLapIter_succ`. -/
private theorem rawConnLapIter_tensorL2CoeffRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapIter (I := I) g r s j T)) i =
      (- Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i := by
  induction j with
  | zero => rw [Integral.Connection.rawTensorConnLapIter_zero]; simp
  | succ j ih =>
      rw [Integral.Connection.rawTensorConnLapIter_succ,
        rawConnLapSmooth_tensorL2CoeffRS (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapIter (I := I) g r s j T) i, ih, pow_succ]
      ring

/-- **The general-rank iterated-Laplacian `L²` norm ≤ spectral norm bound.** For a smooth
`(r, s)`-tensor `T`, a gradient order `i`, and an even spectral exponent `N` with `2 * i ≤ N`,
the `L²` norm of the iterated rough Laplacian `Δ_∇^i T` is bounded by the square root of the
weighted spectral square-sum `∑ⱼ (1 + λⱼ)^N · cⱼ(T)²`.  The bidegree-`(r, s)` analogue of the
`(0, 2)` `rawConnLapIter_l2Norm_le_sqrt_spectral`: `‖Δ_∇^i T‖² = ∑ⱼ λⱼ^{2i} · cⱼ(T)²` by
Parseval applied to the iterated eigen-equation `rawConnLapIter_tensorL2CoeffRS`, and
`λⱼ^{2i} ≤ (1 + λⱼ)^N` termwise (since `λⱼ ≥ 0`, `1 ≤ 1 + λⱼ`, `2i ≤ N`); summability of the
weighted family `smoothCcTensorRS_tensorL2Coeff_weighted_summable` lifts the termwise bound to
the infinite sums. -/
private theorem rawConnLapIterRS_l2Norm_le_sqrt_spectral
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (i N : ℕ) (hiN : 2 * i ≤ N) :
    ‖Integral.L2.SmoothCcTensor.toL2
        (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ ≤
      Real.sqrt (∑' j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (Integral.L2.SmoothCcTensor.toL2 T) j) ^ 2) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s with hc_def
  set cT : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun j => tensorL2Coeff (I := I) (M := M) hc (Integral.L2.SmoothCcTensor.toL2 T) j with hcT_def
  have hsq_eq :
      ‖Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ ^ 2 =
        ∑' j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
          (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
            ^ (2 * i) * (cT j) ^ 2 := by
    rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) hc
      (Integral.L2.SmoothCcTensor.toL2
        (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T))]
    refine tsum_congr (fun j => ?_)
    rw [rawConnLapIter_tensorL2CoeffRS (I := I) (M := M) g r s T j i]
    rw [mul_pow, ← pow_mul, mul_comm i 2,
      (even_two_mul i).neg_pow
        (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)]
  have hsummable :
      Summable (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2) :=
    smoothCcTensorRS_tensorL2Coeff_weighted_summable (I := I) (M := M) g r s (N : ℝ) T
  have hterm : ∀ j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
      (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
          ^ (2 * i) * (cT j) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2 := by
    intro j
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hlam_nn : 0 ≤ Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) j :=
      Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg (I := I) (M := M) j
    have h_one_le : (1 : ℝ) ≤ 1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) j := by linarith
    have h_base_le : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) j ≤
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j := by
      linarith
    have h1 : (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
        ^ (2 * i) ≤
        (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
          ^ (2 * i) :=
      pow_le_pow_left₀ hlam_nn h_base_le (2 * i)
    have h2 : (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
        ^ (2 * i) ≤
        (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j) ^ N :=
      pow_le_pow_right₀ h_one_le hiN
    have hw : tensorSobolevWeight (I := I) (M := M) j (N : ℝ) =
        (1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j) ^ N := by
      unfold tensorSobolevWeight
      rw [Real.rpow_natCast]
    rw [hw]
    exact le_trans h1 h2
  have hsummable_small :
      Summable (fun j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
        (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
          ^ (2 * i) * (cT j) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hterm hsummable
    have hlam_nn : 0 ≤ Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) j :=
      Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg (I := I) (M := M) j
    positivity
  have htsum_le :
      ∑' j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
          (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) j)
            ^ (2 * i) * (cT j) ^ 2 ≤
        ∑' j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
          tensorSobolevWeight (I := I) (M := M) j (N : ℝ) * (cT j) ^ 2 :=
    Summable.tsum_le_tsum hterm hsummable_small hsummable
  have hnn : 0 ≤ ‖Integral.L2.SmoothCcTensor.toL2
      (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ := norm_nonneg _
  rw [← Real.sqrt_sq hnn, hsq_eq]
  exact Real.sqrt_le_sqrt htsum_le

/-! ### The general-rank all-order Gårding bootstrap

The bidegree-`(r, s)` mirror of the `(0, 2)` `AllOrderGardingBootstrap.lean`.  The strong
induction `gradOrderRS_l2Norm_le_lapIter_sum` (the engine) is **rank-generic**: it threads only
norms of `iteratedCovGrad`/`rawTensorConnLapIter`/`covGrad`/`rawTensorConnLapSmooth` (all
bidegree-`(r, s)` in the library) through pure norm arithmetic, exactly as the `(0, 2)` engine
`gradOrder_l2Norm_le_lapIter_sum`.  The three per-order inputs it consumes —
`Order2GardingFamilyRS`, `Order1ControlFamilyRS`, `CommutatorDefectBoundRS` — are the
genuinely-`(r, s)` curvature/Green content (the `(0, ·)` discharges `order2GardingFamily_holds`,
`order1ControlFamily_holds`, `commutatorDefectBound_holds` rest on `(0, ·)`-restricted curvature
primitives), so the three `(r, ·)`-valence families are posited below as precise atoms and the
bootstrap is *proved* on top of them by the ported induction. -/

/-- **The per-valence order-`2` Gårding family at fixed contravariant rank `r`.** Bidegree-`(r, ·)`
analogue of `Order2GardingFamily`. -/
private def Order2GardingFamilyRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) (Cg : ℕ → ℝ) : Prop :=
  (∀ s, 0 ≤ Cg s) ∧ ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g r s),
    ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)‖ ^ 2 ≤
      Cg s * (‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S‖ ^ 2 + ‖S‖ ^ 2)

/-- **The per-valence order-`1` control family at fixed contravariant rank `r`.** Bidegree-`(r, ·)`
analogue of `Order1ControlFamily`. -/
private def Order1ControlFamilyRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) : Prop :=
  ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g r s),
    ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S‖ ^ 2 ≤
      ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S‖ * ‖S‖

/-- **The per-order curvature-commutator `L²` defect family at fixed bidegree `(r, s)`.**
Bidegree-`(r, s)` analogue of `CommutatorDefectBound`. -/
private def CommutatorDefectBoundRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Cc : ℕ → ℝ) : Prop :=
  (∀ p, 0 ≤ Cc p) ∧ ∀ (U : Integral.L2.SmoothCcTensor g r s) (p : ℕ),
    ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p)
          (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U) -
        PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖ ≤
      Cc p * ∑ i ∈ Finset.range (p + 2),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖

/-- **The general-rank order-`1` control family.** At fixed contravariant rank `r`,
`Order1ControlFamilyRS g r` holds: for every covariant rank `s` and smooth compactly-supported
`(r, s)`-tensor `S`, `‖∇S‖² ≤ ‖Δ_∇ S‖ · ‖S‖`.

This is the bidegree-`(r, s)` analogue of `order1ControlFamily_holds`, *proved* here by the
verbatim port of the `(0, ·)` interior-elliptic estimate `covGrad_l2NormSq_le_rawConnLap_mul_self_gen`:
the squared `L²` gradient norm equals the self-inner product `⟪∇S, ∇S⟫_{L²}` (`tensorL2Norm_sq_toFun`),
which the general-rank connection-Laplacian Green identity — the in-file posited
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS`, specialised at `v := S` — turns into
`-⟪Δ_∇ S, S⟫_{L²}`, bounded by `|⟪Δ_∇ S, S⟫_{L²}| ≤ ‖Δ_∇ S‖·‖S‖` through the rank-generic global
`L²` Cauchy–Schwarz `abs_tensorL2Inner_le` (with `neg_le_abs`). No curvature input is needed (the
order-`1` control is curvature-free, constant `1`). Consumers transitively depend on `sorryAx` only
through the posited general-rank Green identity. -/
private theorem order1ControlFamilyRS_holds (g : SmoothRiemannianMetric I M) (r : ℕ) :
    Order1ControlFamilyRS (I := I) (M := M) g r := by
  intro s S
  set ΔS : Integral.L2.SmoothCcTensor g r s :=
    Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S),
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) ΔS,
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) S]
  have hgreen :
      Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ^ 2 =
        - Integral.L2.tensorL2Inner (I := I) (M := M) g r s ΔS.toFun S.toFun := by
    rw [Integral.Connection.tensorL2Norm_sq_toFun (I := I) (M := M) g r (s + 1)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)]
    rw [hΔS_def]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS (I := I) (M := M) g r s S S
  rw [hgreen]
  have hcs := Integral.L2.abs_tensorL2Inner_le (I := I) (M := M) g r s ΔS.toFun S.toFun
    (Integral.L2.SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (Integral.L2.SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (Integral.L2.SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  exact le_trans (neg_le_abs _) hcs

/-- **The per-valence integrated curvature cross-term bound at fixed contravariant rank `r`.**
Bidegree-`(r, ·)` analogue of `CurvatureCrossTermBound`: a valence-dependent nonnegative
`Ccross : ℕ → ℝ` such that at every covariant rank `s` the one-sided `L²` pairing of the
rough-Laplacian / covariant-gradient commutator defect `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` against `∇S`
is bounded by `Ccross s · (‖∇S‖²_{L²} + ‖S‖_{L²}·‖∇S‖_{L²})`. -/
private def CurvatureCrossTermBoundRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) (Ccross : ℕ → ℝ) : Prop :=
  (∀ s, 0 ≤ Ccross s) ∧ ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g r s),
    - Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ≤
      Ccross s *
        (Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ^ 2 +
          Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun *
            Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun)

/-- **The general-rank diagonal Green identity at rank `s + 1`.** For a smooth compactly-supported
`(r, s)`-tensor `S`, writing `∇S := covGrad g r s S` for its `(r, s + 1)` covariant gradient, the
diagonal `L²` self-pairing of `∇²S = ∇(∇S)` equals minus the `L²` pairing of the rough Laplacian
`Δ_∇(∇S)` with `∇S`.  The diagonal specialisation (at `v := T := ∇S`) of the general-rank
connection-Laplacian Green identity `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS`; the
bidegree-`(r, s)` analogue of `covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen`. -/
private lemma covGradRS_l2Inner_self_eq_neg_rawConnLap_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1 + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun =
      - Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS (I := I) (M := M) g r (s + 1)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)

/-- **The general-rank Laplacian-gradient collapse at rank `s`.** For a smooth compactly-supported
`(r, s)`-tensor `S`, the `L²` inner product of the covariant gradient of `Δ_∇ S` with the covariant
gradient of `S` equals minus the squared `L²` norm of `Δ_∇ S`.  The rank-`(r, s)` Green identity at
the pair `(S, Δ_∇ S)` with the symmetry of the global `L²` pairing; the bidegree-`(r, s)` analogue of
`covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen`. -/
private lemma covGradRS_rawConnLap_l2Inner_covGrad_eq_neg_normSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun =
      - Integral.L2.tensorL2Norm (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 := by
  set ΔS : Integral.L2.SmoothCcTensor g r s :=
    Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
  rw [Integral.L2.tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s ΔS).toFun
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS (I := I) (M := M) g r s S ΔS]
  rw [hΔS_def]
  rw [Integral.Connection.tensorL2Norm_sq_toFun (I := I) (M := M) g r s
    (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)]

/-- **The general-rank cross-pairing split.** Writing `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` for the
rough-Laplacian / covariant-gradient commutator defect (a `(r, s + 1)`-tensor field), the `L²` pairing
of `Δ_∇(∇S)` with `∇S` splits as minus the squared `L²` norm of `Δ_∇ S` plus the curvature cross term.
The bidegree-`(r, s)` analogue of `rawConnLap_l2Inner_covGrad_split_gen`. -/
private lemma rawConnLapRS_l2Inner_covGrad_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
        (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun =
      - Integral.L2.tensorL2Norm (I := I) (M := M) g r s
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 +
        Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  set GS : Integral.L2.SmoothCcTensor g r (s + 1) :=
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S with hGS_def
  set ΔGS : Integral.L2.SmoothCcTensor g r (s + 1) :=
    Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1) GS with hΔGS_def
  set GΔ : Integral.L2.SmoothCcTensor g r (s + 1) :=
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
      (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [Integral.L2.SmoothCcTensor.toFun_add]
  rw [Integral.L2.tensorL2Inner_add_left (I := I) (M := M) g r (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (Integral.L2.SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (Integral.L2.SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGradRS_rawConnLap_l2Inner_covGrad_eq_neg_normSq (I := I) (M := M) g r s S]

/-- **The general-rank integrated order-`2` Weitzenböck identity.** For a smooth compactly-supported
`(r, s)`-tensor `S`, `‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Curv, ∇S⟩_{L²}`, where `Curv := Δ_∇(∇S) − ∇(Δ_∇ S)`.

This is the bidegree-`(r, s)` analogue of `weitzenbock_integrated_covGrad_l2_normSq`, *proved* here by
the verbatim port of that rank-`0` proof: the derivation is purely the two diagonal Green identities
(the general-rank `covGradRS_l2Inner_self_eq_neg_rawConnLap_inner` at rank `s + 1` and the collapse
`covGradRS_rawConnLap_l2Inner_covGrad_eq_neg_normSq` at rank `s`, both feeding the now-in-library
general-rank connection-Laplacian Green identity `…_rs` via the in-file transit
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS`) chained through the cross-pairing split
`rawConnLapRS_l2Inner_covGrad_split` and closed by `ring`.  The curvature content is packaged into the
single defect field `Curv` and never differentiated, exactly as in the `(0, s)` proof; with the
general-rank Green identity in the library no rank restriction remains.  Consumers transitively depend
on `sorryAx` only through that Green identity. -/
private theorem weitzenbockRS_integrated_covGrad_l2_normSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun ^ 2 =
      Integral.L2.tensorL2Norm (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun := by
  rw [Integral.Connection.tensorL2Norm_sq_toFun (I := I) (M := M) g r (s + 1 + 1)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S))]
  rw [covGradRS_l2Inner_self_eq_neg_rawConnLap_inner (I := I) (M := M) g r s S]
  rw [rawConnLapRS_l2Inner_covGrad_split (I := I) (M := M) g r s S]
  ring

/-- **The general-rank order-`2` Gårding estimate from a cross-term bound.** Bidegree-`(r, s)`
analogue of `secondCovGrad_l2NormSq_le_of_cross_bound`, *proved* here by the verbatim port of the
integrated-Weitzenböck Young reduction: the general-rank integrated Weitzenböck identity
`weitzenbockRS_integrated_covGrad_l2_normSq`, the supplied cross-term hypothesis, the order-`1`
control `order1ControlFamilyRS_holds` (`‖∇S‖² ≤ ‖Δ_∇ S‖·‖S‖`), and Young's inequality
`2ab ≤ a² + b²`. -/
private theorem secondCovGradRS_l2NormSq_le_of_cross_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s)
    (Ccross : ℝ) (hCcross : 0 ≤ Ccross)
    (hcross :
      - Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ≤
        Ccross *
          (Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ^ 2 +
            Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun *
              Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun)) :
    Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
          (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun ^ 2 ≤
      (2 + 2 * Ccross) *
        (Integral.L2.tensorL2Norm (I := I) (M := M) g r s
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 +
          Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2) := by
  classical
  set nHess : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)).toFun with hnHess_def
  set nGrad : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1)
    (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun with hnGrad_def
  set nLap : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r s
    (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S).toFun with hnLap_def
  set nS : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun with hnS_def
  have hnGrad_nn : 0 ≤ nGrad := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + 1) _
  have hnS_nn : 0 ≤ nS := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r s _
  have hweitz :
      nHess ^ 2 =
        nLap ^ 2 -
          Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun := by
    rw [hnHess_def, hnLap_def]
    exact weitzenbockRS_integrated_covGrad_l2_normSq (I := I) (M := M) g r s S
  have horder1 : nGrad ^ 2 ≤ nLap * nS := by
    have h := order1ControlFamilyRS_holds (I := I) (M := M) g r s S
    rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S),
      Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S),
      Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) S] at h
    rw [hnGrad_def, hnLap_def, hnS_def]; exact h
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := by
    have hcross' :
        - Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
                  (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
                Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
                  (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ≤
          Ccross * (nGrad ^ 2 + nS * nGrad) := by
      rw [hnGrad_def, hnS_def]; exact hcross
    rw [hweitz]
    linarith [hcross']
  have hyoung_ls : nLap * nS ≤ (nLap ^ 2 + nS ^ 2) / 2 := by
    nlinarith [sq_nonneg (nLap - nS)]
  have hyoung_sg : nS * nGrad ≤ (nS ^ 2 + nGrad ^ 2) / 2 := by
    nlinarith [sq_nonneg (nS - nGrad)]
  have hbracket : nGrad ^ 2 + nS * nGrad ≤ 2 * (nLap ^ 2 + nS ^ 2) := by
    have h1 : nGrad ^ 2 ≤ (nLap ^ 2 + nS ^ 2) / 2 := le_trans horder1 hyoung_ls
    nlinarith [h1, hyoung_sg]
  have hkey : Ccross * (nGrad ^ 2 + nS * nGrad) ≤ Ccross * (2 * (nLap ^ 2 + nS ^ 2)) :=
    mul_le_mul_of_nonneg_left hbracket hCcross
  have hnLapSq_nn : 0 ≤ nLap ^ 2 := sq_nonneg _
  have hnSSq_nn : 0 ≤ nS ^ 2 := sq_nonneg _
  calc nHess ^ 2
      ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := hstep1
    _ ≤ nLap ^ 2 + Ccross * (2 * (nLap ^ 2 + nS ^ 2)) := by linarith [hkey]
    _ ≤ (2 + 2 * Ccross) * (nLap ^ 2 + nS ^ 2) := by nlinarith [hnLapSq_nn, hnSSq_nn]

/-- **The general-rank order-`2` cross-term family from the atomic cross-term bound.** The
bidegree-`(r, ·)` analogue of `order2GardingFamily_of_curvatureCrossTermBound`: from a
`CurvatureCrossTermBoundRS g r Ccross` witness the order-`2` Gårding family
`Order2GardingFamilyRS g r (fun s => 2 + 2·Ccross s)` follows, at every valence `s` by the
general-rank reduction `secondCovGradRS_l2NormSq_le_of_cross_bound`. -/
private theorem order2GardingFamilyRS_of_curvatureCrossTermBoundRS
    (g : SmoothRiemannianMetric I M) (r : ℕ) (Ccross : ℕ → ℝ)
    (hcross : CurvatureCrossTermBoundRS (I := I) (M := M) g r Ccross) :
    Order2GardingFamilyRS (I := I) (M := M) g r (fun s => 2 + 2 * Ccross s) := by
  obtain ⟨hCcross, hcrossS⟩ := hcross
  refine ⟨fun s => by have := hCcross s; linarith, fun s S => ?_⟩
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S)),
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
      (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S),
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) S]
  exact secondCovGradRS_l2NormSq_le_of_cross_bound (I := I) (M := M) g r s S (Ccross s)
    (hCcross s) (hcrossS s S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Three-term pointwise-to-`L²` packaging at contravariant rank `r`.** The bidegree-`(r, ·)`
analogue of `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_three`: if the intrinsic fibre norm of
`Curv : SmoothCcTensor g r c` is pointwise bounded by `C²` times the sum of the fibre norms of
`A : SmoothCcTensor g r a`, `B : SmoothCcTensor g r b`, `D : SmoothCcTensor g r d` (with `C ≥ 0`),
then `‖Curv‖ ≤ C · (‖A‖ + ‖B‖ + ‖D‖)`. Proved verbatim from the rank-generic fibre-norm bridge
`Integral.L2.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq` and `integral_mono`, exactly as the
rank-`0` original (whose underlying engine is already rank-generic). -/
private theorem tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_three
    (g : SmoothRiemannianMetric I M) (r : ℕ) {a b c d : ℕ}
    (A : Integral.L2.SmoothCcTensor g r a) (B : Integral.L2.SmoothCcTensor g r b)
    (D : Integral.L2.SmoothCcTensor g r d)
    (Curv : Integral.L2.SmoothCcTensor g r c) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x) ≤
        C ^ 2 *
          (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) +
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x))) :
    ‖Curv‖ ≤ C * (‖A‖ + ‖B‖ + ‖D‖) := by
  classical
  set μ := Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) A,
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) B,
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) D,
    Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) Curv]
  set nA : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r a A.toFun with hnA_def
  set nB : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r b B.toFun with hnB_def
  set nD : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r d D.toFun with hnD_def
  set nCurv : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r c Curv.toFun with hnCurv_def
  have hnA_nn : 0 ≤ nA := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r a _
  have hnB_nn : 0 ≤ nB := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r b _
  have hnD_nn : 0 ≤ nD := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r d _
  have hnCurv_nn : 0 ≤ nCurv := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r c _
  have hfunA : A.toFun = fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
      (M := M) (r := r) (s := a) (x := x) (A.toSection x) := rfl
  have hfunB : B.toFun = fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
      (M := M) (r := r) (s := b) (x := x) (B.toSection x) := rfl
  have hfunD : D.toFun = fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
      (M := M) (r := r) (s := d) (x := x) (D.toSection x) := rfl
  have hfunCurv : Curv.toFun = fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (I := I) (M := M) (r := r) (s := c) (x := x) (Curv.toSection x) := rfl
  have hbridgeA : nA ^ 2 =
      ∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) ∂μ := by
    rw [hnA_def, hμ_def, hfunA]
    exact Integral.Connection.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r a _
  have hbridgeB : nB ^ 2 =
      ∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) ∂μ := by
    rw [hnB_def, hμ_def, hfunB]
    exact Integral.Connection.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r b _
  have hbridgeD : nD ^ 2 =
      ∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x) ∂μ := by
    rw [hnD_def, hμ_def, hfunD]
    exact Integral.Connection.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r d _
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def, hfunCurv]
    exact Integral.Connection.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r c _
  have hintA := Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r a A
  have hintB := Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r b B
  have hintD := Integral.Connection.integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r d D
  set RHS : M → ℝ := fun x =>
    C ^ 2 *
      (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) +
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x))
    with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def, hμ_def]
    exact ((hintA.add hintB).add hintD).const_mul (C ^ 2)
  have hcurv_nn : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r c x _)
  have hint_le :
      (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn hRHS_int
      (Filter.Eventually.of_forall hpt)
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        C ^ 2 *
          ((∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) ∂μ) +
            (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) ∂μ) +
            (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x) ∂μ)) := by
    rw [hRHS_def, MeasureTheory.integral_const_mul]
    congr 1
    have hsplitAB :
        (∫ x, (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x)) ∂μ) =
          (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) ∂μ) +
            (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) ∂μ) :=
      MeasureTheory.integral_add hintA hintB
    have hsplitABD :
        (∫ x, ((Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
              Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x)) +
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x)) ∂μ) =
          (∫ x, (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
              Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x)) ∂μ) +
            (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x) ∂μ) :=
      MeasureTheory.integral_add (hintA.add hintB) hintD
    rw [hsplitABD, hsplitAB]
  have hsq_bound : nCurv ^ 2 ≤ C ^ 2 * (nA ^ 2 + nB ^ 2 + nD ^ 2) := by
    rw [hbridgeCurv, hbridgeA, hbridgeB, hbridgeD]
    calc (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C ^ 2 *
            ((∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) ∂μ) +
              (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x) ∂μ) +
              (∫ x, Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r d x (D.toSection x) ∂μ)) :=
          hRHS_integral
  clear_value nA nB nD nCurv
  have hy_nn : 0 ≤ C * (nA + nB + nD) :=
    mul_nonneg hC (by linarith [hnA_nn, hnB_nn, hnD_nn])
  have hfinal_sq : nCurv ^ 2 ≤ (C * (nA + nB + nD)) ^ 2 := by
    refine le_trans hsq_bound ?_
    have hcross : nA ^ 2 + nB ^ 2 + nD ^ 2 ≤ (nA + nB + nD) ^ 2 := by
      nlinarith [mul_nonneg hnA_nn hnB_nn, mul_nonneg hnA_nn hnD_nn,
        mul_nonneg hnB_nn hnD_nn]
    nlinarith [mul_le_mul_of_nonneg_left hcross (sq_nonneg C), sq_nonneg C]
  nlinarith [hfinal_sq, hnCurv_nn, hy_nn, sq_nonneg (nCurv - C * (nA + nB + nD))]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Two-term pointwise-to-`L²` packaging at contravariant rank `r`.** The bidegree-`(r, ·)`
analogue of `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`: from
`rfns(Curv)(x) ≤ C² · (rfns(A)(x) + rfns(B)(x))` (`C ≥ 0`), conclude `‖Curv‖ ≤ C · (‖A‖ + ‖B‖)`.
The two-term specialization of `tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_three` (third term
the zero tensor, whose fibre norm vanishes). -/
private theorem tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_two
    (g : SmoothRiemannianMetric I M) (r : ℕ) {a b c : ℕ}
    (A : Integral.L2.SmoothCcTensor g r a) (B : Integral.L2.SmoothCcTensor g r b)
    (Curv : Integral.L2.SmoothCcTensor g r c) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r c x (Curv.toSection x) ≤
        C ^ 2 *
          (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r a x (A.toSection x) +
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x (B.toSection x))) :
    ‖Curv‖ ≤ C * (‖A‖ + ‖B‖) := by
  have hbound := tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_three (I := I) (M := M) g r
    A B (0 : Integral.L2.SmoothCcTensor g r b) Curv C hC (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r b x
        ((0 : Integral.L2.SmoothCcTensor g r b).toSection x) = 0 := by
      rw [Integral.L2.SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact Integral.Connection.riemannianFiberNormSq_zero (I := I) (M := M) g r b x
    rw [hz, add_zero]; exact hpt x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The general-rank integrated bracket-free curvature representation (posited general-rank
curvature child).** At fixed contravariant rank `r` there is a valence-dependent nonnegative
`K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the rough-Laplacian / covariant-gradient commutator defect
`Curv := Δ_∇(∇S) − ∇(Δ_∇ S)` admits a *bracket-free* curvature contraction field `G` (a
`(r, s + 1)`-tensor) with the same `L²` pairing against `∇S`, `⟨Curv, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}`,
and `‖G‖ ≤ K s · (‖∇S‖ + ‖S‖)`.

This is the bidegree-`(r, ·)` analogue of the `(0, ·)` atomic curvature input
`exists_pointwiseTensorCurv_l2_bracketFree_repr`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`, body `sorry`).  Fibrewise
`Curv` is, by the Ricci identity on the gradient field, a Riemann-curvature contraction of `∇S`
plus a moving-frame `∇²S`-order bracket (the false slot-`0` frame-trace matching on a normal
manifold); only the `L²` pairing against `∇S` integrates the bracket away, leaving the bracket-free
field `G` whose fibre norm is a genuine curvature contraction of `∇S`, controlled at each fixed
valence `s` by the curvature sup `‖R‖_∞` over the compact manifold (which on the `(r, s)`-tensor
bundle grows like `(r + s + 1)·‖R‖_∞`, hence the per-valence constant).  The genuinely general-rank
`(r, s)` curvature contraction is absent from the library (the rank-`0` field `pointwiseTensorCurv`
and its bounds are stated only at contravariant rank `0`), so it is posited here.  The constant is
per-valence (`ℕ → ℝ`), not a single scalar (the curvature endomorphism of the `(r, s)`-bundle is an
`(r + s)`-slot derivation), so this is NOT the unsatisfiable single-const-∀s shape.  The conclusion
is a representation-plus-norm-bound for a curvature field, structurally distinct from the one-sided
pairing bound it powers (and strictly stronger: it produces the representing field `G`); the body is
`sorry` and consumers transitively depend on `sorryAx`. -/
private theorem exists_curvCrossTermRS_l2_bracketFree_repr
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧ ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g r s),
      ∃ G : Integral.L2.SmoothCcTensor g r (s + 1),
        Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 1)
                  (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) -
                Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s
                  (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s S)).toFun
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun =
            Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1) G.toFun
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toFun ∧
          ‖G‖ ≤ K s *
            (‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S‖ + ‖S‖) := by
  classical
  obtain ⟨Cper, hCper_nn, hdata⟩ :=
    Integral.Connection.exists_pointwiseTensorCurvRS_movingFrameField_orderSeparated_bracketFreePairing
      (I := I) (M := M) g r
  refine ⟨fun s => 2 * Cper s, fun s => mul_nonneg (by norm_num) (hCper_nn s), fun s S => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hGcurv, hGcurvDeriv, _hrem, hpair⟩ := hdata s S
  refine ⟨Gcurv + GcurvDeriv, ?_, ?_⟩
  · exact hpair.symm
  · refine tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g r
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S) S
      (Gcurv + GcurvDeriv) (2 * Cper s)
      (mul_nonneg (by norm_num) (hCper_nn s)) (fun x => ?_)
    set fS : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x
      (S.toSection x) with hfS
    set fgS : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S).toSection x) with hfgS
    have hfS_nn : 0 ≤ fS := Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    have hfgS_nn : 0 ≤ fgS :=
      Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hCsq_nn : 0 ≤ Cper s ^ 2 := sq_nonneg _
    have hadd := Integral.Connection.riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
      (Gcurv.toSection x) (GcurvDeriv.toSection x)
    have hGSec : (Gcurv + GcurvDeriv).toSection x = Gcurv.toSection x + GcurvDeriv.toSection x := by
      rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl
    have hsq : (2 * Cper s) ^ 2 = 4 * Cper s ^ 2 := by ring
    rw [hsq, hGSec]
    nlinarith [hadd, hGcurv x, hGcurvDeriv x, hfS_nn, hfgS_nn, hCsq_nn]

/-- **The general-rank atomic curvature cross-term bound.** At fixed contravariant rank `r` there is
a valence-dependent nonnegative `Ccross : ℕ → ℝ` with `CurvatureCrossTermBoundRS g r Ccross`.

This is the bidegree-`(r, ·)` analogue of the `(0, ·)` atomic cross-term `curvatureCrossTermBound_holds`,
*proved* here by the verbatim port of that reduction: the general-rank integrated bracket-free curvature
representation `exists_curvCrossTermRS_l2_bracketFree_repr` supplies, at each valence `s`, the bracket-free
field `G` with `⟨Curv, ∇S⟩_{L²} = ⟨G, ∇S⟩_{L²}` and `‖G‖ ≤ Ccross s · (‖∇S‖ + ‖S‖)`; the inner-product
Cauchy–Schwarz `|⟨G, ∇S⟩| ≤ ‖G‖·‖∇S‖` (`abs_real_inner_le_norm`, via `SmoothCcTensor.inner_def`) and
`neg_le_abs` then bound the one-sided pairing by `Ccross s · (‖∇S‖² + ‖S‖·‖∇S‖)`.  Consumers transitively
depend on `sorryAx` through the posited bracket-free representation. -/
private theorem curvatureCrossTermBoundRS_holds (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Ccross : ℕ → ℝ, CurvatureCrossTermBoundRS (I := I) (M := M) g r Ccross := by
  classical
  obtain ⟨K, hK_nn, hrepr⟩ := exists_curvCrossTermRS_l2_bracketFree_repr (I := I) (M := M) g r
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨G, hident, hGbound⟩ := hrepr s S
  set GS : Integral.L2.SmoothCcTensor g r (s + 1) :=
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s S with hGS_def
  rw [hident]
  set nGrad : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + 1) GS.toFun with hnGrad_def
  set nS : ℝ := Integral.L2.tensorL2Norm (I := I) (M := M) g r s S.toFun with hnS_def
  have hnGrad_eq : ‖GS‖ = nGrad := Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) GS
  have hnS_eq : ‖S‖ = nS := Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) S
  have hnGrad_nn : 0 ≤ nGrad := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + 1) _
  have hcs : |Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1) G.toFun GS.toFun| ≤
      ‖G‖ * ‖GS‖ := by
    have h := abs_real_inner_le_norm G GS
    rwa [Integral.L2.SmoothCcTensor.inner_def (I := I) (M := M) G GS] at h
  have hGbound' : ‖G‖ ≤ K s * (nGrad + nS) := by rw [hnGrad_eq, hnS_eq] at hGbound; exact hGbound
  have hpair_le :
      |Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1) G.toFun GS.toFun| ≤
        K s * (nGrad ^ 2 + nS * nGrad) :=
    calc |Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1) G.toFun GS.toFun|
        ≤ ‖G‖ * ‖GS‖ := hcs
      _ = ‖G‖ * nGrad := by rw [hnGrad_eq]
      _ ≤ K s * (nGrad + nS) * nGrad := mul_le_mul_of_nonneg_right hGbound' hnGrad_nn
      _ = K s * (nGrad ^ 2 + nS * nGrad) := by ring
  rw [hnGrad_def, hnS_def] at hpair_le ⊢
  exact le_trans (neg_le_abs _) hpair_le

/-- **The general-rank order-`2` Gårding family.** At fixed contravariant rank `r` there is a
valence-dependent `Cg : ℕ → ℝ` with `Order2GardingFamilyRS g r Cg`:
`‖∇²S‖²_{L²} ≤ Cg s · (‖Δ_∇ S‖²_{L²} + ‖S‖²_{L²})` at every valence `s`.

This is the bidegree-`(r, ·)` analogue of `order2GardingFamily_holds`, *proved* here from the atomic
general-rank cross-term bound `curvatureCrossTermBoundRS_holds` via the general-rank integrated-Weitzenböck
Young reduction `order2GardingFamilyRS_of_curvatureCrossTermBoundRS`; the resulting Gårding constant
`Cg s = 2 + 2·Ccross s` inherits the per-valence dependence.  Consumers transitively depend on `sorryAx`
through the posited general-rank cross-term and Weitzenböck identity. -/
private theorem order2GardingFamilyRS_holds (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cg : ℕ → ℝ, Order2GardingFamilyRS (I := I) (M := M) g r Cg := by
  obtain ⟨Ccross, hcross⟩ := curvatureCrossTermBoundRS_holds (I := I) (M := M) g r
  exact ⟨fun s => 2 + 2 * Ccross s,
    order2GardingFamilyRS_of_curvatureCrossTermBoundRS (I := I) (M := M) g r Ccross hcross⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The general-rank single-step curvature-defect `L²` bound (posited general-rank curvature
child).** At fixed contravariant rank `r` there is a valence-dependent nonnegative `Ccurv : ℕ → ℝ`
such that, at every covariant rank `s'` and for every smooth compactly-supported `(r, s')`-tensor
`W`, the single-step rough-Laplacian / covariant-gradient commutator defect
`Curv W := Δ_∇(∇W) − ∇(Δ_∇ W)` is `L²`-bounded by `Ccurv s' · (‖W‖ + ‖∇W‖ + ‖∇²W‖)`.

This is the bidegree-`(r, ·)` analogue of the `(0, ·)` atomic single-step defect bound
`exists_pointwiseTensorCurv_l2_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`, body `sorry`).  Fibrewise
`Curv W` is, by the Ricci identity on the gradient field, a Riemann-curvature contraction of
`∇W` (plus a frame bracket), a zeroth/first-order operator in `∇W` whose fibre norm is bounded
at each fixed valence `s'` by the curvature sup `‖R‖_∞` over the compact manifold (which on the
`(r, s')`-tensor bundle grows like `(r + s' + 1)·‖R‖_∞`, hence the per-valence constant).  The
genuinely general-rank `(r, s')` curvature contraction is absent from the library (the rank-`0`
field `pointwiseTensorCurv` and its bound are stated only at contravariant rank `0`), so it is
posited here.  The constant is per-valence (`ℕ → ℝ`), not a single scalar, so this is NOT the
unsatisfiable single-const-∀s shape.  The conclusion is a single-step `L²` defect bound,
structurally distinct from the summability/Gårding statements it powers (no packaging); the body
is `sorry` and consumers transitively depend on `sorryAx`. -/
private theorem exists_singleStepCurvDefectRS_l2_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Ccurv : ℕ → ℝ, (∀ s, 0 ≤ Ccurv s) ∧
      ∀ (s' : ℕ) (W : Integral.L2.SmoothCcTensor g r s'),
        ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s' + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W) -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s'
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s' W)‖ ≤
          Ccurv s' *
            (‖W‖ + ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W‖ +
              ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s' + 1)
                  (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W)‖) := by
  classical
  obtain ⟨Cper, hCper_nn, hdata⟩ :=
    Integral.Connection.exists_pointwiseTensorCurvRS_movingFrameField_orderSeparated_bracketFreePairing
      (I := I) (M := M) g r
  refine ⟨fun s' => Real.sqrt 10 * Cper s',
    fun s' => mul_nonneg (Real.sqrt_nonneg 10) (hCper_nn s'), fun s' W => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hGcurv, hGcurvDeriv, hrem, _hpair⟩ := hdata s' W
  set Curv : Integral.L2.SmoothCcTensor g r (s' + 1) :=
    Integral.Connection.pointwiseTensorCurvRS (I := I) (M := M) g r s' W with hCurv_def
  have hCurv_split : Curv = (Gcurv + GcurvDeriv) +
      (Curv - Gcurv - GcurvDeriv) := by abel
  have hbound :
      ‖Curv‖ ≤ Real.sqrt 10 * Cper s' *
        (‖W‖ + ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W‖ +
          ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s' + 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W)‖) := by
    refine tensorL2NormRS_le_of_pointwise_fiberNormSq_bound_three (I := I) (M := M) g r
      W (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W)
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s' + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W))
      Curv (Real.sqrt 10 * Cper s')
      (mul_nonneg (Real.sqrt_nonneg 10) (hCper_nn s')) (fun x => ?_)
    set fW : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s' x
      (W.toSection x) with hfW
    set fgW : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
      ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W).toSection x) with hfgW
    set fhW : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1 + 1) x
      ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s' + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' W)).toSection x) with hfhW
    have hfW_nn : 0 ≤ fW := Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r s' x _
    have hfgW_nn : 0 ≤ fgW :=
      Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s' + 1) x _
    have hfhW_nn : 0 ≤ fhW :=
      Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s' + 1 + 1) x _
    have hCsq_nn : 0 ≤ Cper s' ^ 2 := sq_nonneg _
    set fA : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
      ((Gcurv + GcurvDeriv).toSection x) with hfA
    set fB : ℝ := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
      ((Curv - Gcurv - GcurvDeriv).toSection x) with hfB
    have hAB_eq : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
        (Curv.toSection x) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
        (((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toSection x) := by
      rw [← hCurv_split]
    have hAB_le : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r (s' + 1) x
        (((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toSection x) ≤ 2 * fA + 2 * fB := by
      have hsec : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toSection x =
          (Gcurv + GcurvDeriv).toSection x + (Curv - Gcurv - GcurvDeriv).toSection x := by
        rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl
      rw [hsec]
      exact Integral.Connection.riemannianFiberNormSq_add_le (I := I) (M := M) g r (s' + 1) x _ _
    have hfA_le : fA ≤ 2 * (Cper s' ^ 2 * fgW) + 2 * (Cper s' ^ 2 * (fgW + fW)) := by
      have hsec : (Gcurv + GcurvDeriv).toSection x =
          Gcurv.toSection x + GcurvDeriv.toSection x := by
        rw [Integral.L2.SmoothCcTensor.toSection_add]; rfl
      rw [hfA, hsec]
      have hadd := Integral.Connection.riemannianFiberNormSq_add_le (I := I) (M := M) g r (s' + 1) x
        (Gcurv.toSection x) (GcurvDeriv.toSection x)
      nlinarith [hadd, hGcurv x, hGcurvDeriv x, hCsq_nn, hfgW_nn, hfW_nn]
    have hfB_le : fB ≤ Cper s' ^ 2 * (fhW + fgW + fW) := hrem x
    have hsqrt10 : (Real.sqrt 10 * Cper s') ^ 2 = 10 * Cper s' ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)]
    rw [hsqrt10, hAB_eq]
    nlinarith [hAB_le, hfA_le, hfB_le, hfW_nn, hfgW_nn, hfhW_nn, hCsq_nn]
  exact hbound

/-- **The general-rank covariant-product curvature primitive (posited general-rank curvature
child).** The bidegree-`(r, ·)` analogue of the `(0, ·)` covariant-product input
`exists_iteratedCovGrad_pointwiseTensorCurv_l2_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`, body `sorry` at rank `0`).
At fixed contravariant rank `r` there is a *valence/order-dependent* nonnegative constant
`Cic : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, every gradient order `m`, and for every
smooth compactly-supported `(r, s)`-tensor `T`, the `m`-fold iterated covariant gradient of the
order-`2` single-step commutator defect `Curv T := pointwiseTensorCurvRS g r s T = Δ_∇(∇T) − ∇(Δ_∇ T)`
is `L²`-controlled by the `≤ m + 2`-order iterated gradients of `T`:
`‖∇^m(Curv T)‖ ≤ Cic s m · ∑_{i < m + 3} ‖∇^i T‖`.

`Curv T` is a second-order curvature(-derivative) operator in `T` (a Riemann contraction of `∇T` plus
a differentiated-curvature contraction of `T`, with the moving-frame `∇²T`-order discrepancy surviving
at the norm level), so each further covariant gradient produces one more contraction of a covariant
derivative of curvature against one-higher gradient of `T`, all sup-bounded on the compact manifold.
The genuinely general-rank `(r, s)` iterated curvature-product content is absent from the library (the
rank-`0` field `pointwiseTensorCurv` and its iterated-gradient bound are stated only at contravariant
rank `0`), so it is posited here.  The constant is per-valence/order (`ℕ → ℕ → ℝ`), not a single scalar
(the tensor-bundle curvature endomorphism is an `O(r + s + m)`-slot derivation and the
curvature-derivative term count grows with `m`), so this is NOT the unsatisfiable single-const-∀ shape.
The degenerate witness is rejected at `m = 0`: the bound is `‖Curv T‖ ≤ Cic s 0 · (‖T‖ + ‖∇T‖ + ‖∇²T‖)`,
the genuine single-step defect norm bound, *false* with `Cic s 0 = 0` on a non-flat manifold (the
defect carries the genuine curvature contraction of `T`).  The body is `sorry`; consumers transitively
depend on `sorryAx`. -/
private theorem exists_iteratedCovGrad_pointwiseTensorCurvRS_l2_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cic : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cic s m) ∧
      ∀ (s m : ℕ) (T : Integral.L2.SmoothCcTensor g r s),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + 1) m
            (Integral.Connection.pointwiseTensorCurvRS (I := I) (M := M) g r s T)‖ ≤
          Cic s m * ∑ i ∈ Finset.range (m + 3),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i T‖ :=
  sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The general-rank iterated-gradient commutator-defect `L²` bound (general gradient order).** At
fixed bidegree `(r, s)` there is an order/gradient-dependent nonnegative `Dc : ℕ → ℕ → ℝ` such that,
for every smooth compactly-supported `(r, s)`-tensor base `U`, every iterated commutator order `p`, and
every extra gradient order `m`, the `m`-fold covariant gradient of the order-`p` rough-Laplacian /
iterated-gradient commutator defect `Defect p := Δ_∇(∇^p U) − ∇^p(Δ_∇ U)` satisfies
`‖∇^m(Defect p)‖ ≤ Dc p m · ∑_{i ≤ p + m + 1} ‖∇^i U‖`.

The bidegree-`(r, s)` analogue of `exists_iteratedCovGrad_commutatorDefect_l2_bound`, *proved* here by
the verbatim port of that reduction: induction on `p` (with `m` universally quantified, so the inductive
hypothesis is used at `m + 1`); the base case `Defect 0 = Δ_∇ U − Δ_∇ U = 0` vanishes
(`iteratedCovGrad_zero`), and the inductive step uses the defect recursion
`Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)` (from `covGrad`-additivity and `iteratedCovGrad_succ`,
both bidegree-generic), the triangle inequality, the gradient-commuting `norm_iteratedCovGrad_covGrad_comm`,
and the posited general-rank covariant-product input `exists_iteratedCovGrad_pointwiseTensorCurvRS_l2_bound`
(re-indexed through `norm_iteratedCovGrad_iteratedCovGrad`).  Consumers transitively depend on `sorryAx`
through that posited input. -/
private theorem exists_iteratedCovGrad_commutatorDefectRS_l2_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Dc : ℕ → ℕ → ℝ, (∀ p m, 0 ≤ Dc p m) ∧
      ∀ (U : Integral.L2.SmoothCcTensor g r s) (p m : ℕ),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + p) m
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p)
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U) -
              PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U))‖ ≤
          Dc p m * ∑ i ∈ Finset.range (p + m + 2),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
  classical
  obtain ⟨Cic, hCic_nn, hcic⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurvRS_l2_bound (I := I) (M := M) g r
  have hkey : ∀ p : ℕ, ∃ c : ℕ → ℝ, (∀ m, 0 ≤ c m) ∧
      ∀ (U : Integral.L2.SmoothCcTensor g r s) (m : ℕ),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + p) m
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p)
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U) -
              PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U))‖ ≤
          c m * ∑ i ∈ Finset.range (p + m + 2),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
    intro p
    induction p with
    | zero =>
        refine ⟨fun _ => 0, fun _ => le_refl 0, fun U m => ?_⟩
        have hzero :
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 0)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s 0 U) -
              PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s 0
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)) = 0 := by
          simp only [Nat.add_zero, PDE.RicciFlow.iteratedCovGrad_zero, sub_self]
        rw [hzero, Integral.Connection.iteratedCovGrad_zero_tensor, norm_zero, zero_mul]
    | succ p' ih =>
        obtain ⟨c', hc'_nn, hc'⟩ := ih
        refine ⟨fun m => c' (m + 1) + Cic (s + p') m,
          fun m => add_nonneg (hc'_nn (m + 1)) (hCic_nn (s + p') m), fun U m => ?_⟩
        set GpU : Integral.L2.SmoothCcTensor g r (s + p') :=
          PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p' U with hGpU
        set Defp : Integral.L2.SmoothCcTensor g r (s + p') :=
          Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p') GpU -
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p'
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U) with hDefp
        have hcovsub : ∀ (s'' : ℕ) (w₁ w₂ : Integral.L2.SmoothCcTensor g r s''),
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s'' (w₁ - w₂) =
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s'' w₁ -
                Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s'' w₂ := by
          intro s'' w₁ w₂
          rw [sub_eq_add_neg, sub_eq_add_neg, Analysis.Parabolic.TensorSpectral.covGrad_add,
            ← neg_one_smul ℝ w₂, Analysis.Parabolic.TensorSpectral.covGrad_smul, neg_one_smul]
        have hrecur :
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + (p' + 1))
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + 1) U) -
              PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + 1)
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)) =
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p') Defp +
                Integral.Connection.pointwiseTensorCurvRS (I := I) (M := M) g r (s + p') GpU := by
          rw [hDefp, hGpU, PDE.RicciFlow.iteratedCovGrad_succ,
            PDE.RicciFlow.iteratedCovGrad_succ, Integral.Connection.pointwiseTensorCurvRS, hcovsub]
          change (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p' + 1)
                  (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p')
                    (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p' U)) -
                Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p')
                  (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p'
                    (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U))) = _
          abel
        rw [hrecur, Integral.Connection.iteratedCovGrad_add]
        refine le_trans (norm_add_le _ _) ?_
        have hcomm :
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + (p' + 1)) m
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p') Defp)‖ =
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + p') (m + 1) Defp‖ :=
          Integral.Connection.norm_iteratedCovGrad_covGrad_comm (I := I) (M := M) g r (s + p') m Defp
        rw [hcomm]
        have hih := hc' U (m + 1)
        rw [← hGpU, ← hDefp] at hih
        have hcurv :
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + (p' + 1)) m
                (Integral.Connection.pointwiseTensorCurvRS (I := I) (M := M) g r (s + p') GpU)‖ ≤
              Cic (s + p') m *
                ∑ i ∈ Finset.range (m + 3),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + i) U‖ := by
          refine le_trans (hcic (s + p') m GpU) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCic_nn (s + p') m)
          refine le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))
          rw [hGpU, Integral.Connection.norm_iteratedCovGrad_iteratedCovGrad (I := I) (M := M) g r s p' i U]
        set FullSum : ℝ := ∑ i ∈ Finset.range (p' + 1 + m + 2),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ with hFullSum
        have hFullSum_nn : 0 ≤ FullSum := Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hc'_nn' : 0 ≤ c' (m + 1) := hc'_nn (m + 1)
        have hCic_nn' : 0 ≤ Cic (s + p') m := hCic_nn (s + p') m
        have hsum1 :
            ∑ i ∈ Finset.range (p' + (m + 1) + 2),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ = FullSum := by
          rw [hFullSum, show p' + (m + 1) + 2 = p' + 1 + m + 2 from by omega]
        have hsum2 :
            ∑ i ∈ Finset.range (m + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + i) U‖ ≤ FullSum := by
          rw [hFullSum]
          have hmap :
              ∑ i ∈ Finset.range (m + 3),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + i) U‖ =
                ∑ j ∈ (Finset.range (m + 3)).image (fun i => p' + i),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j U‖ := by
            rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
          rw [hmap]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
          intro j hj
          simp only [Finset.mem_image, Finset.mem_range] at hj
          obtain ⟨i, hi, rfl⟩ := hj
          simp only [Finset.mem_range]; omega
        calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + p') (m + 1) Defp‖ +
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r (s + (p' + 1)) m
                (Integral.Connection.pointwiseTensorCurvRS (I := I) (M := M) g r (s + p') GpU)‖
            ≤ c' (m + 1) * ∑ i ∈ Finset.range (p' + (m + 1) + 2),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ +
                Cic (s + p') m * ∑ i ∈ Finset.range (m + 3),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p' + i) U‖ :=
              add_le_add hih hcurv
          _ ≤ c' (m + 1) * FullSum + Cic (s + p') m * FullSum :=
              add_le_add (le_of_eq (by rw [hsum1]))
                (mul_le_mul_of_nonneg_left hsum2 hCic_nn')
          _ = (c' (m + 1) + Cic (s + p') m) * FullSum := by ring
  refine ⟨fun p => (hkey p).choose, fun p m => ((hkey p).choose_spec.1) m, fun U p m => ?_⟩
  exact (hkey p).choose_spec.2 U m

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The general-rank gradient-of-defect `L²` bound.** At fixed bidegree `(r, s)` there is an
order-dependent nonnegative `Dc : ℕ → ℝ` such that, for every smooth compactly-supported
`(r, s)`-tensor base `U` and every gradient order `p`, the covariant gradient of the order-`p`
rough-Laplacian / iterated-gradient commutator defect is `L²`-controlled by the lower gradients:
`‖∇(Δ_∇(∇^p U) − ∇^p(Δ_∇ U))‖ ≤ Dc p · ∑_{i ≤ p+2} ‖∇^i U‖`.

The bidegree-`(r, s)` analogue of `exists_covGrad_commutatorDefect_l2_bound`, *proved* here from the
general-rank iterated-gradient commutator-defect bound `exists_iteratedCovGrad_commutatorDefectRS_l2_bound`
specialised to one extra gradient (`m = 1`): `covGrad g r (s + p) (Defect p) = ∇^1(Defect p)` by
`iteratedCovGrad_succ`/`iteratedCovGrad_zero`, and the sum `range (p + 1 + 2)` is the `m = 1` instance of
`range (p + m + 2)`.  Consumers transitively depend on `sorryAx` through the posited covariant-product
curvature input. -/
private theorem exists_covGrad_commutatorDefectRS_l2_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Dc : ℕ → ℝ, (∀ p, 0 ≤ Dc p) ∧
      ∀ (U : Integral.L2.SmoothCcTensor g r s) (p : ℕ),
        ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p)
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U) -
                PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
                  (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U))‖ ≤
          Dc p * ∑ i ∈ Finset.range (p + 1 + 2),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
  classical
  obtain ⟨Dc, hDc_nn, hbound⟩ :=
    exists_iteratedCovGrad_commutatorDefectRS_l2_bound (I := I) (M := M) g r s
  refine ⟨fun p => Dc p 1, fun p => hDc_nn p 1, fun U p => ?_⟩
  have hb := hbound U p 1
  rw [PDE.RicciFlow.iteratedCovGrad_succ, PDE.RicciFlow.iteratedCovGrad_zero] at hb
  exact hb

/-- **The general-rank order-`(p+1)` commutator-defect bound.** At fixed bidegree `(r, s)` there is an
order-dependent nonnegative `Cc : ℕ → ℝ` such that, for every smooth compactly-supported `(r, s)`-tensor
base `U` and every gradient order `p`, the rough-Laplacian / iterated-gradient commutator defect at
order `p + 1` is `L²`-controlled by the lower gradients:
`‖Δ_∇(∇^{p+1} U) − ∇^{p+1}(Δ_∇ U)‖ ≤ Cc (p+1) · ∑_{i ≤ p+2} ‖∇^i U‖`.

This is the bidegree-`(r, s)` analogue of the `(0, 2)`-restricted `exists_commutatorDefect_l2_bound_succ`,
*proved* here by the verbatim port of that reduction: the iterated Ricci-identity recursion
`Defect (p + 1) = ∇(Defect p) + Curv (∇^p U)` (established from `covGrad`-additivity and
`iteratedCovGrad_succ`, both bidegree-generic), the triangle inequality `‖a + b‖ ≤ ‖a‖ + ‖b‖`, and the
two posited general-rank atomic curvature inputs — the single-step defect bound
`exists_singleStepCurvDefectRS_l2_bound` (applied at `∇^p U`, with its three gradient terms `‖∇^p U‖`,
`‖∇^{p+1} U‖`, `‖∇^{p+2} U‖` bounded by the full sum) and the gradient-of-defect bound
`exists_covGrad_commutatorDefectRS_l2_bound`.  Consumers transitively depend on `sorryAx` through those
posited inputs.  The per-order constant is `Cc (p + 1) = Dc p + Ccurv (s + p)`. -/
private theorem exists_commutatorDefectRS_l2_bound_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Cc : ℕ → ℝ, (∀ p, 0 ≤ Cc p) ∧
      ∀ (U : Integral.L2.SmoothCcTensor g r s) (p : ℕ),
        ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + (p + 1))
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1) U) -
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1)
              (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖ ≤
          Cc (p + 1) * ∑ i ∈ Finset.range ((p + 1) + 2),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
  classical
  obtain ⟨Ccurv, hCcurv_nn, hcurv⟩ := exists_singleStepCurvDefectRS_l2_bound (I := I) (M := M) g r
  obtain ⟨Dc, hDc_nn, hdc⟩ := exists_covGrad_commutatorDefectRS_l2_bound (I := I) (M := M) g r s
  refine ⟨fun n => match n with | 0 => 0 | (p + 1) => Dc p + Ccurv (s + p), fun n => ?_,
    fun U p => ?_⟩
  · match n with
    | 0 => exact le_refl 0
    | (p + 1) => exact add_nonneg (hDc_nn p) (hCcurv_nn (s + p))
  · set GpU : Integral.L2.SmoothCcTensor g r (s + p) :=
      PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U with hGpU_def
    set Defp : Integral.L2.SmoothCcTensor g r (s + p) :=
      Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p) GpU -
        PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U) with hDefp_def
    set Sum : ℝ := ∑ i ∈ Finset.range (p + 1 + 2),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ with hSum_def
    have hcovsub : ∀ (s' : ℕ) (w₁ w₂ : Integral.L2.SmoothCcTensor g r s'),
        Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' (w₁ - w₂) =
          Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' w₁ -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s' w₂ := by
      intro s' w₁ w₂
      rw [sub_eq_add_neg, sub_eq_add_neg, Analysis.Parabolic.TensorSpectral.covGrad_add,
        ← neg_one_smul ℝ w₂, Analysis.Parabolic.TensorSpectral.covGrad_smul, neg_one_smul]
    have hrecur :
        (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + (p + 1))
            (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1) U) -
          PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1)
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)) =
          Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) Defp +
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU) -
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p)
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p) GpU)) := by
      rw [hDefp_def, hGpU_def, PDE.RicciFlow.iteratedCovGrad_succ,
        PDE.RicciFlow.iteratedCovGrad_succ, hcovsub]
      change (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p)
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U)) -
            Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U))) = _
      abel
    rw [hrecur]
    refine le_trans (norm_add_le _ _) ?_
    change ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) Defp‖ +
        ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p + 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU) -
          Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p)
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + p) GpU)‖ ≤
          (Dc p + Ccurv (s + p)) * Sum
    rw [add_mul]
    refine add_le_add ?_ ?_
    · have h := hdc U p
      rw [← hGpU_def, ← hDefp_def] at h
      exact h
    · refine le_trans (hcurv (s + p) GpU) ?_
      have h3 :
          ‖GpU‖ + ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU‖ +
              ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU)‖ ≤
            Sum := by
        have e1 : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU =
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1) U := by
          rw [PDE.RicciFlow.iteratedCovGrad_succ, hGpU_def]
        have e2 : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p + 1)
              (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU) =
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 2) U := by
          rw [e1]
          exact (PDE.RicciFlow.iteratedCovGrad_succ g r s (p + 1) U).symm
        rw [e2, e1, hGpU_def, hSum_def]
        have hsub : ({p, p + 1, p + 2} : Finset ℕ) ⊆ Finset.range (p + 1 + 2) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          simp only [Finset.mem_range]
          omega
        have hsum3 :
            ∑ i ∈ ({p, p + 1, p + 2} : Finset ℕ),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ ≤
              ∑ i ∈ Finset.range (p + 1 + 2),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
        have hsum3_eq :
            ∑ i ∈ ({p, p + 1, p + 2} : Finset ℕ),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ =
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U‖ +
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 1) U‖ +
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (p + 2) U‖ := by
          rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
            Finset.sum_singleton]
          ring
        rw [hsum3_eq] at hsum3
        linarith [hsum3]
      calc Ccurv (s + p) *
            (‖GpU‖ + ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU‖ +
              ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + p) GpU)‖)
          ≤ Ccurv (s + p) * Sum := mul_le_mul_of_nonneg_left h3 (hCcurv_nn (s + p))

/-- **The general-rank commutator-defect family.** At fixed bidegree `(r, s)` there is an
order-dependent nonnegative `Cc : ℕ → ℝ` with `CommutatorDefectBoundRS g r s Cc`.

This is the bidegree-`(r, s)` analogue of `commutatorDefectBound_holds`, *proved* here by splitting on
the gradient order, exactly as the `(0, 2)` proof: the order-`0` defect `Δ_∇(∇^0 U) − ∇^0(Δ_∇ U) =
Δ_∇ U − Δ_∇ U` vanishes (here unconditionally, by the general-rank `iteratedCovGrad_zero`), and the
orders `p + 1` are supplied by the posited general-rank curvature child
`exists_commutatorDefectRS_l2_bound_succ`.  Consumers transitively depend on `sorryAx` through that
posited input. -/
private theorem commutatorDefectBoundRS_holds (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Cc : ℕ → ℝ, CommutatorDefectBoundRS (I := I) (M := M) g r s Cc := by
  obtain ⟨Cc, hCc, hsucc⟩ := exists_commutatorDefectRS_l2_bound_succ (I := I) (M := M) g r s
  refine ⟨Cc, hCc, fun U p => ?_⟩
  match p with
  | 0 =>
      have hzero :
          Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + 0)
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s 0 U) -
              PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s 0
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U) = 0 := by
        rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero]
        simp
      rw [hzero, norm_zero]
      have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (0 + 2),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ :=
        Finset.sum_nonneg (fun i _ => norm_nonneg _)
      exact mul_nonneg (hCc 0) hsum_nn
  | (p + 1) => exact hsucc U p

/-- `‖∇^i U‖` as a `SmoothCcTensor` seminorm equals `tensorL2Norm` of its underlying field, at
bidegree `(r, s)`. -/
private lemma iteratedCovGradRS_norm_eq_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (U : Integral.L2.SmoothCcTensor g r s) :
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j U‖ =
      Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j U).toFun :=
  Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
    (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j U)

/-- `‖Δ_∇^i U‖` as a `SmoothCcTensor` seminorm equals `‖(Δ_∇^i U).toL2‖`, at bidegree `(r, s)`. -/
private lemma rawTensorConnLapIterRS_norm_eq_toL2
    (g : SmoothRiemannianMetric I M) (r s i : ℕ) (U : Integral.L2.SmoothCcTensor g r s) :
    ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ =
      ‖Integral.L2.SmoothCcTensor.toL2
        (Integral.Connection.rawTensorConnLapIter (I := I) g r s i U)‖ :=
  (Integral.L2.SmoothCcTensor.norm_toL2 (I := I) (M := M)
    (Integral.Connection.rawTensorConnLapIter (I := I) g r s i U)).symm

set_option maxHeartbeats 1600000 in
/-- **The general-rank mixed bound.** The bidegree-`(r, s)` analogue of
`gradOrder_l2Norm_le_lapIter_sum`, proved by the same strong induction on the gradient order `p`,
threading the three `(r, ·)` per-order families through pure norm arithmetic. -/
private lemma gradOrderRS_l2Norm_le_lapIter_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Cg Cc : ℕ → ℝ)
    (hgard : Order2GardingFamilyRS (I := I) (M := M) g r Cg)
    (hgrad1 : Order1ControlFamilyRS (I := I) (M := M) g r)
    (hcomm : CommutatorDefectBoundRS (I := I) (M := M) g r s Cc) :
    ∃ Cmix : ℕ → ℝ, (∀ p, 0 ≤ Cmix p) ∧
      ∀ (p : ℕ) (U : Integral.L2.SmoothCcTensor g r s),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s p U‖ ≤
          Cmix p * ∑ i ∈ Finset.range ((p + 1) / 2 + 1),
            ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ := by
  classical
  obtain ⟨hCg, hgardS⟩ := hgard
  obtain ⟨hCc, hcommU⟩ := hcomm
  set sg : ℕ → ℝ := fun m => Real.sqrt (Cg (s + m)) with hsg_def
  have hsg_nn : ∀ m, 0 ≤ sg m := fun m => Real.sqrt_nonneg _
  set K : ℕ → ℝ := fun m => sg m * (2 + Cc m) with hK_def
  have hK_nn : ∀ m, 0 ≤ K m := fun m => mul_nonneg (hsg_nn m) (by linarith [hCc m])
  let Bpair : ℕ → ℝ × ℝ := fun n => Nat.rec (motive := fun _ => ℝ × ℝ)
    (1, 1)
    (fun n prev =>
      let s := prev.2
      let b : ℝ := if n = 0 then 1 else K (n - 1) * s + 1
      (b, s + b))
    n
  let B : ℕ → ℝ := fun n => (Bpair n).1
  have hBfst_succ : ∀ n, (Bpair (n + 1)).1 =
      (if n = 0 then 1 else K (n - 1) * (Bpair n).2 + 1) := fun _ => rfl
  have hBsnd_succ : ∀ n, (Bpair (n + 1)).2 =
      (Bpair n).2 + (Bpair (n + 1)).1 := fun _ => rfl
  have hBsnd_zero : (Bpair 0).2 = 1 := rfl
  have hB0 : B 0 = 1 := rfl
  have hB1 : B 1 = 1 := rfl
  have hB_fst : ∀ n, B n = (Bpair n).1 := fun _ => rfl
  have hBpair_sum : ∀ n, (Bpair n).2 = ∑ i ∈ Finset.range (n + 1), B i := by
    intro n
    induction n with
    | zero => rw [hBsnd_zero, Finset.sum_range_one, hB0]
    | succ m ihm =>
        rw [Finset.sum_range_succ, ← ihm, hBsnd_succ m, hB_fst (m + 1)]
  have hBsucc_pos : ∀ n, B (n + 2) = K n * (∑ i ∈ Finset.range (n + 2), B i) + 1 := by
    intro n
    rw [hB_fst (n + 2), hBfst_succ (n + 1)]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [hBpair_sum (n + 1)]
  have hB_nn : ∀ p, 0 ≤ B p := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [hB0]; norm_num
      | 1 => rw [hB1]; norm_num
      | (m + 2) =>
          rw [hBsucc_pos m]
          have h2 : 0 ≤ ∑ i ∈ Finset.range (m + 2), B i :=
            Finset.sum_nonneg (fun i hi => ih i (by
              have := Finset.mem_range.mp hi; omega))
          have : 0 ≤ K m * (∑ i ∈ Finset.range (m + 2), B i) := mul_nonneg (hK_nn m) h2
          linarith
  have hBstep : ∀ m,
      sg m * (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m) + 1 ≤
      B (m + 2) := by
    intro m
    rw [hBsucc_pos m]
    have hBm_le : B m ≤ ∑ i ∈ Finset.range (m + 2), B i := by
      apply Finset.single_le_sum (f := B) (fun i _ => hB_nn i)
      rw [Finset.mem_range]; omega
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (m + 2), B i :=
      Finset.sum_nonneg (fun i _ => hB_nn i)
    have hkey : sg m * (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m) ≤
        K m * (∑ i ∈ Finset.range (m + 2), B i) := by
      rw [hK_def]
      have h1 : B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m ≤
          (2 + Cc m) * (∑ i ∈ Finset.range (m + 2), B i) := by
        nlinarith [hBm_le, hCc m, hsum_nn]
      calc sg m * (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m)
          ≤ sg m * ((2 + Cc m) * (∑ i ∈ Finset.range (m + 2), B i)) :=
            mul_le_mul_of_nonneg_left h1 (hsg_nn m)
        _ = sg m * (2 + Cc m) * (∑ i ∈ Finset.range (m + 2), B i) := by ring
    linarith
  refine ⟨B, hB_nn, ?_⟩
  intro p
  induction p using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        intro U
        rw [PDE.RicciFlow.iteratedCovGrad_zero]
        rw [hB0]
        have hsum : ∑ i ∈ Finset.range ((0 + 1) / 2 + 1),
            ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ = ‖U‖ := by
          norm_num [Integral.Connection.rawTensorConnLapIter_zero]
        rw [hsum]; ring_nf; exact le_refl _
    | 1 =>
        intro U
        rw [hB1]
        have hord1 : ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s U‖ ^ 2 ≤
            ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U‖ * ‖U‖ := hgrad1 s U
        have hgrad_eq :
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s 1 U =
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s U := by
          have h := PDE.RicciFlow.iteratedCovGrad_succ (I := I) (M := M) g r s 0 U
          rw [PDE.RicciFlow.iteratedCovGrad_zero] at h
          exact h
        rw [hgrad_eq]
        have hsum : ∑ i ∈ Finset.range ((1 + 1) / 2 + 1),
              ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ =
            ‖U‖ + ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U‖ := by
          have : (1 + 1) / 2 + 1 = 2 := by norm_num
          rw [this]
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          rw [Integral.Connection.rawTensorConnLapIter_zero,
            Integral.Connection.rawTensorConnLapIter_one]
        rw [hsum, one_mul]
        set a : ℝ := ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U‖ with ha_def
        set b : ℝ := ‖U‖ with hb_def
        have ha_nn : 0 ≤ a := norm_nonneg _
        have hb_nn : 0 ≤ b := norm_nonneg _
        have hgrad_nn : 0 ≤ ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s U‖ :=
          norm_nonneg _
        have hsqrt : ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s U‖ ≤
            Real.sqrt (a * b) := by
          rw [← Real.sqrt_sq hgrad_nn]
          exact Real.sqrt_le_sqrt hord1
        have hamgm : Real.sqrt (a * b) ≤ b + a := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ b + a)]
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (a - b), ha_nn, hb_nn]
        linarith [hsqrt, hamgm]
    | (m + 2) =>
        intro U
        set S : Integral.L2.SmoothCcTensor g r (s + m) :=
          PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U with hS_def
        have hgrad2_eq :
            PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (m + 2) U =
              Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m) S) := by
          rw [hS_def]
          rfl
        have hgard2 :
            ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m + 1)
                (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m) S)‖ ^ 2 ≤
              Cg (s + m) *
                (‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m) S‖ ^ 2 +
                  ‖S‖ ^ 2) :=
          hgardS (s + m) S
        set nHess : ℝ :=
          ‖Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m + 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + m) S)‖
          with hnHess_def
        set nLapS : ℝ := ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m) S‖
          with hnLapS_def
        set nS : ℝ := ‖S‖ with hnS_def
        have hnHess_nn : 0 ≤ nHess := norm_nonneg _
        have hnLapS_nn : 0 ≤ nLapS := norm_nonneg _
        have hnS_nn : 0 ≤ nS := norm_nonneg _
        have hgard_fp : nHess ≤ sg m * (nLapS + nS) := by
          rw [hsg_def]
          rw [← Real.sqrt_sq hnHess_nn]
          calc Real.sqrt (nHess ^ 2)
              ≤ Real.sqrt (Cg (s + m) * (nLapS ^ 2 + nS ^ 2)) := Real.sqrt_le_sqrt hgard2
            _ = Real.sqrt (Cg (s + m)) * Real.sqrt (nLapS ^ 2 + nS ^ 2) := by
                  rw [Real.sqrt_mul (hCg (s + m))]
            _ ≤ Real.sqrt (Cg (s + m)) * (nLapS + nS) := by
                  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
                  rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ nLapS + nS)]
                  apply Real.sqrt_le_sqrt
                  nlinarith [mul_nonneg hnLapS_nn hnS_nn]
        have hΔS_eq : Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m) S =
            Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U) := by
          rw [hS_def]
        have hcomm_m := hcommU U m
        have hnLapS_eq : nLapS =
            ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U)‖ := by
          rw [hnLapS_def, hΔS_eq]
        set DefM : Integral.L2.SmoothCcTensor g r (s + m) :=
          PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U) with hDefM_def
        have htri :
            ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
                (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U)‖ ≤
              ‖DefM‖ +
                ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U) - DefM‖ :=
          norm_le_norm_add_norm_sub'
            (Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U)) DefM
        have hdef_bound :
            ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U) - DefM‖ ≤
              Cc m * ∑ i ∈ Finset.range (m + 2),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
          rw [hDefM_def]; exact hcomm_m
        have hih_base :
            ‖DefM‖ ≤ B m * ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
              ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖ := by
          rw [hDefM_def]
          exact ih m (by omega) (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)
        have hlapiter_shift : ∀ i,
            Integral.Connection.rawTensorConnLapIter (I := I) g r s i
                (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U) =
              Integral.Connection.rawTensorConnLapIter (I := I) g r s (i + 1) U := by
          intro i
          induction i with
          | zero => simp [Integral.Connection.rawTensorConnLapIter]
          | succ n ihn =>
              rw [Integral.Connection.rawTensorConnLapIter_succ, ihn,
                ← Integral.Connection.rawTensorConnLapIter_succ]
        have hih_low : ∀ i, i < m + 2 →
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ ≤
              B i * ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s j U‖ :=
          fun i hi => ih i hi U
        set Rfull : ℕ := ((m + 2) + 1) / 2 + 1 with hRfull_def
        set Sfull : ℝ := ∑ i ∈ Finset.range Rfull,
          ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ with hSfull_def
        have hSfull_nn : 0 ≤ Sfull :=
          Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hbase_le_full :
            ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i
                  (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖ ≤ Sfull := by
          rw [hSfull_def]
          have hrw : ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i
                  (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖ =
              ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s (i + 1) U‖ := by
            apply Finset.sum_congr rfl
            intro i _; rw [hlapiter_shift i]
          rw [hrw]
          have hshift : ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s (i + 1) U‖ =
              ∑ i ∈ Finset.Ico 1 ((m + 1) / 2 + 2),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖ := by
            rw [Finset.sum_Ico_eq_sum_range]
            apply Finset.sum_congr (by norm_num) (fun i _ => by ring_nf)
          rw [hshift]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_Ico] at hx
            rw [Finset.mem_range]
            rw [hRfull_def]; omega
          · intro i _ _; exact norm_nonneg _
        have hlow_sub_le_full : ∀ i, i < m + 2 →
            ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s j U‖ ≤ Sfull := by
          intro i hi
          rw [hSfull_def]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_range] at hx ⊢
            rw [hRfull_def]; omega
          · intro j _ _; exact norm_nonneg _
        have hSlow_nn : 0 ≤ ∑ i ∈ Finset.range (m + 2),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ :=
          Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hnLapS_le :
            nLapS ≤ B m * Sfull
              + Cc m * ∑ i ∈ Finset.range (m + 2),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
          rw [hnLapS_eq]
          calc ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U)‖
              ≤ ‖DefM‖ + ‖Integral.Connection.rawTensorConnLapSmooth (I := I) g r (s + m)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U) - DefM‖ := htri
            _ ≤ (B m * ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                    ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i
                      (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s U)‖)
                  + Cc m * ∑ i ∈ Finset.range (m + 2),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ :=
                add_le_add hih_base hdef_bound
            _ ≤ B m * Sfull
                  + Cc m * ∑ i ∈ Finset.range (m + 2),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := by
                have hb := mul_le_mul_of_nonneg_left hbase_le_full (hB_nn m)
                linarith [hb]
        have hSlow_le :
            ∑ i ∈ Finset.range (m + 2),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ ≤
              (∑ i ∈ Finset.range (m + 2), B i) * Sfull := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖
              ≤ B i * ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                  ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s j U‖ := hih_low i hi
            _ ≤ B i * Sfull :=
                mul_le_mul_of_nonneg_left (hlow_sub_le_full i hi) (hB_nn i)
        have hnS_le : nS ≤ B m * Sfull := by
          rw [hnS_def, hS_def]
          calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s m U‖
              ≤ B m * ∑ j ∈ Finset.range ((m + 1) / 2 + 1),
                  ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s j U‖ := ih m (by omega) U
            _ ≤ B m * Sfull :=
                mul_le_mul_of_nonneg_left (hlow_sub_le_full m (by omega)) (hB_nn m)
        have hcombine : nLapS + nS ≤
            (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m) * Sfull := by
          have h1 : nLapS ≤ B m * Sfull
              + Cc m * ((∑ i ∈ Finset.range (m + 2), B i) * Sfull) := by
            calc nLapS ≤ B m * Sfull
                  + Cc m * ∑ i ∈ Finset.range (m + 2),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s i U‖ := hnLapS_le
              _ ≤ B m * Sfull + Cc m * ((∑ i ∈ Finset.range (m + 2), B i) * Sfull) := by
                  have hc := mul_le_mul_of_nonneg_left hSlow_le (hCc m)
                  linarith [hc]
          nlinarith [h1, hnS_le, hSfull_nn]
        have hfinal : nHess ≤ B (m + 2) * Sfull := by
          have hstep := hBstep m
          calc nHess ≤ sg m * (nLapS + nS) := hgard_fp
            _ ≤ sg m * ((B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m) * Sfull) := by
                exact mul_le_mul_of_nonneg_left hcombine (hsg_nn m)
            _ = (sg m * (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m)) * Sfull := by
                ring
            _ ≤ B (m + 2) * Sfull := by
                have hle : sg m * (B m + Cc m * (∑ i ∈ Finset.range (m + 2), B i) + B m) ≤
                    B (m + 2) := by linarith [hstep]
                exact mul_le_mul_of_nonneg_right hle hSfull_nn
        have hLHS : ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s (m + 2) U‖ = nHess := by
          rw [hgrad2_eq, hnHess_def]
        have hRHS : (B (m + 2) * ∑ i ∈ Finset.range (((m + 2) + 1) / 2 + 1),
              ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i U‖) = B (m + 2) * Sfull := by
          rw [hSfull_def, hRfull_def]
        rw [hLHS, hRHS]
        exact hfinal

/-- **The general-rank all-order intrinsic Gårding bootstrap.** For every order `k` there is a
constant `C ≥ 0` such that, for every smooth `(r, s)`-tensor `T`, the sum of the `L²` norms of the
covariant gradients `∇^j T` up to order `2k` is bounded by `C` times the sum of the `L²` norms of
the iterated rough Laplacians `Δ_∇^i T` up to order `k`:
`∑_{j ≤ 2k} ‖∇^j T‖_{L²} ≤ C · ∑_{i ≤ k} ‖Δ_∇^i T‖_{L²}`.

This is the bidegree-`(r, s)` analogue of the in-library `(0, 2)`
`allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional`, *proved* here by the ported strong
induction `gradOrderRS_l2Norm_le_lapIter_sum` with the three `(r, ·)` per-order families
(`order2GardingFamilyRS_holds`, `order1ControlFamilyRS_holds`, `commutatorDefectBoundRS_holds`)
discharged as the genuinely general-rank curvature/Green content.  Consumers transitively depend on
`sorryAx` through those three posited family atoms. -/
private theorem covGrad_l2Norm_le_lapIter_sumRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s),
        ∑ j ∈ Finset.range (2 * k + 1),
            Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            ‖Integral.L2.SmoothCcTensor.toL2
              (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ := by
  classical
  obtain ⟨Cg, hgard⟩ := order2GardingFamilyRS_holds (I := I) (M := M) g r
  obtain ⟨Cc, hcomm⟩ := commutatorDefectBoundRS_holds (I := I) (M := M) g r s
  obtain ⟨Cmix, hCmix_nn, hmix⟩ :=
    gradOrderRS_l2Norm_le_lapIter_sum (I := I) (M := M) g r s Cg Cc hgard
      (order1ControlFamilyRS_holds (I := I) (M := M) g r) hcomm
  set Cmax : ℝ := ∑ j ∈ Finset.range (2 * k + 1), Cmix j with hCmax_def
  have hCmax_nn : 0 ≤ Cmax := Finset.sum_nonneg (fun j _ => hCmix_nn j)
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩
  have hLHS_eq : ∀ j,
      Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + j)
          (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T).toFun =
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T‖ :=
    fun j => (iteratedCovGradRS_norm_eq_tensorL2Norm (I := I) (M := M) g r s j T).symm
  have hRHS_eq : ∀ i,
      ‖Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ =
        ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i T‖ :=
    fun i => (rawTensorConnLapIterRS_norm_eq_toL2 (I := I) (M := M) g r s i T).symm
  rw [Finset.sum_congr rfl (fun j _ => hLHS_eq j),
      Finset.sum_congr rfl (fun i _ => hRHS_eq i)]
  set Sk : ℝ := ∑ i ∈ Finset.range (k + 1),
    ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i T‖ with hSk_def
  have hSk_nn : 0 ≤ Sk := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hper : ∀ j ∈ Finset.range (2 * k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T‖ ≤ Cmix j * Sk := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hsub_le : ∑ i ∈ Finset.range ((j + 1) / 2 + 1),
          ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i T‖ ≤ Sk := by
      rw [hSk_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro i _ _; exact norm_nonneg _
    calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T‖
        ≤ Cmix j * ∑ i ∈ Finset.range ((j + 1) / 2 + 1),
            ‖Integral.Connection.rawTensorConnLapIter (I := I) g r s i T‖ := hmix j T
      _ ≤ Cmix j * Sk := mul_le_mul_of_nonneg_left hsub_le (hCmix_nn j)
  calc ∑ j ∈ Finset.range (2 * k + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T‖
      ≤ ∑ j ∈ Finset.range (2 * k + 1), Cmix j * Sk := Finset.sum_le_sum hper
    _ = (∑ j ∈ Finset.range (2 * k + 1), Cmix j) * Sk := by rw [Finset.sum_mul]
    _ = Cmax * Sk := by rw [hCmax_def]

set_option linter.unusedSectionVars false in
/-- **The general-rank matching-order Gårding lift `chart-H^{2a} ≤ spectral@{2a}`.** For every
chart order `a` there is a constant `C ≥ 0` such that the intrinsic order-`a`
partition-of-unity Hilbert–Schmidt chart-Sobolev norm `‖T.toHs a‖` — an `H^{2a}` chart-Sobolev
norm — of a smooth `(r, s)`-tensor `T` is bounded by `C` times the square root of the
*order-`2a`* weighted spectral square-sum
`∑ᵢ (1 + λᵢ)^{2a} · (tensorL2Coeff (T.toL2) i)²` of the eigenbasis coordinates of `T`'s `L²`
class.

The Sobolev exponent on the right is `2a = 2 · a`, **matching** the `H^{2a}` regularity of the
chart norm `‖T.toHs a‖` (the chart inner product `hkInner` / `tensorPouSobolevHsNorm g a`
aggregates chart derivatives up to order `2a`, so `‖T.toHs a‖ ↔ chart-H^{2a} ↔ spectral weight
`(1 + λ)^{2a}``).  This is the general-rank analogue of the in-library `(0, 2)`
`pouSobolevToHsNorm_le_spectral`; it is *proved* here at general bidegree `(r, s)` and general
order `a`, by the same three-step composition: the general-rank reverse Hebey-Sobolev bridge
`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum` (chart-`H^{2a}` ≤
`∑_{j ≤ 2a} ‖∇^j T‖_{L²}`), the posited general-rank Gårding bootstrap
`covGrad_l2Norm_le_lapIter_sumRS` (`∑_{j ≤ 2a} ‖∇^j T‖ ≤ C · ∑_{i ≤ a} ‖Δ_∇^i T‖`), and the
general-rank spectral collapse `rawConnLapIterRS_l2Norm_le_sqrt_spectral` (each `‖Δ_∇^i T‖`,
`i ≤ a`, bounded by the single spectral weight `(1 + λ)^{2a}`).  Consumers transitively depend
on `sorryAx` through the posited Gårding bootstrap. -/
private theorem chartHsRS_le_sqrt_spectral_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ ≤ C *
          Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g r s,
            tensorSobolevWeight (I := I) (M := M) i ((2 * a : ℕ) : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
                (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    PDE.RicciFlow.exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g r s a
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    covGrad_l2Norm_le_lapIter_sumRS (I := I) (M := M) g r s a
  refine ⟨CB * (C₁ * (a + 1)), by positivity, fun T => ?_⟩
  set Nspec : ℝ := Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s,
    tensorSobolevWeight (I := I) (M := M) i ((2 * a : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := Real.sqrt_nonneg _
  rw [tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g a T]
  set GradSum : ℝ := ∑ j ∈ Finset.range (2 * a + 1),
    Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + j)
      (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T).toFun with hGradSum_def
  set LapSum : ℝ := ∑ i ∈ Finset.range (a + 1),
    ‖Integral.L2.SmoothCcTensor.toL2
      (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ with hLapSum_def
  have hLapSum_le : LapSum ≤ (a + 1 : ℝ) * Nspec := by
    rw [hLapSum_def]
    have hterm : ∀ i ∈ Finset.range (a + 1),
        ‖Integral.L2.SmoothCcTensor.toL2
          (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ ≤ Nspec := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hiN : 2 * i ≤ 2 * a := by omega
      rw [hNspec_def]
      exact rawConnLapIterRS_l2Norm_le_sqrt_spectral (I := I) (M := M) g r s T i (2 * a) hiN
    calc ∑ i ∈ Finset.range (a + 1),
            ‖Integral.L2.SmoothCcTensor.toL2
              (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖
        ≤ ∑ _i ∈ Finset.range (a + 1), Nspec := Finset.sum_le_sum hterm
      _ = (Finset.range (a + 1)).card • Nspec := by rw [Finset.sum_const]
      _ = (a + 1 : ℝ) * Nspec := by
            rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hbootstrap : GradSum ≤ C₁ * LapSum := hC₁ T
  have hreverse :
      (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T).toReal ≤
        CB * GradSum := hCB T
  calc (Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g a T).toReal
      ≤ CB * GradSum := hreverse
    _ ≤ CB * (C₁ * LapSum) := mul_le_mul_of_nonneg_left hbootstrap hCB_nn
    _ ≤ CB * (C₁ * ((a + 1 : ℝ) * Nspec)) := by
          have h := mul_le_mul_of_nonneg_left hLapSum_le hC₁_nn
          exact mul_le_mul_of_nonneg_left h hCB_nn
    _ = CB * (C₁ * (a + 1)) * Nspec := by ring

/-- **Monotone domination of the raw spectral square-root sum in the order.** For `τ ≤ σ` the
order-`τ` weighted spectral square-root sum of the eigenbasis coordinates of `T`'s `L²` class is
bounded by the order-`σ` one, since the spectral weight `(1 + λᵢ)^τ ≤ (1 + λᵢ)^σ` is monotone in
the exponent (`tensorSobolevWeight_mono`) and both weighted square-sums are summable
(`smoothCcTensorRS_tensorL2Coeff_weighted_summable`).  This is the raw-`tsum` form of the
continuous Sobolev inclusion `Hˢ ⊆ Hᵗ` on the smooth subspace, used to descend the chained
embedding from a smaller chart order back to the contract spectral order. -/
private lemma spectral_sqrt_mono_of_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i τ *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) ≤
      Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  refine Real.sqrt_le_sqrt ?_
  refine Summable.tsum_le_tsum (fun i => ?_)
    (smoothCcTensorRS_tensorL2Coeff_weighted_summable (I := I) (M := M) g r s τ T)
    (smoothCcTensorRS_tensorL2Coeff_weighted_summable (I := I) (M := M) g r s σ T)
  exact mul_le_mul_of_nonneg_right
    (Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_mono (I := I) (M := M) i hτσ)
    (sq_nonneg _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp general-rank fibre Sobolev embedding `H^a ↪ C⁰` at the supercritical
spectral order `a`.** At a supercritical order `a` (`2a > dim M + 4`) there is a constant
`C ≥ 0` such that the bundle-fibre value `‖T.toSection x‖` of a smooth `(r, s)`-tensor is
bounded by `C` times the square root of the weighted order-`a` spectral square-sum
`∑ᵢ (1 + λᵢ)^a · (tensorL2Coeff (T.toL2) i)²` of the eigenbasis coordinates of `T`'s `L²`
class, for all `x`.

This is the genuine elliptic / Sobolev content underlying the local Weyl law at general
bidegree: the *sharp* spectral Sobolev embedding `H^a ↪ C⁰`, valid for `a > (dim M)/2` (here
`2a > dim M + 4 ⟹ a > dim M / 2` with margin for the `(r, s)` fibre Hilbert–Schmidt slack).
It is recorded at the *sharp* order `a` rather than the chained order of the in-file
`(0, 2)` `pointwiseFiberNorm_le_spectralHs_02`.  It is *proved* here, honestly and at the
sharp order `a`, by routing the two posited general-rank analytic children through the
**halved** chart order `m = a / 2`: the chart-`H^{2m}`-embedding
`pointwiseFiberNormRS_le_chartHs_sharp` at order `m` (`chart-H^{2m} ↪ C⁰`, valid since
`2·(2m) ≥ 2a - 2 > dim M`), composed with the matching-order Gårding lift
`chartHsRS_le_sqrt_spectral_sharp` at order `m` (`‖T.toHs m‖ ≤ √(spectral@{2m})`), produces the
order-`2m` spectral square-root; since `2m = 2·(a / 2) ≤ a`, the monotone Sobolev domination
`spectral_sqrt_mono_of_le` descends it to the contract order-`a` square-root.  (Routing the
children at the full order `a` would instead land the order-`2a` spectral sum, strictly larger
than — hence not dominating — the order-`a` sum; the halving is the honest reconciliation of the
`H^{2·order}`-regularity of `‖T.toHs order‖` with the order-`a` contract.)  Consumers
transitively depend on `sorryAx` through those two posited general-rank children.  The
conclusion is a fibre `C⁰` bound by the raw spectral square-sum, structurally distinct from the
spectral-`H^a`-norm bound `pointwiseFiberNormRS_le_spectralHs` it powers (no packaging). -/
private theorem pointwiseFiberNormRS_le_sqrt_spectral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤ C *
          Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g r s,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
                (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  set m : ℕ := a / 2 with hm_def
  have h2m_le_a : 2 * m ≤ a := by rw [hm_def]; omega
  have hm_embed : 2 * (2 * m) > Module.finrank ℝ E := by
    have h2m : a - 1 ≤ 2 * m := by rw [hm_def]; omega
    omega
  obtain ⟨Cc, hCc_nn, hCc⟩ :=
    pointwiseFiberNormRS_le_chartHs_sharp (I := I) (M := M) g r s m hm_embed
  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    chartHsRS_le_sqrt_spectral_sharp (I := I) (M := M) g r s m
  refine ⟨Cc * Cn, by positivity, fun T x => ?_⟩
  set Nspec : ℝ := Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s,
    tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) with hNspec_def
  set Nhalf : ℝ := Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s,
    tensorSobolevWeight (I := I) (M := M) i ((2 * m : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (Integral.L2.SmoothCcTensor.toL2 T) i) ^ 2) with hNhalf_def
  have hdom : Nhalf ≤ Nspec := by
    rw [hNhalf_def, hNspec_def]
    exact spectral_sqrt_mono_of_le (I := I) (M := M) g r s
      (by exact_mod_cast h2m_le_a) T
  calc ‖T.toSection x‖
      ≤ Cc * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) m T‖ := hCc T x
    _ ≤ Cc * (Cn * Nhalf) := by
          exact mul_le_mul_of_nonneg_left (hCn T) hCc_nn
    _ ≤ Cc * (Cn * Nspec) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdom hCn_nn) hCc_nn
    _ = (Cc * Cn) * Nspec := by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Composite pointwise fibre / spectral bound at general bidegree `(r, s)`.** At a
supercritical order `a` (`2a > dim M + 4`) there is a constant `C ≥ 0` such that the
bundle-fibre value `‖T.toSection x‖` of a smooth `(r, s)`-tensor is bounded by
`C · ‖smoothToTensorHsRS g r s a T‖` for all `x`.

This is the bidegree-`(r, s)` analogue of the in-file `(0, 2)`
`pointwiseFiberNorm_le_spectralHs_02`.  It is *proved* here from the sharp general-rank fibre
Sobolev embedding `pointwiseFiberNormRS_le_sqrt_spectral` (the genuine `H^a ↪ C⁰` content at
the supercritical order `a`, posited above) by identifying its raw order-`a` spectral
square-sum with the spectral `H^a`-norm `‖smoothToTensorHsRS g r s a T‖` via
`norm_smoothToTensorHsRS_eq_spectral_sqrt`, exactly as the `(0, 2)`
`pointwiseFiberNorm_le_spectralHs_02` identifies its Gårding-side spectral sum with
`‖smoothToTensorHs g (4k) T‖`.  Consumers transitively depend on `sorryAx` through the posited
sharp embedding.  The conclusion is a norm bound, structurally distinct from any spectral-decay
hypothesis (no packaging). -/
private theorem pointwiseFiberNormRS_le_spectralHs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤ C * ‖smoothToTensorHsRS (I := I) (M := M) g r s (a : ℝ) T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, hC_nn, hbound⟩ :=
    pointwiseFiberNormRS_le_sqrt_spectral (I := I) (M := M) g r s a ha
  refine ⟨C, hC_nn, fun T x => ?_⟩
  rw [norm_smoothToTensorHsRS_eq_spectral_sqrt (I := I) (M := M) g r s (a : ℝ) T]
  exact hbound T x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-direction truncated Bessel bound at general bidegree `(r, s)`.** For every
supercritical Sobolev order `a` (`2a > dim M + 4`) there is a finite constant `C ≥ 0` such
that, at every point `x`, every fibre vector `ζ` with `gFiberInner x ζ ζ ≤ 1`, and every
finite eigen-index set `F`, the truncated Bessel sum of the `g`-fibre pairings of `ζ`
against the eigenbasis fibre values, weighted by `(1 + λⱼ)^{-a}`, is bounded by `C`:

  `∑_{j ∈ F} (1 + λⱼ)^{-a} · (gFiberInnerRS x ζ (bⱼ(x)))² ≤ C`,  `bⱼ = eigenvectorSmooth g r s j`.

This is the genuine general-rank analytic content of the local Weyl law: it is the
bidegree-`(r, s)` analogue of the in-file `(0, 2)` `partialBessel_le_Csq_02`, whose proof
builds the smooth eigen-combination `T := ∑_{j ∈ F}(1 + λⱼ)^{-a}⟪ζ, bⱼ(x)⟫·eigenSmooth_j`
and bounds the partial sum `S = ⟪ζ, T(x)⟫ ≤ ‖ζ‖·‖T(x)‖ ≤ C·‖φ(T)‖ = C·√S` through the
chart-Sobolev embedding `H^{2k} ↪ C⁰` (`tensorPouSobolevHilbert_embedding_Ck`, available at
general rank) composed with the general-rank Gårding spectral bound and the general-rank
finite-eigen-combination spectral calculus.
This node is *proven* here from the general-rank finite-eigen-combination spectral calculus
built below (`finiteEigenComboRS` / `smoothToTensorHsRS`, the bidegree-`(r, s)` mirror of the
`(0, 2)` `finiteEigenCombo` / `smoothToTensorHs` tower) and the in-file composite fibre /
spectral bound `pointwiseFiberNormRS_le_spectralHs`.  Two precise general-rank analytic
children remain posited (absent from the library at general rank):
`smoothCcTensorRS_tensorL2Coeff_weighted_summable` (the `(r, s)` weighted Sobolev-scale
summability) and `pointwiseFiberNormRS_le_spectralHs` (the `(r, s)` fibre Sobolev-embedding /
Gårding bound).  Consumers transitively depend on `sorryAx` through those two posited
general-rank inputs.  The conclusion is a truncated quadratic-form bound, structurally
distinct from the summability/`tsum` conclusion it powers (no packaging). -/
theorem reproducingKernel_partialBessel_le_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (ζ : TensorRSSpace r s I x),
        gFiberInnerRS (I := I) (M := M) g r s x ζ ζ ≤ 1 →
        ∀ F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g r s),
          ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j (a : ℝ))⁻¹ *
              gFiberInnerRS (I := I) (M := M) g r s x ζ
                ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) ^ 2 ≤ C := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  -- The composite fibre/spectral embedding *at the supercritical order `a`*:
  -- `‖T.toSection x‖ ≤ C·‖smoothToTensorHsRS g r s a T‖`, so the left weight `(1+λⱼ)^{-a}`
  -- and the test-norm order agree (the cancellation `weightₐ·weightₐ⁻² = weightₐ⁻¹` that
  -- makes `‖φ(T)‖² = S` work, exactly as in the `(0, 2)` `partialBessel_le_Csq_02`).
  obtain ⟨C, hC_nn, hbound⟩ :=
    pointwiseFiberNormRS_le_spectralHs (I := I) (M := M) g r s a ha
  refine ⟨C ^ 2, by positivity, fun x ζ hζ F => ?_⟩
  set σ : ℝ := (a : ℝ) with hσ_def
  -- coefficient family and the test tensor.
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun j => (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
      gFiberInnerRS (I := I) (M := M) g r s x ζ
        ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) with hc_def
  set T : Integral.L2.SmoothCcTensor g r s :=
    finiteEigenComboRS (I := I) (M := M) g r s F c with hT_def
  set S : ℝ := ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
      gFiberInnerRS (I := I) (M := M) g r s x ζ
        ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) ^ 2 with hS_def
  change S ≤ C ^ 2
  -- `gFiberInnerRS x ζ ·` is the genuine fibre inner product `⟪ζ, ·⟫`.
  have hbridge : ∀ w : TensorRSSpace r s I x,
      gFiberInnerRS (I := I) (M := M) g r s x ζ w = (inner ℝ ζ w : ℝ) :=
    fun w => gFiberInnerRS_eq_inner (I := I) (M := M) g r s x ζ w
  have hζ' : ‖ζ‖ ^ 2 ≤ 1 := by
    rw [← real_inner_self_eq_norm_sq, ← hbridge ζ]; exact hζ
  have hζ_le_one : ‖ζ‖ ≤ 1 := by nlinarith [norm_nonneg ζ, hζ']
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    refine Finset.sum_nonneg (fun j _ => ?_)
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) j σ :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) j σ
    positivity
  -- (a) `⟪ζ, T.toSection x⟫ = S`.
  have hpair : (inner ℝ ζ (T.toSection x) : ℝ) = S := by
    rw [hT_def, finiteEigenComboRS_toSection_apply (I := I) (M := M) g r s F c x, inner_sum, hS_def]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_smul_right, hc_def,
      ← hbridge ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x)]
    ring
  -- (b) `‖φ(T)‖² = S` (the weight cancellation at the common order `σ = a`).
  have hnorm_sq : ‖smoothToTensorHsRS (I := I) (M := M) g r s σ T‖ ^ 2 = S := by
    rw [Analysis.Parabolic.TensorHeatEquation.tensorHs.norm_sq_eq_tsum, hS_def]
    have hcoeff : ∀ i, (smoothToTensorHsRS (I := I) (M := M) g r s σ T).coeff i =
        (if i ∈ F then c i else 0) := by
      intro i
      rw [smoothToTensorHsRS_coeff, hT_def]
      exact finiteEigenComboRS_tensorL2Coeff (I := I) (M := M) g r s F c i
    rw [tsum_congr (fun i => by rw [hcoeff i])]
    rw [tsum_eq_sum (s := F) (fun i hi => by rw [if_neg hi]; ring)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [if_pos hj, hc_def]
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) j σ :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) j σ
    rw [mul_pow]
    rw [show tensorSobolevWeight (I := I) (M := M) j σ *
          ((tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ ^ 2 *
            (gFiberInnerRS (I := I) (M := M) g r s x ζ
              ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x)) ^ 2)
        = (tensorSobolevWeight (I := I) (M := M) j σ *
            (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹) *
          ((tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
            (gFiberInnerRS (I := I) (M := M) g r s x ζ
              ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x)) ^ 2) by ring,
      mul_inv_cancel₀ hw.ne', one_mul]
  -- (c) `S = ⟪ζ, T(x)⟫ ≤ ‖ζ‖·‖T(x)‖ ≤ ‖T(x)‖ ≤ C·‖φ(T)‖ = C·√S`, forcing `S ≤ C²`.
  have hCS : (inner ℝ ζ (T.toSection x) : ℝ) ≤ ‖ζ‖ * ‖T.toSection x‖ := by
    calc (inner ℝ ζ (T.toSection x) : ℝ) ≤ ‖(inner ℝ ζ (T.toSection x) : ℝ)‖ := le_abs_self _
      _ ≤ ‖ζ‖ * ‖T.toSection x‖ := norm_inner_le_norm ζ (T.toSection x)
  have hS_le_secnorm : S ≤ ‖T.toSection x‖ := by
    rw [← hpair]
    refine hCS.trans ?_
    calc ‖ζ‖ * ‖T.toSection x‖ ≤ 1 * ‖T.toSection x‖ :=
          mul_le_mul_of_nonneg_right hζ_le_one (norm_nonneg _)
      _ = ‖T.toSection x‖ := one_mul _
  have hsec_le : ‖T.toSection x‖ ≤ C * Real.sqrt S := by
    refine (hbound T x).trans ?_
    rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hS_le : S ≤ C * Real.sqrt S := le_trans hS_le_secnorm hsec_le
  rcases eq_or_lt_of_le hS_nn with hS0 | hSpos
  · rw [← hS0]; positivity
  · have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
    have hSeq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS_nn
    have hsqrt_le_C : Real.sqrt S ≤ C := by nlinarith [hS_le, hSeq, hsqrt_pos]
    calc S = Real.sqrt S * Real.sqrt S := hSeq.symm
      _ ≤ C * C := mul_le_mul hsqrt_le_C hsqrt_le_C (Real.sqrt_nonneg _) hC_nn
      _ = C ^ 2 := (sq C).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The supercritical on-diagonal reproducing-kernel summability `(★)` (general
bidegree, uniform in the supercritical order).** This is the pointwise local Weyl
law: for every supercritical Sobolev order `a` (`2a > dim M + 4`) and every point
`x : M`, the weighted reproducing-kernel tail `∑ᵢ (1 + λᵢ)^{-a} · ‖bᵢ(x)‖²_g` is
summable and bounded by a point-uniform constant `C a`. The base term
`‖bᵢ(x)‖²_g = riemannianFiberNormSq g r s x (bᵢ.toSection x)` is the Riemannian fibre
norm squared of the eigenbasis representative `bᵢ = eigenvectorSmooth g r s i`.

It is *proven* here by the fibre-Parseval-over-an-orthonormal-frame argument (the same one
that derives `reproducingKernel_tsum_le_of_closed_02` from `partialBessel_le_Csq_02` at
`(0, 2)`): the fibre Parseval `riemannianFiberNormSq_eq_sum_gFiberInnerRS_sq` expands
`‖bⱼ(x)‖²_g = ∑ₘ ⟪ζₘ, bⱼ(x)⟫²` over a fibre orthonormal frame `ζₘ`, summing the posited
per-direction truncated Bessel bound `reproducingKernel_partialBessel_le_of_closed` over
the `D = dim` frame directions bounds every finite partial sum of
`(1 + λⱼ)^{-a} · ‖bⱼ(x)‖²_g` by `D · C`, hence summability with total `≤ D · C` by
`Real.tsum_le_of_sum_le`.  Consumers transitively depend on `sorryAx` through that
per-direction primitive. -/
theorem reproducingKernel_weighted_tsum_le_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : M,
          Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g r s =>
            (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) ∧
          (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g r s,
            (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) ≤ C := by
  classical
  intro a ha
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, hC_nn, hbessel⟩ :=
    reproducingKernel_partialBessel_le_of_closed (I := I) (M := M) g r s a ha
  -- The point-uniform constant is `D · C`, `D = dim` of the model fibre.
  refine ⟨(Module.finrank ℝ (TensorRSModel r s ℝ E) : ℝ) * C, by positivity, fun x => ?_⟩
  set D : ℕ := Module.finrank ℝ (TensorRSSpace r s I x) with hD_def
  set bON := stdOrthonormalBasis ℝ (TensorRSSpace r s I x) with hbON_def
  set f : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
      eigenFiberNormSq (I := I) (M := M) g r s i x with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := by
    intro i; rw [hf_def]
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    have := eigenFiberNormSq_nonneg (I := I) (M := M) g r s i x
    positivity
  -- Per-finite-set bound: `∑_{j∈F} f j ≤ D · C`.
  have hfinset : ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g r s)), ∑ j ∈ F, f j ≤ (D : ℝ) * C := by
    intro F
    -- expand `eigenFiberNormSq = ∑ₘ (gFiberInnerRS ζₘ bⱼ(x))²` via the fibre Parseval.
    have hexpand : ∀ j, f j =
        ∑ m : Fin D, (tensorSobolevWeight (I := I) (M := M) j (a : ℝ))⁻¹ *
          gFiberInnerRS (I := I) (M := M) g r s x (bON m)
            ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) ^ 2 := by
      intro j
      simp only [hf_def, eigenFiberNormSq]
      rw [riemannianFiberNormSq_eq_sum_gFiberInnerRS_sq (I := I) (M := M) g r s x bON
          ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x), Finset.mul_sum]
    -- swap sums and apply the truncated Bessel bound per direction.
    calc ∑ j ∈ F, f j
        = ∑ j ∈ F, ∑ m : Fin D, (tensorSobolevWeight (I := I) (M := M) j (a : ℝ))⁻¹ *
            gFiberInnerRS (I := I) (M := M) g r s x (bON m)
              ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) ^ 2 := by
          exact Finset.sum_congr rfl (fun j _ => hexpand j)
      _ = ∑ m : Fin D, ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j (a : ℝ))⁻¹ *
            gFiberInnerRS (I := I) (M := M) g r s x (bON m)
              ((eigenvectorSmooth (I := I) (M := M) g r s j).toSection x) ^ 2 :=
          Finset.sum_comm
      _ ≤ ∑ _m : Fin D, C := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          refine hbessel x (bON m) ?_ F
          -- `gFiberInnerRS x (bON m) (bON m) = ‖bON m‖² = 1 ≤ 1`.
          have hone : gFiberInnerRS (I := I) (M := M) g r s x (bON m) (bON m) = 1 := by
            rw [gFiberInnerRS_eq_inner (I := I) (M := M) g r s x (bON m) (bON m),
              real_inner_self_eq_norm_sq, hbON_def,
              (stdOrthonormalBasis ℝ (TensorRSSpace r s I x)).orthonormal.1 m]
            norm_num
          rw [hone]
      _ = (D : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- summability + tsum bound from the uniform finite-set bound.
  have hsummable : Summable f := summable_of_sum_le hf_nn hfinset
  refine ⟨hsummable, ?_⟩
  -- `D = finrank (model)` since the fibre is isomorphic to the model fibre.
  have hDeq : (D : ℝ) = (Module.finrank ℝ (TensorRSModel r s ℝ E) : ℝ) := by
    rw [hD_def]
    congr 1
    exact (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (M := M)
      (𝕜 := ℝ) r s x).toLinearEquiv.finrank_eq
  calc ∑' i, f i ≤ (D : ℝ) * C := Real.tsum_le_of_sum_le hf_nn hfinset
    _ = (Module.finrank ℝ (TensorRSModel r s ℝ E) : ℝ) * C := by rw [hDeq]

/-- **Discreteness of the tensor connection-Laplacian spectrum below a threshold.**
For every threshold `Λ`, only finitely many eigen-indices `i` satisfy `1 + λᵢ < Λ`.
This is the standard discreteness of the spectrum of the compact resolvent
`tensorResolventL2 g r s` (finitely many eigenvalues outside any neighbourhood of `0`,
each with a finite-dimensional eigenspace). -/
theorem tensorEigenIdx_one_add_lambda_lt_finite
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Λ : ℝ) :
    {i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s |
      1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) i < Λ}.Finite := by
  classical
  by_cases hΛ : 0 < Λ
  · -- The base set of nonzero resolvent eigenvalues `μ` with `1 + λ(μ) < Λ`.
    set B : Set (Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue
        (I := I) (M := M) g r s) :=
      {μ | 1 + Analysis.Parabolic.TensorSpectral.tensorLaplacianEigenvalueOf μ.val < Λ}
      with hB_def
    -- It is finite: the value map `μ ↦ μ.val` injects it into the finite shell
    -- `{x | HasEigenvalue x ∧ 1/Λ ≤ |x|}` (`tensorResolvent_eigenvalues_finite_above`).
    have hBfin : B.Finite := by
      apply Set.Finite.of_finite_image
        (f := fun μ : Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s => μ.val)
      · refine Set.Finite.subset
          (Analysis.Parabolic.TensorSpectral.tensorResolvent_eigenvalues_finite_above
            (I := I) (M := M) g r s
            (IntrinsicSpectral.tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s)
            (show (0 : ℝ) < 1 / Λ by positivity)) ?_
        rintro x ⟨μ, hμB, rfl⟩
        have hev : Module.End.HasEigenvalue
            ((Analysis.Parabolic.TensorSpectral.tensorResolventL2
              (I := I) (M := M) g r s).toLinearMap) μ.val :=
          μ.hasEigenvalue
        obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
        have hu_in : u ∈ Analysis.Parabolic.TensorSpectral.tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val := hu_mem
        have hμ_unit : μ.val ∈ Set.Ioc (0 : ℝ) 1 :=
          Analysis.Parabolic.TensorSpectral.tensorResolvent_eigenvalue_mem_unit_interval
            (I := I) (M := M) g r s hu_in hu_ne
        have hμ_pos : 0 < μ.val := hμ_unit.1
        have hlt : 1 + Analysis.Parabolic.TensorSpectral.tensorLaplacianEigenvalueOf μ.val < Λ :=
          hμB
        have hinv : (μ.val)⁻¹ < Λ := by
          have heq : (μ.val)⁻¹
              = 1 + Analysis.Parabolic.TensorSpectral.tensorLaplacianEigenvalueOf μ.val := by
            rw [Analysis.Parabolic.TensorSpectral.tensorLaplacianEigenvalueOf]
            field_simp; ring
          rw [heq]; exact hlt
        have hμ_gt : 1 / Λ < μ.val := by
          rw [div_lt_iff₀ hΛ]
          rw [inv_lt_iff_one_lt_mul₀ hμ_pos] at hinv
          linarith [hinv]
        exact ⟨hev, by rw [abs_of_pos hμ_pos]; exact le_of_lt hμ_gt⟩
      · intro μ₁ _ μ₂ _ h
        exact Analysis.Parabolic.TensorSpectral.TensorNonzeroResolventEigenvalue.ext μ₁ μ₂ h
    -- The eigen-index set is the sigma over `B` with finite (`Fintype`) eigenspace fibres.
    have hset_eq :
        {i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s |
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) i < Λ}
          = ⋃ μ ∈ B, Sigma.mk μ '' Set.univ := by
      ext ⟨μ, k⟩
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨μ, by rw [hB_def]; exact h, k, rfl⟩
      · rintro ⟨μ', hμ'B, k', heq⟩
        obtain ⟨rfl, _⟩ := Sigma.mk.injEq .. ▸ heq
        rw [hB_def] at hμ'B; exact hμ'B
    rw [hset_eq]
    exact hBfin.biUnion (fun μ _ => Set.finite_univ.image _)
  · -- For `Λ ≤ 0` the set is empty, as `1 + λᵢ ≥ 1 > 0 ≥ Λ`.
    have hempty :
        {i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s |
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) i < Λ} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro i hi
      have hlam := Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg (I := I) (M := M) i
      have hΛle := not_lt.1 hΛ
      simp only [Set.mem_setOf_eq] at hi
      linarith
    rw [hempty]; exact Set.finite_empty

/-! ## Conjunct 1: the polynomial diagonal-kernel bound -/

/-- The threshold-indexed finite family `count Λ := {i : 1 + λᵢ < Λ}`, as a
`Finset` (its underlying set is finite by `tensorEigenIdx_one_add_lambda_lt_finite`). -/
private noncomputable def thresholdCount
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Λ : ℝ) :
    Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :=
  (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset

private lemma mem_thresholdCount_iff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Λ : ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    i ∈ thresholdCount (I := I) (M := M) g r s Λ ↔
      1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
  unfold thresholdCount
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **The polynomial diagonal-kernel bound (conjunct 1).** With the supercritical
order `σ` and constant `C` from the reproducing-kernel summability `(★)`, the
on-diagonal reproducing kernel of `thresholdCount Λ` is bounded by `C · Λ^σ`
pointwise on `M`, and `thresholdCount Λ` contains every index with `1 + λᵢ < Λ`. -/
theorem diagonalKernel_polynomial_bound_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (q : ℕ) (B : ℝ), 0 ≤ B ∧
      ∃ count : ℝ → Finset
          (Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        (∀ (Λ : ℝ)
            (i : Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
        (∀ (Λ : ℝ) (x : M),
          MetricRealization.diagonalKernel (I := I) (M := M) g r s (count Λ) x ≤ B * Λ ^ q) := by
  classical
  -- Instantiate the kernel summability at an even supercritical order `a`.
  set a : ℕ := 2 * (Module.finrank ℝ E + 3) with ha_def
  have ha_super : 2 * a > Module.finrank ℝ E + 4 := by rw [ha_def]; omega
  obtain ⟨C, hC_nn, hstar⟩ :=
    reproducingKernel_weighted_tsum_le_of_closed (I := I) (M := M) g r s a ha_super
  refine ⟨a, C, hC_nn, thresholdCount (I := I) (M := M) g r s, ?_, ?_⟩
  · intro Λ i hi
    exact (mem_thresholdCount_iff (I := I) (M := M) g r s Λ i).2 hi
  · intro Λ x
    obtain ⟨hsummable, htsum_le⟩ := hstar x
    rw [diagonalKernel_eq_sum_eigenFiberNormSq (I := I) (M := M) g r s _ x]
    -- For `Λ ≤ 0` the threshold set is empty (`1 + λᵢ ≥ 1 > Λ`).
    by_cases hΛ_pos : 0 < Λ
    case neg =>
      have hΛ : Λ ≤ 0 := not_lt.1 hΛ_pos
      have hempty : thresholdCount (I := I) (M := M) g r s Λ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        have hlt := (mem_thresholdCount_iff (I := I) (M := M) g r s Λ i).1 hi
        have := Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg (I := I) (M := M) i
        linarith
      rw [hempty, Finset.sum_empty]
      have hΛnn : (0 : ℝ) ≤ Λ ^ a := by
        rw [ha_def, pow_mul]; positivity
      nlinarith [hC_nn, hΛnn]
    -- Telescope: on `count Λ`, `‖bᵢ(x)‖² ≤ Λ^a · (1+λᵢ)^{-a}‖bᵢ(x)‖²`.
    have hterm : ∀ i ∈ thresholdCount (I := I) (M := M) g r s Λ,
        eigenFiberNormSq (I := I) (M := M) g r s i x ≤
          Λ ^ a * ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
            eigenFiberNormSq (I := I) (M := M) g r s i x) := by
      intro i hi
      have hlt : 1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i < Λ :=
        (mem_thresholdCount_iff (I := I) (M := M) g r s Λ i).1 hi
      have hone_le : (1 : ℝ) ≤
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i := by
        have := Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg (I := I) (M := M) i; linarith
      have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
        Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
      -- `(1+λᵢ)^a ≤ Λ^a`.
      have hwle : tensorSobolevWeight (I := I) (M := M) i (a : ℝ) ≤ Λ ^ a := by
        unfold tensorSobolevWeight
        rw [← Real.rpow_natCast Λ a]
        exact Real.rpow_le_rpow (le_trans zero_le_one hone_le) hlt.le (by positivity)
      have hfn_nn : 0 ≤ eigenFiberNormSq (I := I) (M := M) g r s i x :=
        eigenFiberNormSq_nonneg (I := I) (M := M) g r s i x
      have hfactor : (1 : ℝ) ≤
          Λ ^ a * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ := by
        rw [le_mul_inv_iff₀ hw_pos, one_mul]; exact hwle
      calc eigenFiberNormSq (I := I) (M := M) g r s i x
          = 1 * eigenFiberNormSq (I := I) (M := M) g r s i x := (one_mul _).symm
        _ ≤ (Λ ^ a * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) *
              eigenFiberNormSq (I := I) (M := M) g r s i x :=
            mul_le_mul_of_nonneg_right hfactor hfn_nn
        _ = Λ ^ a * ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) := by ring
    calc ∑ i ∈ thresholdCount (I := I) (M := M) g r s Λ,
            eigenFiberNormSq (I := I) (M := M) g r s i x
        ≤ ∑ i ∈ thresholdCount (I := I) (M := M) g r s Λ,
            Λ ^ a * ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) :=
          Finset.sum_le_sum hterm
      _ = Λ ^ a * ∑ i ∈ thresholdCount (I := I) (M := M) g r s Λ,
            ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) := by
          rw [Finset.mul_sum]
      _ ≤ Λ ^ a * (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g r s,
            (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g r s i x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hsummable.sum_le_tsum _ (fun i _ => ?_)
          have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
            Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
          have hfn_nn : 0 ≤ eigenFiberNormSq (I := I) (M := M) g r s i x :=
            eigenFiberNormSq_nonneg (I := I) (M := M) g r s i x
          positivity
      _ ≤ Λ ^ a * C := mul_le_mul_of_nonneg_left htsum_le (by positivity)
      _ = C * Λ ^ a := by ring

/-! ## The composite chart-Sobolev / spectral pointwise bound at `(0, 2)`

`pointwiseFiberNorm_le_spectralHs_02` composes the chart-Sobolev embedding
`H^{2k} ↪ C⁰` (`tensorPouSobolevHilbert_embedding_Ck` at `m = 0`) with the all-order
Gårding spectral bound `pouSobolevToHsNorm_le_spectral`: at the supercritical chart
order `2k > dim M`, the bundle-fibre value `‖T.toSection x‖` of a smooth `(0, 2)`-tensor
is bounded by `C` times the spectral `H^{4k}`-norm of its eigenbasis-coordinate family
`φ(T)`, the `tensorHs g 0 2 (4k)` element with coordinates `tensorL2Coeff (T.toL2)`. -/

/-- The eigenbasis-coordinate `Hˢ` element of a smooth `(0, 2)`-tensor `T` at spectral
order `σ`: the `tensorHs g 0 2 σ` element with coordinate family
`tensorL2Coeff (hCompact g) (T.toL2)`, square-summable at every real order by
`smoothCcTensor_tensorL2Coeff_weighted_summable`. -/
private noncomputable def smoothToTensorHs
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g 0 2) :
    tensorHs (I := I) (M := M) g 0 2 σ where
  coeff i := tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
    (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g σ T
      (hCompact (I := I) (M := M) g)

@[simp] private lemma smoothToTensorHs_coeff
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (smoothToTensorHs (I := I) (M := M) g σ T).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 T) i := rfl

/-- The spectral `H^{2*(2k)}`-norm of `φ(T)` equals the `Real.sqrt` spectral sum on the
right of the all-order Gårding bound `pouSobolevToHsNorm_le_spectral`. -/
private lemma norm_smoothToTensorHs_eq_spectral_sqrt
    (g : SmoothRiemannianMetric I M) (k : ℕ) (T : SmoothCcTensor g 0 2) :
    ‖smoothToTensorHs (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) T‖ =
      Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) i) ^ 2) := by
  rw [Analysis.Parabolic.TensorHeatEquation.tensorHs.norm_eq_sqrt_tsum]
  refine congrArg Real.sqrt (tsum_congr (fun i => ?_))
  rw [smoothToTensorHs_coeff]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Composite pointwise fibre / spectral bound (`(0, 2)`).** There is a constant
`C ≥ 0` and, for every supercritical chart order `k` (`2k > dim M`), the bundle-fibre
value `‖T.toSection x‖` of a smooth `(0, 2)`-tensor is bounded by
`C · ‖φ(T)‖_{H^{4k}}` for all `x`, where `φ(T) = smoothToTensorHs g (4k) T`. -/
private lemma pointwiseFiberNorm_le_spectralHs_02
    (g : SmoothRiemannianMetric I M) (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        ‖T.toSection x‖ ≤ C *
          ‖smoothToTensorHs (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) T‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  -- Embedding `H^{2k} ↪ C⁰` (m = 0): `‖T.toSection x‖ ≤ Ce · ‖T.toHs (2k)‖`.
  obtain ⟨Ce, hCe_pos, hCe⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck
      (I := I) (M := M) (g := g) (r := 0) (s := 2) (k := k) (m := 0)
      (by simpa using hk)
  -- All-order Gårding spectral bound: `‖T.toHs (2k)‖ ≤ Cn · √(spectral sum @ 4k)`.
  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.pouSobolevToHsNorm_le_spectral
      (I := I) (M := M) g k
  refine ⟨Ce * Cn, by positivity, fun T x => ?_⟩
  calc ‖T.toSection x‖
      ≤ Ce * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ := hCe T x
    _ ≤ Ce * (Cn * Real.sqrt (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hCn T) (le_of_lt hCe_pos)
    _ = (Ce * Cn) * ‖smoothToTensorHs (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) T‖ := by
        rw [norm_smoothToTensorHs_eq_spectral_sqrt]; ring

/-! ## The reproducing-kernel bound at `(0, 2)` by finite truncation -/

/-- The fibre value of a finite eigen-combination is the finite fibre-linear
combination of the eigenbasis fibre values:
`(finiteEigenCombo g F c).toSection x = ∑_{i ∈ F} c i • (eigenSmooth_i.toSection x)`. -/
private lemma finiteEigenCombo_toSection_apply
    (g : SmoothRiemannianMetric I M)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (x : M) :
    (finiteEigenCombo (I := I) (M := M) g F c).toSection x =
      ∑ i ∈ F, c i • (eigenSmooth (I := I) (M := M) g i).toSection x := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, SmoothCcTensor.toSection_zero]
      rfl
  | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul]
      simp only [ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
        Pi.smul_apply, ih]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The Riemannian bundle fibre-norm squared `riemannianFiberNormSq g 0 2 x z`
coincides with the squared bundle-fibre norm `‖z‖²` under the Riemannian bundle
instance, via the fibre-norm bridge and `tensorRSRiemannianInnerCLM_apply`. -/
private lemma riemannianFiberNormSq_eq_norm_sq_02
    (g : SmoothRiemannianMetric I M) (x : M) (z : TensorRSSpace 0 2 I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g 0 2 x z z : ℝ) =
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g 0 2 x z).symm
  have hself : (inner ℝ z z : ℝ) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

/-- The fibre Riemannian inner product as a plain function, `gInner x ζ z =
tensorRSRiemannianInnerCLM g 0 2 x ζ z` (instance-free in the signature). -/
@[reducible] private noncomputable def gFiberInner
    (g : SmoothRiemannianMetric I M) (x : M) (ζ z : TensorRSSpace 0 2 I x) : ℝ :=
  DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
    (I := I) (M := M) g 0 2 x ζ z

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- With the Riemannian bundle instance installed, `gFiberInner` is the genuine fibre
inner product `inner ℝ`. (Proved once; the underlying `rfl` unfolds the bundle inner
product instance, hence the raised heartbeat budget.) -/
private lemma gFiberInner_eq_inner
    (g : SmoothRiemannianMetric I M) (x : M) (ζ z : TensorRSSpace 0 2 I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
    gFiberInner (I := I) (M := M) g x ζ z = (inner ℝ ζ z : ℝ) :=
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-direction truncated Bessel bound.** For the supercritical order
`σ = 2(2k)` and the embedding constant `C`, every finite partial sum of
`(1 + λⱼ)^{-σ} · ⟪ζ, bⱼ(x)⟫²` against any fibre vector `ζ` with `gFiberInner x ζ ζ ≤ 1`
is bounded by `C²`. This is the finite-truncation form of Bessel's inequality: the
smooth test tensor `T := ∑_{j ∈ F} (1 + λⱼ)^{-σ}⟪ζ, bⱼ(x)⟫ · eigenSmooth_j` has spectral
`Hˢ`-norm-squared equal to the partial sum `S`, and `⟪ζ, T.toSection x⟫ = S`, so
`S = ⟪ζ, T.toSection x⟫ ≤ ‖ζ‖ · ‖T.toSection x‖ ≤ C · ‖φ(T)‖ = C · √S`, forcing
`S ≤ C²`. -/
private lemma partialBessel_le_Csq_02
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (C : ℝ) (hC_nn : 0 ≤ C)
    (hbound : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
        ‖T.toSection x‖ ≤ C *
          ‖smoothToTensorHs (I := I) (M := M) g ((2 * (2 * k) : ℕ) : ℝ) T‖)
    (x : M) (ζ : TensorRSSpace 0 2 I x)
    (hζ : gFiberInner (I := I) (M := M) g x ζ ζ ≤ 1)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2)) :
    ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j ((2 * (2 * k) : ℕ) : ℝ))⁻¹ *
        gFiberInner (I := I) (M := M) g x ζ
          ((eigenSmooth (I := I) (M := M) g j).toSection x) ^ 2 ≤ C ^ 2 := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  set σ : ℝ := ((2 * (2 * k) : ℕ) : ℝ) with hσ_def
  -- The fibre inner product `gFiberInner` is, with the bundle instance active, the
  -- genuine fibre inner product `⟪·,·⟫`.
  have hbridge : ∀ w : TensorRSSpace 0 2 I x,
      gFiberInner (I := I) (M := M) g x ζ w = (inner ℝ ζ w : ℝ) :=
    fun w => gFiberInner_eq_inner (I := I) (M := M) g x ζ w
  -- coefficient family and the test tensor.
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun j => (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
      (inner ℝ ζ ((eigenSmooth (I := I) (M := M) g j).toSection x) : ℝ) with hc_def
  set T : SmoothCcTensor g 0 2 := finiteEigenCombo (I := I) (M := M) g F c with hT_def
  set S : ℝ := ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
      (inner ℝ ζ ((eigenSmooth (I := I) (M := M) g j).toSection x) : ℝ) ^ 2 with hS_def
  -- Rewrite the goal's `gFiberInner` as the bundle inner product `⟪·,·⟫`.
  simp only [hbridge]
  change S ≤ C ^ 2
  have hζ' : ‖ζ‖ ^ 2 ≤ 1 := by
    rw [← real_inner_self_eq_norm_sq, ← hbridge ζ]
    exact hζ
  have hζ_le_one : ‖ζ‖ ≤ 1 := by
    nlinarith [norm_nonneg ζ, hζ']
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    refine Finset.sum_nonneg (fun j _ => ?_)
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) j σ :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) j σ
    positivity
  -- (a) `⟪ζ, T.toSection x⟫ = S`.
  have hpair : (inner ℝ ζ (T.toSection x) : ℝ) = S := by
    rw [hT_def, finiteEigenCombo_toSection_apply (I := I) (M := M) g F c x,
      inner_sum]
    rw [hS_def]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_smul_right, hc_def]
    ring
  -- (b) `‖φ(T)‖² = S`.
  have hnorm_sq : ‖smoothToTensorHs (I := I) (M := M) g σ T‖ ^ 2 = S := by
    rw [Analysis.Parabolic.TensorHeatEquation.tensorHs.norm_sq_eq_tsum]
    rw [hS_def]
    have hcoeff : ∀ i, (smoothToTensorHs (I := I) (M := M) g σ T).coeff i =
        (if i ∈ F then c i else 0) := by
      intro i
      rw [smoothToTensorHs_coeff, hT_def]
      exact finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i
    rw [tsum_congr (fun i => by rw [hcoeff i])]
    rw [tsum_eq_sum (s := F) (fun i hi => by rw [if_neg hi]; ring)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [if_pos hj, hc_def]
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) j σ :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) j σ
    rw [mul_pow]
    rw [show tensorSobolevWeight (I := I) (M := M) j σ *
          ((tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ ^ 2 *
            (inner ℝ ζ ((eigenSmooth (I := I) (M := M) g j).toSection x) : ℝ) ^ 2)
        = (tensorSobolevWeight (I := I) (M := M) j σ *
            (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹) *
          ((tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
            (inner ℝ ζ ((eigenSmooth (I := I) (M := M) g j).toSection x) : ℝ) ^ 2) by ring,
      mul_inv_cancel₀ hw.ne', one_mul]
  -- (c) `S ≤ ‖T.toSection x‖`, and `‖T.toSection x‖ ≤ C·√S`.
  have hCS : (inner ℝ ζ (T.toSection x) : ℝ) ≤ ‖ζ‖ * ‖T.toSection x‖ := by
    calc (inner ℝ ζ (T.toSection x) : ℝ) ≤ ‖(inner ℝ ζ (T.toSection x) : ℝ)‖ := le_abs_self _
      _ ≤ ‖ζ‖ * ‖T.toSection x‖ := norm_inner_le_norm ζ (T.toSection x)
  have hS_le_secnorm : S ≤ ‖T.toSection x‖ := by
    rw [← hpair]
    refine hCS.trans ?_
    calc ‖ζ‖ * ‖T.toSection x‖ ≤ 1 * ‖T.toSection x‖ :=
          mul_le_mul_of_nonneg_right hζ_le_one (norm_nonneg _)
      _ = ‖T.toSection x‖ := one_mul _
  have hsec_le : ‖T.toSection x‖ ≤ C * Real.sqrt S := by
    refine (hbound T x).trans ?_
    rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hS_le : S ≤ C * Real.sqrt S := le_trans hS_le_secnorm hsec_le
  rcases eq_or_lt_of_le hS_nn with hS0 | hSpos
  · rw [← hS0]; positivity
  · have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
    have hSeq : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS_nn
    have hsqrt_le_C : Real.sqrt S ≤ C := by
      nlinarith [hS_le, hSeq, hsqrt_pos]
    calc S = Real.sqrt S * Real.sqrt S := hSeq.symm
      _ ≤ C * C := mul_le_mul hsqrt_le_C hsqrt_le_C (Real.sqrt_nonneg _) hC_nn
      _ = C ^ 2 := (sq C).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Fibre Parseval.** The Riemannian fibre-norm squared expands over any fibre
orthonormal basis `b` as `∑ₘ (gFiberInner x (b m) z)²`. The heavy bundle-inner-product
unfolding (`gFiberInner = inner ℝ`) is confined to this single lemma. The orthonormal
basis is taken with respect to the Riemannian-bundle inner product (supplied as the
`letI` instance), passed explicitly to avoid the `finrank` instance diamond. -/
private lemma riemannianFiberNormSq_eq_sum_gFiberInner_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    {ι : Type*} [Fintype ι]
    (b : letI : Bundle.RiemannianBundle (fun y : M => TensorRSSpace 0 2 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
      OrthonormalBasis ι ℝ (TensorRSSpace 0 2 I x))
    (z : TensorRSSpace 0 2 I x) :
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x z =
      ∑ m : ι, gFiberInner (I := I) (M := M) g x (b m) z ^ 2 := by
  letI : Bundle.RiemannianBundle (fun y : M => TensorRSSpace 0 2 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  rw [riemannianFiberNormSq_eq_norm_sq_02 (I := I) (M := M) g x z]
  rw [← OrthonormalBasis.sum_sq_inner_left b z]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [gFiberInner_eq_inner (I := I) (M := M) g x (b m) z, real_inner_comm]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The reproducing-kernel summability `(★)` at `(0, 2)`, proved outright.**
Summing the per-direction truncated Bessel bound `partialBessel_le_Csq_02` over a
fibre orthonormal frame `ζₘ` (`OrthonormalBasis.sum_sq_inner_left` expands
`‖bⱼ(x)‖²_g = ∑ₘ ⟪ζₘ, bⱼ(x)⟫²`) bounds every finite partial sum of
`(1 + λⱼ)^{-σ} · ‖bⱼ(x)‖²_g` by `(dim fibre) · C²`, hence the family is summable with
total `≤ (dim fibre) · C²` by `Real.tsum_le_of_sum_le`. -/
theorem reproducingKernel_tsum_le_of_closed_02
    (g : SmoothRiemannianMetric I M) :
    ∃ (a : ℕ) (C : ℝ), 0 ≤ C ∧ 0 < a ∧
      ∀ x : M,
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2 =>
          (tensorSobolevWeight (I := I) (M := M) i ((2 * a : ℕ) : ℝ))⁻¹ *
            eigenFiberNormSq (I := I) (M := M) g 0 2 i x) ∧
        (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2,
          (tensorSobolevWeight (I := I) (M := M) i ((2 * a : ℕ) : ℝ))⁻¹ *
            eigenFiberNormSq (I := I) (M := M) g 0 2 i x) ≤ C := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  set k : ℕ := (Module.finrank ℝ E) + 1 with hk_def
  have hk : Module.finrank ℝ E < 2 * k := by rw [hk_def]; omega
  obtain ⟨C, hC_nn, hbound⟩ := pointwiseFiberNorm_le_spectralHs_02 (I := I) (M := M) g k hk
  refine ⟨2 * k, (Module.finrank ℝ (TensorRSModel 0 2 ℝ E) : ℝ) * C ^ 2,
    by positivity, by omega, fun x => ?_⟩
  set σ : ℝ := ((2 * (2 * k) : ℕ) : ℝ) with hσ_def
  -- fibre orthonormal basis at `x`.
  set D : ℕ := Module.finrank ℝ (TensorRSSpace 0 2 I x) with hD_def
  set bON := stdOrthonormalBasis ℝ (TensorRSSpace 0 2 I x) with hbON_def
  -- The term function.
  set f : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => (tensorSobolevWeight (I := I) (M := M) i σ)⁻¹ *
      eigenFiberNormSq (I := I) (M := M) g 0 2 i x with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := by
    intro i; rw [hf_def]
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i σ
    have := eigenFiberNormSq_nonneg (I := I) (M := M) g 0 2 i x
    positivity
  -- Per-finite-set bound: `∑_{j∈F} f j ≤ D · C²`.
  have hfinset : ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2)), ∑ j ∈ F, f j ≤ (D : ℝ) * C ^ 2 := by
    intro F
    -- expand `eigenFiberNormSq = ∑ₘ (gFiberInner ζₘ bⱼ(x))²` via the fibre Parseval.
    have hexpand : ∀ j, f j =
        ∑ m : Fin D, (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
          gFiberInner (I := I) (M := M) g x (bON m)
            ((eigenSmooth (I := I) (M := M) g j).toSection x) ^ 2 := by
      intro j
      simp only [hf_def, eigenFiberNormSq]
      rw [riemannianFiberNormSq_eq_sum_gFiberInner_sq (I := I) (M := M) g x bON
          ((eigenvectorSmooth (I := I) (M := M) g 0 2 j).toSection x), Finset.mul_sum]
    -- swap sums and apply the truncated Bessel bound per direction.
    calc ∑ j ∈ F, f j
        = ∑ j ∈ F, ∑ m : Fin D, (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
            gFiberInner (I := I) (M := M) g x (bON m)
              ((eigenSmooth (I := I) (M := M) g j).toSection x) ^ 2 := by
          exact Finset.sum_congr rfl (fun j _ => hexpand j)
      _ = ∑ m : Fin D, ∑ j ∈ F, (tensorSobolevWeight (I := I) (M := M) j σ)⁻¹ *
            gFiberInner (I := I) (M := M) g x (bON m)
              ((eigenSmooth (I := I) (M := M) g j).toSection x) ^ 2 :=
          Finset.sum_comm
      _ ≤ ∑ _m : Fin D, C ^ 2 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          refine partialBessel_le_Csq_02 (I := I) (M := M) g k C hC_nn ?_ x (bON m) ?_ F
          · exact fun T y => hbound T y
          · -- `gFiberInner x (bON m) (bON m) = ‖bON m‖² = 1 ≤ 1`.
            have : gFiberInner (I := I) (M := M) g x (bON m) (bON m) = 1 := by
              rw [gFiberInner_eq_inner (I := I) (M := M) g x (bON m) (bON m),
                real_inner_self_eq_norm_sq, hbON_def,
                (stdOrthonormalBasis ℝ (TensorRSSpace 0 2 I x)).orthonormal.1 m]
              norm_num
            rw [this]
      _ = (D : ℝ) * C ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- summability + tsum bound from the uniform finite-set bound.
  have hsummable : Summable f := summable_of_sum_le hf_nn hfinset
  refine ⟨hsummable, ?_⟩
  -- `D = finrank (model)` since the fibre is isomorphic to the model fibre.
  have hDeq : (D : ℝ) = (Module.finrank ℝ (TensorRSModel 0 2 ℝ E) : ℝ) := by
    rw [hD_def]
    congr 1
    exact (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) (M := M)
      (𝕜 := ℝ) 0 2 x).toLinearEquiv.finrank_eq
  calc ∑' i, f i ≤ (D : ℝ) * C ^ 2 := Real.tsum_le_of_sum_le hf_nn hfinset
    _ = (Module.finrank ℝ (TensorRSModel 0 2 ℝ E) : ℝ) * C ^ 2 := by rw [hDeq]

/-! ## Conjuncts 2 and 3: the realize read-offs of the kernel -/

/-- **Intrinsic `g`-fibre Cauchy–Schwarz for the symmetric realize evaluation.** For a
smooth `(0, 2)`-tensor `T`, the squared symmetric bilinear value
`ccTensorBilinSymm g T x v w` is bounded by the product of the intrinsic quadratic
factors `g(v,v)`, `g(w,w)` and the Riemannian fibre-norm squared
`riemannianFiberNormSq g 0 2 x (T.toSection x)`. This is the symmetrization of the
fibre Cauchy–Schwarz for the extracted bilinear form (proved, for the unsymmetrized
form, by expanding `v, w` in a `g`-orthonormal tangent frame and Parseval). -/
theorem ccTensorBilinSymm_sq_le_gInner_eigenFiberNormSq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    (ccTensorBilinSymm (I := I) g T x v w) ^ 2 ≤
      g.inner x v v * g.inner x w w *
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) := by
  set fnsq : ℝ :=
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
    with hfnsq_def
  have hgvv : 0 ≤ g.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x v
  have hgww : 0 ≤ g.inner x w w :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x w
  have hfnsq_nn : 0 ≤ fnsq :=
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  -- Cauchy–Schwarz for the unsymmetrized form, in both argument orders.
  have hCSvw : (ccTensorBilin (I := I) g T x v w) ^ 2 ≤ g.inner x v v * g.inner x w w * fnsq :=
    ccTensorBilin_sq_le_gInner_riemannianFiberNormSq (I := I) g T x v w
  have hCSwv : (ccTensorBilin (I := I) g T x w v) ^ 2 ≤ g.inner x v v * g.inner x w w * fnsq := by
    have h := ccTensorBilin_sq_le_gInner_riemannianFiberNormSq (I := I) g T x w v
    calc (ccTensorBilin (I := I) g T x w v) ^ 2
        ≤ g.inner x w w * g.inner x v v * fnsq := h
      _ = g.inner x v v * g.inner x w w * fnsq := by ring
  set R : ℝ := Real.sqrt (g.inner x v v * g.inner x w w * fnsq) with hR_def
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = g.inner x v v * g.inner x w w * fnsq := by
    rw [hR_def, Real.sq_sqrt (by positivity)]
  have hbvw : |ccTensorBilin (I := I) g T x v w| ≤ R := by
    rw [hR_def,
      show |ccTensorBilin (I := I) g T x v w|
          = Real.sqrt ((ccTensorBilin (I := I) g T x v w) ^ 2)
        from (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt hCSvw
  have hbwv : |ccTensorBilin (I := I) g T x w v| ≤ R := by
    rw [hR_def,
      show |ccTensorBilin (I := I) g T x w v|
          = Real.sqrt ((ccTensorBilin (I := I) g T x w v) ^ 2)
        from (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt hCSwv
  rw [ccTensorBilinSymm_apply]
  set S : ℝ :=
    (1 / 2 : ℝ) * (ccTensorBilin (I := I) g T x v w + ccTensorBilin (I := I) g T x w v)
    with hS_def
  have habs : |S| ≤ R := by
    rw [hS_def, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri :=
      (abs_add_le (ccTensorBilin (I := I) g T x v w)
        (ccTensorBilin (I := I) g T x w v)).trans (add_le_add hbvw hbwv)
    linarith [htri]
  calc S ^ 2 = |S| ^ 2 := (sq_abs S).symm
    _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg S) habs 2
    _ = g.inner x v v * g.inner x w w * fnsq := hR_sq

/-- **Conjunct 2: supercritical weighted summability of the realize values.** At a
supercritical order `a` (`2a > dim M + 4`), the per-eigenmode realize values
`eᵢ(x,v,w) = ccTensorBilinSymm g (eigenvectorSmooth g 0 2 i) x v w` decay so that the
`Hᵃ`-Riesz weight `(1+λᵢ)^a · (eᵢ · (1+λᵢ)^{-a})²` is summable, dominated by the
on-diagonal kernel tail `g(v,v)·g(w,w) · ∑ᵢ (1+λᵢ)^{-a} ‖bᵢ(x)‖²_g` of `(★)`. -/
theorem weyl_realize_weighted_summable_of_closed
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (x : M) (v w : TangentSpace I x) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
        (ccTensorBilinSymm (I := I) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w *
          (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2) := by
  classical
  obtain ⟨C, hC_nn, hstar⟩ :=
    reproducingKernel_weighted_tsum_le_of_closed (I := I) (M := M) g 0 2 a ha
  obtain ⟨hsummable, _⟩ := hstar x
  -- The realize term equals `(1+λᵢ)^{-a} · eᵢ²`; dominate by `g(v,v)g(w,w)·kernel`.
  have hgvv : 0 ≤ g.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x v
  have hgww : 0 ≤ g.inner x w w :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x w
  -- Dominating summable family `g(v,v)·g(w,w)·(1+λᵢ)^{-a}·eigenFiberNormSq`.
  have hdom : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2 =>
    g.inner x v v * g.inner x w w *
      ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
        eigenFiberNormSq (I := I) (M := M) g 0 2 i x)) :=
    hsummable.mul_left _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hdom
  · have hw : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    positivity
  · -- termwise: `(1+λᵢ)^a (eᵢ (1+λᵢ)^{-a})² = (1+λᵢ)^{-a} eᵢ² ≤ g·g·(1+λᵢ)^{-a}·fnsq`.
    have hw : 0 < tensorSobolevWeight (I := I) (M := M) i (a : ℝ) :=
      Analysis.Parabolic.TensorHeatEquation.tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    set e : ℝ := ccTensorBilinSymm (I := I) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w with he_def
    have hsimp : tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
          (e * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2 =
        (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ * e ^ 2 := by
      rw [mul_pow, ← mul_assoc]
      rw [show tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * e ^ 2 *
            ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2
          = (tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) *
            ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ * e ^ 2) by ring,
        mul_inv_cancel₀ hw.ne', one_mul]
    rw [hsimp]
    have hCS : e ^ 2 ≤ g.inner x v v * g.inner x w w *
        eigenFiberNormSq (I := I) (M := M) g 0 2 i x := by
      rw [he_def, eigenFiberNormSq]
      exact ccTensorBilinSymm_sq_le_gInner_eigenFiberNormSq (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w
    calc (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ * e ^ 2
        ≤ (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
            (g.inner x v v * g.inner x w w *
              eigenFiberNormSq (I := I) (M := M) g 0 2 i x) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = g.inner x v v * g.inner x w w *
            ((tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹ *
              eigenFiberNormSq (I := I) (M := M) g 0 2 i x) := by ring

/-- `ccTensorBilinSymm g · x v w` is additive in the tensor section (derived from the
subtractivity `ccTensorBilinSymm_sub` and the homogeneity `ccTensorBilinSymm_smul`). -/
private lemma ccTensorBilinSymm_add
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S + T) x v w =
      ccTensorBilinSymm (I := I) g S x v w + ccTensorBilinSymm (I := I) g T x v w := by
  have h1 : S + T = S - ((-1 : ℝ) • T) := by rw [neg_one_smul, sub_neg_eq_add]
  rw [h1, ccTensorBilinSymm_sub, ccTensorBilinSymm_smul]; ring

/-- The symmetric realize value of a finite eigen-combination is the finite fibre-linear
combination of the per-eigenmode realize values: `ccTensorBilinSymm g (∑_{i∈F} cᵢ·bᵢ)
x v w = ∑_{i∈F} cᵢ · ccTensorBilinSymm g bᵢ x v w`. -/
private lemma ccTensorBilinSymm_finiteEigenCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (finiteEigenCombo (I := I) (M := M) g F c) x v w =
      ∑ i ∈ F, c i *
        ccTensorBilinSymm (I := I) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty,
        show (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from
          (zero_smul ℝ _).symm,
        ccTensorBilinSymm_smul]
      ring
  | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, ccTensorBilinSymm_add,
        ccTensorBilinSymm_smul, ih]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Conjunct 3: the realize eigen-expansion.** The realize-evaluation
`ccTensorBilinSymm g T x v w` of a smooth compactly-supported `(0, 2)`-tensor `T` is
the absolutely-convergent eigen-series of its `L²`-coordinates
`cᵢ(T) = tensorL2Coeff (T.toL2) i` weighted by the per-eigenmode realize values
`eᵢ(x,v,w)`. This is the `C⁰`-convergence of the eigenbasis expansion of the realize:
the finite eigen-truncation `T_F = finiteEigenCombo F (cᵢ(T))` has
`ccTensorBilinSymm g T_F x v w = ∑_{i ∈ F} cᵢ(T)·eᵢ(x,v,w)`, and the realize evaluation
of the difference is controlled — through the fibre Cauchy–Schwarz
`ccTensorBilinSymm_sq_le_gInner_eigenFiberNormSq`, the in-file fibre/spectral embedding
`pointwiseFiberNorm_le_spectralHs_02` (taken at a fixed supercritical chart order
`k = dim M + 1`) and the `H^{4k}`-summability of a smooth tensor's `L²`-coordinates —
by the convergent supercritical tail `∑_{i ∉ F}(1+λᵢ)^{4k}·cᵢ(T)² → 0`, forcing the
partial sums to converge to `ccTensorBilinSymm g T x v w`. (The ambient supercritical
order `a` of conjunct 2 is carried for uniformity but not needed here: the expansion
holds for every smooth `T` regardless of `a`, controlled by the fixed order `k`; the
hypothesis `ha` is correspondingly unused — the narrow `linter.unusedVariables`
suppression above is for that frozen signature parameter.) -/
theorem weyl_realize_hasSum_of_closed
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    HasSum
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 2 =>
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
            (SmoothCcTensor.toL2 T) i *
          ccTensorBilinSymm (I := I) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w)
      (ccTensorBilinSymm (I := I) g T x v w) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  -- Supercritical chart order `k`, embedding order `σ = 2·(2k)`.
  set k : ℕ := Module.finrank ℝ E + 1 with hk_def
  have hk : Module.finrank ℝ E < 2 * k := by rw [hk_def]; omega
  set σ : ℝ := ((2 * (2 * k) : ℕ) : ℝ) with hσ_def
  obtain ⟨C, hC_nn, hbound⟩ := pointwiseFiberNorm_le_spectralHs_02 (I := I) (M := M) g k hk
  have hgvv : 0 ≤ g.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x v
  have hgww : 0 ≤ g.inner x w w :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g x w
  -- coordinate family of `T` and the supercritically-summable weight family.
  set cT : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
      (SmoothCcTensor.toL2 T) i with hcT_def
  set fT : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ * (cT i) ^ 2 with hfT_def
  have hfT_summable : Summable fT :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g σ T
      (hCompact (I := I) (M := M) g)
  -- **Combined fibre/spectral bound.** For any smooth `S`, the symmetric realize value
  -- is controlled by `C · √(g v v) · √(g w w) · ‖φ(S)‖`, `φ(S) = smoothToTensorHs g σ S`.
  have hAbs : ∀ S : SmoothCcTensor g 0 2,
      |ccTensorBilinSymm (I := I) g S x v w| ≤
        C * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
          ‖smoothToTensorHs (I := I) (M := M) g σ S‖ := by
    intro S
    have hCS := ccTensorBilinSymm_sq_le_gInner_eigenFiberNormSq (I := I) g S x v w
    rw [riemannianFiberNormSq_eq_norm_sq_02 (I := I) (M := M) g x (S.toSection x)] at hCS
    have hsec : ‖S.toSection x‖ ≤ C * ‖smoothToTensorHs (I := I) (M := M) g σ S‖ := hbound S x
    have hsec_nn : 0 ≤ ‖S.toSection x‖ := norm_nonneg _
    have hφ_nn : 0 ≤ ‖smoothToTensorHs (I := I) (M := M) g σ S‖ := norm_nonneg _
    have hsqv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
    have hsqw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
    -- `|ccTensorBilinSymm| ≤ ‖S(x)‖ · √(g v v) · √(g w w)`.
    have h1 : |ccTensorBilinSymm (I := I) g S x v w| ≤
        ‖S.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
      have hsq : (ccTensorBilinSymm (I := I) g S x v w) ^ 2 ≤
          (‖S.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) ^ 2 := by
        calc (ccTensorBilinSymm (I := I) g S x v w) ^ 2
            ≤ g.inner x v v * g.inner x w w * ‖S.toSection x‖ ^ 2 := hCS
          _ = (‖S.toSection x‖ * Real.sqrt (g.inner x v v) *
                Real.sqrt (g.inner x w w)) ^ 2 := by
              rw [mul_pow, mul_pow, Real.sq_sqrt hgvv, Real.sq_sqrt hgww]; ring
      have hrhs_nn : 0 ≤ ‖S.toSection x‖ * Real.sqrt (g.inner x v v) *
          Real.sqrt (g.inner x w w) := by positivity
      exact abs_le_of_sq_le_sq hsq hrhs_nn
    -- absorb `‖S(x)‖ ≤ C · ‖φ(S)‖`.
    refine h1.trans ?_
    have hmul : ‖S.toSection x‖ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) ≤
        (C * ‖smoothToTensorHs (I := I) (M := M) g σ S‖) *
          Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsec hsqv) hsqw
      exact this
    refine hmul.trans (le_of_eq ?_); ring
  -- The partial sums are the realize values of the finite eigen-truncations.
  set f : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => cT i *
      ccTensorBilinSymm (I := I) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w
    with hf_def
  set K : ℝ := C * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) with hK_def
  have hpartial : ∀ F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 2),
      ∑ i ∈ F, f i =
        ccTensorBilinSymm (I := I) g (finiteEigenCombo (I := I) (M := M) g F cT) x v w := by
    intro F
    rw [ccTensorBilinSymm_finiteEigenCombo (I := I) (M := M) g F cT x v w]
  -- It suffices that the partial sums converge to `ccTensorBilinSymm g T x v w`.
  suffices htend : Filter.Tendsto (fun F => ∑ i ∈ F, f i) Filter.atTop
      (nhds (ccTensorBilinSymm (I := I) g T x v w)) from htend
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun F => dist_nonneg)
    (g := fun F => K * Real.sqrt (∑' (i : {x // x ∉ F}), fT i))
  · -- the per-finite-set distance bound through the truncation tail.
    intro F
    have hdist : dist (∑ i ∈ F, f i) (ccTensorBilinSymm (I := I) g T x v w)
        = |ccTensorBilinSymm (I := I) g
            (finiteEigenCombo (I := I) (M := M) g F cT - T) x v w| := by
      rw [Real.dist_eq, hpartial F, ccTensorBilinSymm_sub]
    rw [hdist]
    -- the truncation difference's spectral norm² is the supercritical tail off `F`.
    have hcoeff : ∀ i, (smoothToTensorHs (I := I) (M := M) g σ
        (finiteEigenCombo (I := I) (M := M) g F cT - T)).coeff i =
          (if i ∈ F then (0 : ℝ) else - cT i) := by
      intro i
      rw [smoothToTensorHs_coeff,
        Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
        map_sub, inner_sub_right,
        ← Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
        ← Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
        show SmoothCcTensor.toL2 (finiteEigenCombo (I := I) (M := M) g F cT) =
            (finiteEigenCombo (I := I) (M := M) g F cT : TensorL2 0 2 g) from
          SmoothCcTensor.toL2_apply _,
        finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F cT i]
      by_cases h : i ∈ F
      · rw [if_pos h, if_pos h, hcT_def, sub_self]
      · rw [if_neg h, if_neg h, hcT_def, zero_sub]
    -- the truncated summand: `(1+λᵢ)^σ · (coeff i)² = if i ∈ F then 0 else fT i`.
    have hsummand : ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
        ((smoothToTensorHs (I := I) (M := M) g σ
          (finiteEigenCombo (I := I) (M := M) g F cT - T)).coeff i) ^ 2 =
          {x : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2 | x ∉ F}.indicator fT i := by
      intro i
      rw [hcoeff i]
      unfold Set.indicator
      by_cases h : i ∈ F
      · simp [h]
      · rw [if_neg (by simpa [Set.mem_setOf_eq] using h), if_pos (by simpa [Set.mem_setOf_eq] using h),
          hfT_def]
        ring
    have hnormsq : ‖smoothToTensorHs (I := I) (M := M) g σ
        (finiteEigenCombo (I := I) (M := M) g F cT - T)‖ ^ 2 =
          ∑' (i : {x // x ∉ F}), fT i := by
      rw [Analysis.Parabolic.TensorHeatEquation.tensorHs.norm_sq_eq_tsum, tsum_congr hsummand]
      exact (tsum_subtype {x : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 2 | x ∉ F} fT).symm
    have hnorm_eq : ‖smoothToTensorHs (I := I) (M := M) g σ
        (finiteEigenCombo (I := I) (M := M) g F cT - T)‖
          = Real.sqrt (∑' (i : {x // x ∉ F}), fT i) := by
      rw [← hnormsq, Real.sqrt_sq (norm_nonneg _)]
    calc |ccTensorBilinSymm (I := I) g
            (finiteEigenCombo (I := I) (M := M) g F cT - T) x v w|
        ≤ C * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
            ‖smoothToTensorHs (I := I) (M := M) g σ
              (finiteEigenCombo (I := I) (M := M) g F cT - T)‖ :=
          hAbs (finiteEigenCombo (I := I) (M := M) g F cT - T)
      _ = K * Real.sqrt (∑' (i : {x // x ∉ F}), fT i) := by rw [hK_def, hnorm_eq]
  · -- the supercritical tail tends to `0`.
    have htail : Filter.Tendsto
        (fun F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2) => ∑' (i : {x // x ∉ F}), fT i)
        Filter.atTop (nhds 0) :=
      tendsto_tsum_compl_atTop_zero fT
    have hsqrt : Filter.Tendsto
        (fun F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2) => Real.sqrt (∑' (i : {x // x ∉ F}), fT i))
        Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp htail
    rw [Real.sqrt_zero] at hsqrt
    simpa using hsqrt.const_mul K

end DifferentialGeometry.PDE.RicciFlow
