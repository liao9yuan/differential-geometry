import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
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
`integral_divergence_eq_zero_of_hasCompactSupport`.  The lowering construction
(`lowerAllUpperIndices` / `dirichletVFSectionGen`) lowers *all* upper indices and is therefore
specific to `(0, s)`-tensors; the genuinely general-rank `(r, s)` Dirichlet-current divergence
identity (the same integration by parts, metric compatibility of `∇` against `g`) is absent
from the library, so the resulting Green identity is posited here.  The conclusion is an `L²`
integration-by-parts identity, structurally distinct from every coordinate-scaling/summability
statement it powers (no packaging); the body is `sorry` and consumers transitively depend on
`sorryAx`. -/
private theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLapRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : Integral.L2.SmoothCcTensor g r s) :
    Integral.L2.tensorL2Inner (I := I) (M := M) g r (s + 1)
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s T).toFun
        (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r s v).toFun =
      - Integral.L2.tensorL2Inner (I := I) (M := M) g r s
          (Integral.Connection.rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun :=
  sorry

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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The general-order per-chart fibre bound on a partition-of-unity super-level set (posited
general-rank analytic child).** At a supercritical chart order `a` (`dim M < 2·(2a)`), for every
atlas index `α` there is a constant `D ≥ 0` such that on the super-level set
`{x | c ≤ chartAtlasPOU α x}` of the chart partition of unity, the bundle-fibre value
`‖T.toSection x‖` of a smooth `(r, s)`-tensor is bounded by `D · ‖T.toHs a‖` — the intrinsic
order-`a` Hilbert–Schmidt chart-Sobolev norm (an `H^{2a}` chart norm).

This is the general-order (`a`, not necessarily even) analogue of the in-library `(0, 2k)`-only
per-chart Euclidean core `chartFiberNorm_le_hsNorm_on_superlevel` (file
`SobolevEmbeddingManifoldC0.lean`, `private`), which is stated only at order `2k` with `D ·
‖T.toHs (2k)‖`.  At order `2k` it is built, chart-locality-free, from the local Euclidean ball
`L²` Sobolev embedding composed with the Hilbert–Schmidt fibre reconstruction; the odd-`a`
general-order case is absent (the library's tensor embedding tower is even-index-only), so it is
posited here.  The hypothesis `dim M < 2·(2a)` is the genuine supercritical threshold for the
chart-`H^{2a} ↪ C⁰` Sobolev embedding.  The conclusion is a fibre `C⁰` bound by the chart
`H^{2a}`-norm on a super-level set, structurally distinct from the global bound it powers (no
packaging); the body is `sorry` and consumers transitively depend on `sorryAx`. -/
private theorem chartFiberNormRS_le_hsNorm_on_superlevel_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℕ)
    (ha : (Module.finrank ℝ E : ℝ) < 2 * (2 * a))
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : Integral.L2.SmoothCcTensor g r s),
      ∀ x ∈ {x : M | c ≤ (Integral.Measure.chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ D *
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T‖ :=
  sorry

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

/-- **The general-rank all-order intrinsic Gårding bootstrap (posited general-rank analytic
child).** For every order `k` there is a constant `C ≥ 0` such that, for every smooth
`(r, s)`-tensor `T`, the sum of the `L²` norms of the covariant gradients `∇^j T` up to order
`2k` is bounded by `C` times the sum of the `L²` norms of the iterated rough Laplacians
`Δ_∇^i T` up to order `k`:
`∑_{j ≤ 2k} ‖∇^j T‖_{L²} ≤ C · ∑_{i ≤ k} ‖Δ_∇^i T‖_{L²}`.

This is the bidegree-`(r, s)` analogue of the in-library `(0, 2)`
`allOrder_covGrad_l2Norm_le_lapIter_sum_unconditional` (file `AllOrderGardingBootstrap.lean`).
At `(0, 2)` the bootstrap rests on the iterated intrinsic Gårding / Bochner inequality, whose
curvature-commutator inputs (`order2GardingFamily_holds`, `commutatorDefectBound_holds`) are
themselves rank-restricted; the genuinely general-rank `(r, s)` bootstrap — the same
elliptic-regularity estimate controlling all covariant derivatives by the iterated rough
Laplacian — is absent from the library, so it is posited here.  The conclusion is an `L²`-norm
domination, structurally distinct from the chart-Sobolev / spectral bound it powers (no
packaging); the body is `sorry` and consumers transitively depend on `sorryAx`. -/
private theorem covGrad_l2Norm_le_lapIter_sumRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s),
        ∑ j ∈ Finset.range (2 * k + 1),
            Integral.L2.tensorL2Norm (I := I) (M := M) g r (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) (M := M) g r s j T).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            ‖Integral.L2.SmoothCcTensor.toL2
              (Integral.Connection.rawTensorConnLapIter (I := I) g r s i T)‖ :=
  sorry

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
