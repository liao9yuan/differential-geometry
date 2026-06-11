import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SharpOrderRealizedJetEmbedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SobolevProductBilinear

/-! # The supercritical chart-Sobolev Banach-algebra product bound

On a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` the chart-partition-of-unity
Sobolev Hilbert scale `‖·.toHs k‖` is a **Banach algebra under the bare fibrewise tensor product**
once the order is high enough (supercritical): for a sufficiently large jet budget there is a single
constant `C` with

  `‖(S ⊗ T).toHs s'‖ ≤ C · ‖S.toHs k‖ · ‖T.toHs k‖`

for all smooth compactly-supported tensor sections `S : (0, s₁)`, `T : (0, s₂)`, where
`S ⊗ T = bareTensorProdSection g S T : (0, s₁ + s₂)`.  This is exactly the
`Analysis.Sobolev.TensorHilbert.SobolevProductBound` hypothesis that the bounded-bilinear-completion
consumer `productBilinCLM` / `isBoundedBilinearMap_productBilin` requires, so this file is the
witness that turns the (otherwise inert) chart-Sobolev product CLM into a genuine bounded bilinear
map on the Hilbert completions — the multiplicative structure a quasilinear chart-Sobolev Nemytskii
functional contracts against.

## The mechanism (the supercritical route — no interpolation)

Unlike the subcritical Gagliardo–Nirenberg / Moser route (which interpolates and is genuinely deep),
the **supercritical** product bound is elementary, because one factor can be carried entirely in the
`C⁰` sup norm:

* **Reverse Hebey bridge** (`exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum`, general valence):
  `‖(S ⊗ T).toHs s'‖ ≤ C₀ · ∑_{j ≤ 2 s'} ‖∇^j (S ⊗ T)‖_{L²}`.
* **Covariant-Leibniz `rfns` grid** (`exists_rfns_iteratedCovGrad_prod_diagGrid_le`, sorry-free):
  `rfns(∇^j (S ⊗ T))(x) ≤ C_j · (∑_{i ≤ j} rfns(∇^i S)(x)) · (∑_{l ≤ j} rfns(∇^l T)(x))` pointwise.
* **Supercritical jet sup-embedding** (`tensorC0_embedding_sharpOrder`, sorry-free): for a high jet
  budget every factor jet `∇^i S` is bounded uniformly in `C⁰` by `‖S.toHs k‖`, so the whole `S`-jet
  sum is bounded by `‖S.toHs k‖²` uniformly over the manifold.
* The remaining `T`-jet sum stays in `L²`, integrated against the manifold's finite volume, and each
  `‖∇^l T‖_{L²}` is dominated by `‖T.toHs k‖` (`iteratedCovGrad_toHs_norm_le` at order `0` plus
  chart-Sobolev order monotonicity).

Integrating `rfns(∇^j (S ⊗ T))` against the supercritical sup bound on the `S`-jets and the `L²`
bound on the `T`-jets yields `‖∇^j (S ⊗ T)‖_{L²} ≤ C' · ‖S.toHs k‖ · ‖T.toHs k‖`; summing over
`j ≤ 2 s'` and folding the finitely-many constants gives the algebra bound.

## Scope of the budget

The order `k` must clear the supercritical sup-embedding threshold for **every** factor jet up to
order `2 s'`: `2 (k − 2 s') > dim M` (equivalently `2 k > dim M + 4 s'`), so the jet `∇^i S` (a
`(0, s₁ + i)`-tensor, `i ≤ 2 s'`) is read in `C⁰` at its own order `k − i ≥ k − 2 s'`, which clears
`dim M`.  This is the honest derivative budget of the algebra: `2 s'` derivatives of head-room on
top of the supercritical floor.  Both the `C⁰` jet sup-bound and the chart-Sobolev order
monotonicity are sorry-free, so the whole witness is sorry-free. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The bare tensor product packaged as an `ℝ`-bilinear map -/

/-- **The bare model tensor product distributes over a sum in the left factor.**
`(S₁ + S₂) ⊗ T = S₁ ⊗ T + S₂ ⊗ T`, derived from the difference / homogeneity bilinearity laws
(`bareTensorProdSection_sub_left`, `bareTensorProdSection_smul_left`) via `S₁ + S₂ = S₁ - (-1) • S₂`. -/
theorem bareTensorProdSection_add_left (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S₁ S₂ : SmoothCcTensor g₀ 0 s₁) (T : SmoothCcTensor g₀ 0 s₂) :
    bareTensorProdSection (I := I) g₀ (S₁ + S₂) T =
      bareTensorProdSection (I := I) g₀ S₁ T + bareTensorProdSection (I := I) g₀ S₂ T := by
  have hsum : S₁ + S₂ = S₁ - (-1 : ℝ) • S₂ := by
    rw [neg_one_smul, sub_neg_eq_add]
  rw [hsum, bareTensorProdSection_sub_left, bareTensorProdSection_smul_left, neg_one_smul,
    sub_neg_eq_add]

/-- **The bare model tensor product distributes over a sum in the right factor.**
`S ⊗ (T₁ + T₂) = S ⊗ T₁ + S ⊗ T₂`. -/
theorem bareTensorProdSection_add_right (g₀ : SmoothRiemannianMetric I M) {s₁ s₂ : ℕ}
    (S : SmoothCcTensor g₀ 0 s₁) (T₁ T₂ : SmoothCcTensor g₀ 0 s₂) :
    bareTensorProdSection (I := I) g₀ S (T₁ + T₂) =
      bareTensorProdSection (I := I) g₀ S T₁ + bareTensorProdSection (I := I) g₀ S T₂ := by
  have hsum : T₁ + T₂ = T₁ - (-1 : ℝ) • T₂ := by
    rw [neg_one_smul, sub_neg_eq_add]
  rw [hsum, bareTensorProdSection_sub_right, bareTensorProdSection_smul_right, neg_one_smul,
    sub_neg_eq_add]

/-- **The bare fibrewise tensor product as an `ℝ`-bilinear map of smooth compactly-supported
sections** `SmoothCcTensor g 0 s₁ →ₗ[ℝ] SmoothCcTensor g 0 s₂ →ₗ[ℝ] SmoothCcTensor g 0 (s₁ + s₂)`.
Additivity / homogeneity in each slot are the bare-product bilinearity laws.  This is the bundled
`prod` argument the chart-Sobolev bounded-bilinear-completion consumer
(`SobolevProductBound` / `productBilinCLM`) requires. -/
def bareTensorProdBilin (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ) :
    Integral.L2.SmoothCcTensor g₀ 0 s₁ →ₗ[ℝ]
      Integral.L2.SmoothCcTensor g₀ 0 s₂ →ₗ[ℝ] Integral.L2.SmoothCcTensor g₀ 0 (s₁ + s₂) where
  toFun S :=
    { toFun := fun T => bareTensorProdSection (I := I) g₀ S T
      map_add' := bareTensorProdSection_add_right (I := I) g₀ S
      map_smul' := fun c T => by
        simp only [RingHom.id_apply]; exact bareTensorProdSection_smul_right (I := I) g₀ c S T }
  map_add' S₁ S₂ := by
    refine LinearMap.ext (fun T => ?_)
    exact bareTensorProdSection_add_left (I := I) g₀ S₁ S₂ T
  map_smul' c S := by
    refine LinearMap.ext (fun T => ?_)
    simp only [RingHom.id_apply, LinearMap.smul_apply]
    exact bareTensorProdSection_smul_left (I := I) g₀ c S T

@[simp] theorem bareTensorProdBilin_apply (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ : ℕ)
    (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (T : Integral.L2.SmoothCcTensor g₀ 0 s₂) :
    bareTensorProdBilin (I := I) g₀ s₁ s₂ S T = bareTensorProdSection (I := I) g₀ S T := rfl

/-! ## The uniform supercritical sup-bound on a single factor's covariant jets -/

/-- **Uniform supercritical `C⁰` bound on a factor's covariant `i`-jet by its order-`k` chart-Sobolev
norm.**  For a base valence `s₁`, a head-room order `J`, and a Sobolev order `k = N + J` whose
floor `N` clears the sup-embedding threshold (`dim M < 2 N`), every covariant jet `∇^i S`
(`i ≤ J`, a `(0, s₁ + i)`-tensor) has its intrinsic fibre-norm-square bounded uniformly — over the
manifold, over `i ≤ J`, over `S` — by the square of the order-`k` chart-Sobolev norm of `S`:
`rfns(∇^i S)(x) ≤ C² · ‖S.toHs k‖²`.

The constant `C` is the supercritical sup-embedding constant `tensorC0_embedding_sharpOrder` (at
valence `(0, s₁ + i)`, order `N`) composed with the iterated-gradient order-dropping bound
`iteratedCovGrad_toHs_norm_le` (`‖(∇^i S).toHs N‖ ≤ C · ‖S.toHs (N + i)‖`) and chart-Sobolev order
monotonicity (`N + i ≤ N + J = k`).  Mirrors `exists_riemannianFiberNormSq_le_toHs_sq_supercritical`
at jet valence; the `√rfns = ‖·.toSection·‖` identity is the installed-bundle bridge. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_le_toHs_sq_supercritical
    (g₀ : SmoothRiemannianMetric I M) (s₁ J N : ℕ)
    (h_super : Module.finrank ℝ E < 2 * N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (i : ℕ), i ≤ J → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
            ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) ≤
          C ^ 2 * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + J) S‖ ^ 2 := by
  classical
  -- For each `i`, a uniform sup-bound constant `Ci` valid when `i ≤ J`.
  have hper : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧ (i ≤ J →
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
            ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) ≤
          Ci ^ 2 * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + J) S‖ ^ 2) := by
    intro i
    by_cases hi : i ≤ J
    · -- The sup-embedding at valence `(0, s₁ + i)`, order `N`.
      obtain ⟨A, hA_pos, hA⟩ :=
        tensorC0_embedding_sharpOrder (I := I) (M := M) g₀ 0 (s₁ + i) N h_super
      -- The iterated-gradient order-dropping bound `‖(∇^i S).toHs N‖ ≤ B · ‖S.toHs (N + i)‖`.
      obtain ⟨B, hB_nn, hB⟩ :=
        iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 s₁ i N
      refine ⟨A * B, mul_nonneg (le_of_lt hA_pos) hB_nn, fun _ S x => ?_⟩
      set NS := ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + J) S‖ with hNS
      have hNS_nn : 0 ≤ NS := norm_nonneg _
      -- `√rfns(∇^i S) = ‖(∇^i S).toSection x‖` (installed bundle); then
      -- `‖(∇^i S).toSection x‖ ≤ A · ‖(∇^i S).toHs N‖ ≤ A·B·‖S.toHs (N + i)‖ ≤ A·B·‖S.toHs (N+J)‖`.
      have hsqrt :
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
              ((iteratedCovGrad g₀ 0 s₁ i S).toSection x)) ≤ (A * B) * NS := by
        rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M)
          g₀ 0 (s₁ + i) (iteratedCovGrad g₀ 0 s₁ i S) x]
        refine le_trans (hA (iteratedCovGrad g₀ 0 s₁ i S) x) ?_
        refine le_trans (mul_le_mul_of_nonneg_left (hB S) (le_of_lt hA_pos)) ?_
        rw [show A * (B * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + i) S‖) =
            (A * B) * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + i) S‖ from by ring]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hA_pos) hB_nn)
        rw [hNS]
        exact toHs_norm_mono_order (I := I) (M := M) g₀ (by omega : N + i ≤ N + J) S
      -- Square the `√rfns` bound.
      have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
          ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₁ + i) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
              ((iteratedCovGrad g₀ 0 s₁ i S).toSection x)
          = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
              ((iteratedCovGrad g₀ 0 s₁ i S).toSection x)) ^ 2 :=
            (Real.sq_sqrt hrfns_nn).symm
        _ ≤ ((A * B) * NS) ^ 2 := by
            apply sq_le_sq'
            · linarith [mul_nonneg (mul_nonneg (le_of_lt hA_pos) hB_nn) hNS_nn,
                Real.sqrt_nonneg (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
                  ((iteratedCovGrad g₀ 0 s₁ i S).toSection x))]
            · exact hsqrt
        _ = (A * B) ^ 2 * NS ^ 2 := by rw [mul_pow]
    · exact ⟨0, le_refl 0, fun hi' => absurd hi' hi⟩
  -- Choose the per-`i` constants and take the maximum over `i ∈ range (J + 1)`.
  choose Cfun hCfun_nn hCfun using hper
  refine ⟨(Finset.range (J + 1)).sup' (by simp) Cfun + 1, ?_, fun S i hi x => ?_⟩
  · have : 0 ≤ (Finset.range (J + 1)).sup' (by simp) Cfun := by
      obtain ⟨b, hb⟩ : (Finset.range (J + 1)).Nonempty := by simp
      exact le_trans (hCfun_nn b) (Finset.le_sup' Cfun hb)
    linarith
  · have hi_mem : i ∈ Finset.range (J + 1) := by simp; omega
    have hCi_le : Cfun i ≤ (Finset.range (J + 1)).sup' (by simp) Cfun :=
      Finset.le_sup' Cfun hi_mem
    have hCi_le' : Cfun i ≤ (Finset.range (J + 1)).sup' (by simp) Cfun + 1 := by linarith
    have hbase := hCfun i hi S x
    refine hbase.trans ?_
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply sq_le_sq'
    · linarith [hCfun_nn i]
    · exact hCi_le'

/-! ## The supercritical chart-Sobolev product (Banach-algebra) bound -/

/-- **The supercritical chart-Sobolev Banach-algebra product bound for the bare tensor product.**

On a closed Riemannian manifold, for base valences `s₁, s₂`, output order `s'`, and a chart-Sobolev
input order `k = N + 2 s'` whose floor `N` clears the sup-embedding threshold (`dim M < 2 N`,
equivalently `2 k > dim M + 4 s'`), there is a single constant `C ≥ 0` such that for all smooth
compactly-supported tensor sections `S : (0, s₁)`, `T : (0, s₂)`,

  `‖(S ⊗ T).toHs s'‖ ≤ C · ‖S.toHs k‖ · ‖T.toHs k‖`,

where `S ⊗ T = bareTensorProdSection g S T : (0, s₁ + s₂)`.  This is the
`Analysis.Sobolev.TensorHilbert.SobolevProductBound` witness for the bare product (packaged as the
bilinear map `bareTensorProdBilin`), the input the bounded-bilinear-completion consumer
`productBilinCLM` / `isBoundedBilinearMap_productBilin` requires.

The mechanism is the supercritical route (no interpolation): the reverse Hebey bridge reduces the
output `toHs` norm to a finite sum of jet `L²` norms; each jet `∇^j (S ⊗ T)` is dominated pointwise
by a covariant-Leibniz `rfns` grid (`bareTensorProdSection` transferred from `bareProd` by the
rank-cast `rfns`-invariance); the `S`-factor jets are bounded uniformly in `C⁰` by `‖S.toHs k‖`, the
`T`-factor jets likewise, and integrating against the manifold's finite volume gives each
`‖∇^j (S ⊗ T)‖_{L²} ≤ C' · ‖S.toHs k‖ · ‖T.toHs k‖`.  All inputs are sorry-free.

**Non-vacuity.**  The constant is uniform over `(S, T)`; the bound is multiplicative in both factor
norms (`C = 0` is rejected by any pair whose product has nonzero `toHs s'` norm, the bare product
being genuinely bilinear and nonzero). -/
theorem exists_bareTensorProd_sobolevProductBound_supercritical
    (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ s' N : ℕ)
    (h_super : Module.finrank ℝ E < 2 * N) :
    ∃ C : ℝ, 0 ≤ C ∧
      SobolevProductBound (I := I) g₀ (N + 2 * s') s'
        (bareTensorProdBilin (I := I) g₀ s₁ s₂) C := by
  classical
  -- Unfold `SobolevProductBound` (and `bareTensorProdBilin S T = bareTensorProdSection S T`):
  -- the goal is the explicit dense-subspace product norm bound below.
  suffices h : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (T : Integral.L2.SmoothCcTensor g₀ 0 s₂),
        ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁ + s₂) s'
            (bareTensorProdSection (I := I) g₀ S T)‖ ≤
          C * (‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + 2 * s') S‖ *
            ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₂) (N + 2 * s') T‖) by
    obtain ⟨C, hC_nn, hC⟩ := h
    exact ⟨C, hC_nn, fun S T => hC S T⟩
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  -- The reverse Hebey bridge at the output valence `(0, s₁ + s₂)`, order `s'`.
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 (s₁ + s₂) s'
  -- The covariant-Leibniz `rfns` diagonal grid coefficient for the bare product (`Cg j = mu·4^j`,
  -- here `mu = 1`).  The pointwise grid bound itself (`hCg`) is the explicit-constant form
  -- `rfns_iteratedCovGrad_prod_le_diagGrid`, applied per `(S, T)` below.
  set Cg : ℕ → ℝ := fun j => (bareTensorRfnsBilinearProduct (I := I) g₀ s₁ s₂).mu * (4 : ℝ) ^ j
    with hCg_def
  have hCg_nn : ∀ j, 0 ≤ Cg j := fun j => by
    rw [hCg_def]
    exact mul_nonneg (bareTensorRfnsBilinearProduct (I := I) g₀ s₁ s₂).mu_nonneg (by positivity)
  -- The uniform supercritical sup-bounds on each factor's jets (`J = 2 s'`).
  obtain ⟨CS, hCS_nn, hCS⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_le_toHs_sq_supercritical (I := I) (M := M)
      g₀ s₁ (2 * s') N h_super
  obtain ⟨CT, hCT_nn, hCT⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_le_toHs_sq_supercritical (I := I) (M := M)
      g₀ s₂ (2 * s') N h_super
  -- Finite total volume of the closed manifold.
  haveI : MeasureTheory.IsFiniteMeasure μ := by
    rw [hμ]
    exact DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g₀
  set V : ℝ := μ.real Set.univ with hV_def
  have hV_nn : 0 ≤ V := by rw [hV_def]; exact MeasureTheory.measureReal_nonneg
  -- The per-`j` jet `L²` bound `‖∇^j (S ⊗ T)‖_{L²} ≤ Kj · ‖S.toHs k‖ · ‖T.toHs k‖`.
  refine ⟨CA * ∑ j ∈ Finset.range (2 * s' + 1),
      Real.sqrt (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V),
      ?_, fun S T => ?_⟩
  · refine mul_nonneg hCA_nn (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
  · set NSh := ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + 2 * s') S‖ with hNSh
    set NTh := ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₂) (N + 2 * s') T‖ with hNTh
    have hNSh_nn : 0 ≤ NSh := norm_nonneg _
    have hNTh_nn : 0 ≤ NTh := norm_nonneg _
    -- Abbreviate the product `P = S ⊗ T`.
    set P := bareTensorProdSection (I := I) g₀ S T with hP_def
    -- The rank-cast identification of `P` with the grid's `bareProd`.
    have hcast : ∀ (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x
            ((iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + 0 + 0 + j) x
            ((iteratedCovGrad g₀ 0 (s₁ + s₂ + 0 + 0) j
              ((bareTensorRfnsBilinearProduct (I := I) g₀ s₁ s₂).prod (a := 0) (b := 0) S T)).toSection
                x) := by
      intro j x
      rw [show ((bareTensorRfnsBilinearProduct (I := I) g₀ s₁ s₂).prod (a := 0) (b := 0) S T)
            = castRankCc_db g₀ 0 (by omega : (s₁ + 0) + (s₂ + 0) = s₁ + s₂ + 0 + 0) P from rfl]
      exact (rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
        (by omega : (s₁ + 0) + (s₂ + 0) = s₁ + s₂ + 0 + 0) P j x).symm
    -- The per-`j` uniform pointwise integrand bound.
    have hpt : ∀ (j : ℕ), j ≤ 2 * s' → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x
            ((iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toSection x) ≤
          Cg j * ((2 * s' + 1) * CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2) := by
      intro j hj x
      rw [hcast j x]
      refine le_trans ((bareTensorRfnsBilinearProduct (I := I) g₀ s₁ s₂).rfns_iteratedCovGrad_prod_le_diagGrid
        j (a := 0) (b := 0) S T x) ?_
      simp only [hCg_def]
      -- Bound the `S`-jet sum and the `T`-inner sums uniformly.
      have hSsum : ∀ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
              ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) ≤ CS ^ 2 * NSh ^ 2 := by
        intro i hi
        rw [Finset.mem_range] at hi
        exact hCS S i (by omega) x
      have hTsum : ∀ i l, l ∈ Finset.range (j + 1 - i) →
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + l) x
              ((iteratedCovGrad g₀ 0 s₂ l T).toSection x) ≤ CT ^ 2 * NTh ^ 2 := by
        intro i l hl
        rw [Finset.mem_range] at hl
        exact hCT T l (by omega) x
      -- Each `T`-inner sum `∑_{l < j+1-i} ≤ (j+1) · CT² · NTh²`, then `∑_i ≤ (j+1)² · CS²·CT²·…`.
      have hinner : ∀ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
              ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + l) x
                ((iteratedCovGrad g₀ 0 s₂ l T).toSection x) ≤
          (CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2)) := by
        intro i hi
        have hSi := hSsum i hi
        have hSi_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
            ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₁ + i) x _
        have hinner_sum : ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + l) x
              ((iteratedCovGrad g₀ 0 s₂ l T).toSection x) ≤ (2 * s' + 1) * (CT ^ 2 * NTh ^ 2) := by
          refine le_trans (Finset.sum_le_card_nsmul _ _ (CT ^ 2 * NTh ^ 2)
            (fun l hl => hTsum i l hl)) ?_
          rw [nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Finset.card_range]
          have : (j + 1 - i : ℕ) ≤ 2 * s' + 1 := by omega
          exact_mod_cast this
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + i) x
                ((iteratedCovGrad g₀ 0 s₁ i S).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + l) x
                  ((iteratedCovGrad g₀ 0 s₂ l T).toSection x)
            ≤ (CS ^ 2 * NSh ^ 2) *
                ∑ l ∈ Finset.range (j + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₂ + l) x
                    ((iteratedCovGrad g₀ 0 s₂ l T).toSection x) :=
              mul_le_mul_of_nonneg_right hSi
                (Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg _ _ _ _ _))
          _ ≤ (CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2)) :=
              mul_le_mul_of_nonneg_left hinner_sum (by positivity)
      -- Sum over `i`: `(j+1)` terms each `≤ (CS²·NSh²)·((2s'+1)·CT²·NTh²)`.
      refine le_trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_card_nsmul _ _ _ hinner) (hCg_nn j)) ?_
      rw [nsmul_eq_mul, Finset.card_range]
      have hcard : ((j + 1 : ℕ) : ℝ) ≤ 2 * s' + 1 := by
        have : (j + 1 : ℕ) ≤ 2 * s' + 1 := by omega
        exact_mod_cast this
      -- `Cg j · ((j+1) · ((CS²·NSh²)·((2s'+1)·CT²·NTh²))) ≤ Cg j · (((2s'+1)·CS²·NSh²)·((2s'+1)·CT²·NTh²))`.
      have hCgj : 0 ≤ Cg j := hCg_nn j
      have hjr : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
      have hA_nn : (0 : ℝ) ≤ CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2)) := by positivity
      have key : (↑(j + 1) : ℝ) * (CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2))) ≤
          (2 * s' + 1) * CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2) := by
        calc (↑(j + 1) : ℝ) * (CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2)))
            ≤ (2 * s' + 1) * (CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2))) :=
              mul_le_mul_of_nonneg_right hcard hA_nn
          _ = (2 * s' + 1) * CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2) := by ring
      calc Cg j * (↑(j + 1) * (CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * (CT ^ 2 * NTh ^ 2))))
          ≤ Cg j * ((2 * s' + 1) * CS ^ 2 * NSh ^ 2 * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2)) :=
            mul_le_mul_of_nonneg_left key hCgj
        _ = Cg j * ((2 * s' + 1) * CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2) := by ring
    -- Integrate each pointwise bound: `‖∇^j P‖_{L²} ≤ Kj · NSh · NTh`.
    have hjL2 : ∀ j ∈ Finset.range (2 * s' + 1),
        tensorL2Norm (I := I) (M := M) g₀ 0 (s₁ + s₂ + j)
            (iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toFun ≤
          Real.sqrt (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V) *
            NSh * NTh := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : j ≤ 2 * s' := by omega
      -- The squared `L²` norm is the integral of `rfns`.
      have hsqInt :
          tensorL2Norm (I := I) (M := M) g₀ 0 (s₁ + s₂ + j)
              (iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toFun ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x
              ((iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toSection x) ∂μ :=
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (s₁ + s₂ + j)
          (iteratedCovGrad g₀ 0 (s₁ + s₂) j P)
      have hCgj_nn : 0 ≤ Cg j := hCg_nn j
      -- Bound the integral by `(const) · V`.
      set Ksq : ℝ := Cg j * ((2 * s' + 1) * CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2)
        with hKsq
      have hKsq_nn : 0 ≤ Ksq := by
        rw [hKsq]
        exact mul_nonneg (mul_nonneg hCgj_nn (by positivity)) (by positivity)
      have hint_le :
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x
              ((iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toSection x) ∂μ ≤ Ksq * V := by
        have hint1 := integrable_riemannianFiberNormSq_toSection (I := I) (M := M)
          (g := g₀) (r := 0) (s := s₁ + s₂ + j) (iteratedCovGrad g₀ 0 (s₁ + s₂) j P)
        calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x
                ((iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toSection x) ∂μ
            ≤ ∫ _x, Ksq ∂μ :=
              MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun x =>
                  riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₁ + s₂ + j) x _))
                (MeasureTheory.integrable_const _)
                (Filter.Eventually.of_forall (fun x => hpt j hj' x))
          _ = Ksq * V := by
              rw [MeasureTheory.integral_const, smul_eq_mul, ← hV_def, mul_comm]
      -- Square-root the `L²` bound.
      have hLHS_nn : 0 ≤ tensorL2Norm (I := I) (M := M) g₀ 0 (s₁ + s₂ + j)
          (iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toFun := by
        rw [← SmoothCcTensor.norm_def]; exact norm_nonneg _
      have hRHS_eq : Real.sqrt (Ksq * V) =
          Real.sqrt (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V) * NSh * NTh := by
        rw [hKsq]
        rw [show Cg j * ((2 * s' + 1) * CS ^ 2 * NSh ^ 2) * ((2 * s' + 1) * CT ^ 2 * NTh ^ 2) * V =
            (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V) * (NSh ^ 2 * NTh ^ 2)
          from by ring]
        rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (mul_nonneg hCgj_nn (by positivity))
            (by positivity)) hV_nn), Real.sqrt_mul (by positivity) (NTh ^ 2),
          Real.sqrt_sq hNSh_nn, Real.sqrt_sq hNTh_nn, ← mul_assoc]
      rw [← hRHS_eq]
      have hsq : tensorL2Norm (I := I) (M := M) g₀ 0 (s₁ + s₂ + j)
          (iteratedCovGrad g₀ 0 (s₁ + s₂) j P).toFun ^ 2 ≤ (Real.sqrt (Ksq * V)) ^ 2 := by
        rw [hsqInt, Real.sq_sqrt (mul_nonneg hKsq_nn hV_nn)]
        exact hint_le
      exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
    -- Assemble: reverse-Hebey bridge + the summed jet bounds.
    -- RHS = CA · (Σⱼ √(…)) · (NSh·NTh) = CA · Σⱼ (√(…) · NSh · NTh).
    have hRHS_eq :
        (CA * ∑ j ∈ Finset.range (2 * s' + 1),
            Real.sqrt (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V)) *
          (NSh * NTh) =
          ∑ j ∈ Finset.range (2 * s' + 1),
            CA * (Real.sqrt (Cg j * ((2 * s' + 1) * CS ^ 2) * ((2 * s' + 1) * CT ^ 2) * V) *
              NSh * NTh) := by
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hRHS_eq]
    refine le_trans (hCA P) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact mul_le_mul_of_nonneg_left (hjL2 j hj) hCA_nn

/-! ## The bounded bilinear bare-product on the chart-Sobolev Hilbert completions -/

/-- **The supercritical bare-product bounded bilinear map on the chart-Sobolev Hilbert
completions.**

For a supercritical Sobolev order floor `N` (`dim M < 2 N`) and input order `k = N + 2 s'`, the bare
fibrewise tensor product lifts to a genuine `IsBoundedBilinearMap ℝ` on the chart-Sobolev Hilbert
completions

  `H^k(0,s₁) × H^k(0,s₂) → H^{s'}(0, s₁ + s₂)`,

uncurried from `productBilinCLM` instantiated at the `SobolevProductBound` witness
`exists_bareTensorProd_sobolevProductBound_supercritical`.  On the dense smooth subspace it factors
the order-`s'` class of the product through the two order-`k` embeddings.  This is the exact shape the
`C^∞` product brick `BanachAlgebraSmoothness.contDiffOn_bilinDiag` consumes (a bounded bilinear map is
`C^∞`, so the diagonal of two `C^∞` Sobolev-valued maps is `C^∞`) — i.e. the chart-Sobolev scale is a
Banach algebra under the bare product at supercritical order, the multiplicative structure a
quasilinear chart-Sobolev Nemytskii functional contracts against.

The constant is uniform; non-vacuity is the bilinearity and genuine nonvanishing of the bare
product. -/
theorem exists_isBoundedBilinearMap_bareTensorProd_supercritical
    (g₀ : SmoothRiemannianMetric I M) (s₁ s₂ s' N : ℕ)
    (h_super : Module.finrank ℝ E < 2 * N) :
    ∃ (B : TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₁ (N + 2 * s') ×
          TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 s₂ (N + 2 * s') →
        TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 (s₁ + s₂) s'),
      IsBoundedBilinearMap ℝ B ∧
        ∀ (S : Integral.L2.SmoothCcTensor g₀ 0 s₁) (T : Integral.L2.SmoothCcTensor g₀ 0 s₂),
          B (SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + 2 * s') S,
              SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₂) (N + 2 * s') T)
            = SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁ + s₂) s'
                (bareTensorProdSection (I := I) g₀ S T) := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    exists_bareTensorProd_sobolevProductBound_supercritical (I := I) (M := M) g₀ s₁ s₂ s' N h_super
  refine ⟨fun p => productBilinCLM (I := I) g₀ (N + 2 * s') s'
      (bareTensorProdBilin (I := I) g₀ s₁ s₂) hbound p.1 p.2,
    isBoundedBilinearMap_productBilin (I := I) g₀ (N + 2 * s') s'
      (bareTensorProdBilin (I := I) g₀ s₁ s₂) hbound,
    fun S T => ?_⟩
  change productBilinCLM (I := I) g₀ (N + 2 * s') s'
      (bareTensorProdBilin (I := I) g₀ s₁ s₂) hbound
        (SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁) (N + 2 * s') S)
        (SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₂) (N + 2 * s') T)
      = SmoothCcTensor.toHs (g := g₀) (r := 0) (s := s₁ + s₂) s'
          (bareTensorProdSection (I := I) g₀ S T)
  rw [productBilinCLM_apply_toHs (I := I) g₀ (N + 2 * s') s'
    (bareTensorProdBilin (I := I) g₀ s₁ s₂) hbound hC_nn S T, bareTensorProdBilin_apply]

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
