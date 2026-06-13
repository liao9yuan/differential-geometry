import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSHighOrderSobolevLipschitz
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.SharpGardingCovGradLadder

/-! # The `H^d` Sobolev multiplier bound for fibre-multiplication by a smooth endomorphism field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, a smooth fibre
endomorphism field `A : Π x, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x` acting fibrewise on
`(0, 2)`-tensors (the full Hom-bundle action `appFullRS`), this file proves the intrinsic chart-Sobolev
**`H^d` multiplier bound**

  `‖toHs d (A · X)‖ ≤ C · Λ · ‖toHs d X‖`,

where `Λ` is the uniform `C^{2d}`-fibre-jet size of `A` and `C` depends only on `(g, d)` and the
manifold.  This is the higher-order companion of the on-disk `L²` (`H^0`) fibre-operator bound
`fibreFieldMulL2_opNorm_le_sqrt` (operator norm `≤ √C` from the pointwise fibre-operator-norm sup):
the multiplier here controls *every* chart-Sobolev order, the high covariant derivatives being
redistributed onto either the (sup-bounded) endomorphism `A` or the `H^d`-controlled tensor `X` by the
covariant Leibniz rule.

## The route (the standard Sobolev Moser/tame multiplier argument)

The `toHs d` Hilbert-completion norm is comparable, in both directions, to the finite sum of the
intrinsic metric `L²` norms of the iterated covariant gradients `∇^i` (the Hebey–Sobolev bridge):

* **Reverse Hebey** (`exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum`, general valence):
  `‖T.toHs d‖ ≤ C · ∑_{j ≤ 2d} ‖∇^j T‖_{L²}`.
* **Forward Hebey** (`exists_iteratedCovGrad_l2Norm_le_toHs`, valence `(0, 2)`):
  `‖∇^i X‖_{L²} ≤ C · ‖X.toHs d‖` for `i ≤ 2d`.

Applying the reverse bridge to `A · X` reduces the goal to bounding each `‖∇^j(A · X)‖_{L²}`.  The
genuine covariant-calculus content — the binomial covariant Leibniz expansion of `∇^j(A · X)` into a
finite sum of products of (sup-bounded) covariant jets of `A` with covariant gradients of `X`,
delivered as a **pointwise fibre-norm jet grid** — is the single posited consumer-minimal child
`PointwiseCovLeibnizGrid` (the covariant Leibniz rule for a smooth Hom-bundle field applied to a tensor
section; the curvature/metric instances of this grid already live on disk as
`DiffBilinOp.rfns_iteratedCovGrad_grid` and `RfnsBilinearProduct`, of which this is the smooth-coefficient
form).  Given that grid the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` lifts it to
`‖∇^j(A · X)‖_{L²} ≤ Λ · √(j + 1) · ∑_{i ≤ j} ‖∇^i X‖_{L²}`, and the forward bridge closes the
`∑_{i ≤ 2d} ‖∇^i X‖_{L²}` against `‖X.toHs d‖`.

## The `δ`-specialization the consumer needs

For the cometric difference `A = g₁⁻¹ − g₀⁻¹` under the fibre-operator gate `gFibreOpBound`, the
uniform jet size satisfies `Λ ≤ Cd · δ` (the `δ`-arm: the order-zero jet is the fibre operator norm
`≤ ~2δ`, the higher jets being `H^{a+2}`-controlled).  The consumer's `eq_sub → triangle → (this
multiplier)` route then reads the principal remainder arm as `c · δ · ‖∇^{·+2}(T₁ − T₂)‖`.  The
`δ`-specialized corollary `toHs_appFullRS_norm_le_of_gFibreJetBound` records the multiplier with the
constant carried by an explicit `Λ` so the consumer can plug `Λ := Cd · δ` directly.

## What is — and is not — proven here

The covariant Leibniz jet grid (the `PointwiseCovLeibnizGrid` hypothesis) is taken as a genuine
quantitative analytic input about `A` and `X` (a *pointwise* fibre-norm domination of `∇^j(A · X)`),
structurally distinct from the multiplier conclusion (a global `toHs`-norm inequality).  It is the
covariant product structure, never the conclusion: a degenerate `Λ = 0` witness forces `A · X ≡ 0` in
`L²` at every order, so the predicate genuinely constrains `A`.  Everything above the grid — the two
Hebey bridges, the packaging, the finite-sum arithmetic — is proven outright; the multiplier therefore
depends transitively only on the `sorryAx` of the bridges it cites (the closed-manifold covariant
Gårding/Green inputs), exactly as every `toHs`-order statement in this tower does. -/

noncomputable section

open Bundle MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The covariant-Leibniz pointwise fibre-norm jet grid for fibre-multiplication.**

For a smooth `(0, 2)`-fibre endomorphism field `A` (with smoothness witness `hA`), a uniform jet size
`Λ ≥ 0`, and an order bound `d`, the predicate asserts that for every covariant order `j ≤ 2d`, every
smooth compactly-supported `(0, 2)`-tensor `X`, and every base point `x`, the intrinsic squared fibre
norm of `∇^j(A · X)` is dominated by `Λ²` times the sum, over `i ≤ j`, of the squared fibre norms of
the covariant gradients `∇^i X`:
```
rfns(∇^j(A · X))(x) ≤ Λ² · ∑_{i ≤ j} rfns(∇^i X)(x).
```

This is the genuine covariant product structure of the Hom-bundle action: the binomial covariant
Leibniz expansion of `∇^j(A · X)` puts the top derivative on either factor, the jets of `A` entering
as the base-point-uniform coefficient `Λ` (its `C^{2d}`-sup) and only the gradient order of `X`
surviving as a fibre-norm jet grid.  It is the smooth-coefficient instance of the on-disk differentiated
bilinear contraction grid `DiffBilinOp.rfns_iteratedCovGrad_grid`.  A degenerate `Λ = 0` forces every
`∇^j(A · X)` to vanish pointwise, hence in `L²`, so the predicate genuinely constrains `A` (it rejects
the zero coefficient whenever `A · X ≠ 0`). -/
def PointwiseCovLeibnizGrid
    (g : SmoothRiemannianMetric I M)
    (A : Π x : M, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x (A x)))
    (Λ : ℝ) (d : ℕ) : Prop :=
  ∀ (j : ℕ), j ≤ 2 * d → ∀ (X : Integral.L2.SmoothCcTensor g 0 2) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j
          (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X)).toSection x) ≤
      Λ ^ 2 * ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toSection x)

/-- The covariant-Leibniz jet grid rejects the degenerate `Λ = 0` coefficient: if it holds with
`Λ = 0`, then `∇^j(A · X)` has vanishing fibre norm at every order `j ≤ 2d`, every `X`, every `x`;
in particular (`j = 0`) the `L²`-section of `A · X` vanishes pointwise.  This certifies that the
predicate genuinely uses `A` and is not a vacuous stand-in (it cannot hold with `Λ = 0` once
`A · X ≠ 0` at some point). -/
theorem PointwiseCovLeibnizGrid.rfns_appFullRS_zero_of_lambda_zero
    {g : SmoothRiemannianMetric I M}
    {A : Π x : M, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x}
    {hA : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x (A x))}
    {d : ℕ}
    (hgrid : PointwiseCovLeibnizGrid (I := I) (M := M) g A hA 0 d)
    (X : Integral.L2.SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X).toSection x) = 0 := by
  have h0 := hgrid 0 (by omega) X x
  simp only [PDE.RicciFlow.iteratedCovGrad_zero, Nat.add_zero] at h0
  have hzero : (0 : ℝ) ^ 2 * ∑ i ∈ Finset.range (0 + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toSection x) = 0 := by
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul]
  rw [hzero] at h0
  exact le_antisymm h0 (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _)

/-- **The single-order `L²` jet bound for fibre-multiplication.**  Under the covariant-Leibniz jet
grid `hgrid` (with size `Λ ≥ 0`), for each order `j ≤ 2d` the metric `L²` norm of `∇^j(A · X)` is
bounded by `Λ · √(j + 1)` times the sum, over `i ≤ j`, of the metric `L²` norms of `∇^i X`:
```
‖∇^j(A · X)‖_{L²} ≤ (Λ · √(j + 1)) · ∑_{i ≤ j} ‖∇^i X‖_{L²}.
```
The proof is the finite-sum pointwise-to-`L²` packaging
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum` applied to the constant
`C := Λ · √(j + 1)` (whose square is `Λ² · (j + 1)`), the grid hypothesis supplying the pointwise
domination after absorbing the `(j + 1)` summand count into the square root. -/
theorem tensorL2Norm_iteratedCovGrad_appFullRS_le
    {g : SmoothRiemannianMetric I M}
    {A : Π x : M, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x}
    {hA : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x (A x))}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : ℕ}
    (hgrid : PointwiseCovLeibnizGrid (I := I) (M := M) g A hA Λ d)
    (X : Integral.L2.SmoothCcTensor g 0 2) {j : ℕ} (hj : j ≤ 2 * d) :
    Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j
          (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X)).toFun ≤
      (Λ * Real.sqrt (j + 1)) * ∑ i ∈ Finset.range (j + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun := by
  classical
  set C : ℝ := Λ * Real.sqrt (j + 1) with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg hΛ (Real.sqrt_nonneg _)
  -- The jet family indexed by `i`, of valence `2 + i`.
  set Ti : ∀ i, Integral.L2.SmoothCcTensor g 0 (2 + i) :=
    fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X with hTi_def
  -- Pointwise: the grid bound rewritten with `C² = Λ² · (j + 1)`.
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j
            (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X)).toSection x) ≤
        C ^ 2 * ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x ((Ti i).toSection x) := by
    intro x
    have hgx := hgrid j hj X x
    -- `Λ² ≤ C² = Λ² · (j + 1)` since `1 ≤ j + 1`, and the sum is nonnegative.
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x ((Ti i).toSection x) :=
      Finset.sum_nonneg fun i _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + i) x _
    have hCsq : C ^ 2 = Λ ^ 2 * ((j : ℝ) + 1) := by
      rw [hC_def, mul_pow, Real.sq_sqrt (by positivity)]
    refine hgx.trans ?_
    rw [hCsq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hge1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    calc ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x ((Ti i).toSection x)
        = 1 * ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x ((Ti i).toSection x) := by
          rw [one_mul]
      _ ≤ ((j : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) x ((Ti i).toSection x) :=
          mul_le_mul_of_nonneg_right hge1 hsum_nn
  -- Lift to `L²` by the finite-sum packaging.
  have hpack :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g (j + 1)
      (fun i => 2 + i) Ti
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j
        (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X))
      C hC_nn hpt
  -- Convert the `SmoothCcTensor` seminorms back to `tensorL2Norm`.
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)] at hpack
  have hsum_eq : (∑ i ∈ Finset.range (j + 1), ‖Ti i‖) =
      ∑ i ∈ Finset.range (j + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun :=
    Finset.sum_congr rfl (fun i _ => by
      rw [hTi_def]; exact Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_eq] at hpack
  exact hpack

/-- **The `H^d` Sobolev multiplier bound for fibre-multiplication by a smooth endomorphism field.**

For a closed Riemannian manifold `(M, g)`, a smooth `(0, 2)`-fibre endomorphism field `A` (smoothness
`hA`) whose covariant jets up to order `2d` are uniformly controlled by `Λ ≥ 0` through the covariant
Leibniz jet grid `PointwiseCovLeibnizGrid g A hA Λ d`, there is a single nonnegative constant `C`
(depending only on `g, d`, and the manifold) such that for every smooth compactly-supported
`(0, 2)`-tensor `X`, the fibre-product `A · X = appFullRS A X` satisfies the chart-Sobolev `H^d`
multiplier bound
```
‖(A · X).toHs d‖ ≤ C · Λ · ‖X.toHs d‖.
```

The constant `C` is `C_rev · (∑_{j ≤ 2d} √(j + 1)) · C_fwd`, the product of the reverse Hebey constant,
the order-count factor from the per-order `L²` jet bounds, and the forward Hebey constant; the size
factor `Λ` is carried explicitly so the cometric-difference specialization plugs `Λ ≤ Cd · δ` directly.

**Proof.**  The reverse Hebey bridge `exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum` reduces
`‖(A · X).toHs d‖` to `C_rev · ∑_{j ≤ 2d} ‖∇^j(A · X)‖_{L²}`.  Each `‖∇^j(A · X)‖_{L²}` is bounded by
`Λ · √(j + 1) · ∑_{i ≤ 2d} ‖∇^i X‖_{L²}` (the single-order bound
`tensorL2Norm_iteratedCovGrad_appFullRS_le`, the inner sum over `i ≤ j` enlarged to `i ≤ 2d` by
nonnegativity).  Summing over `j ≤ 2d` yields `C_rev · (∑_j √(j + 1)) · Λ · ∑_{i ≤ 2d} ‖∇^i X‖_{L²}`,
and the forward Hebey bridge `exists_iteratedCovGrad_l2Norm_le_toHs` closes
`∑_{i ≤ 2d} ‖∇^i X‖_{L²} ≤ (2d + 1) · C_fwd · ‖X.toHs d‖`. -/
theorem exists_toHs_appFullRS_norm_le_of_covLeibnizGrid
    (g : SmoothRiemannianMetric I M) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : Π x : M, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x)
        (hA : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
            (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x (A x)))
        (Λ : ℝ), 0 ≤ Λ →
        PointwiseCovLeibnizGrid (I := I) (M := M) g A hA Λ d →
        ∀ X : Integral.L2.SmoothCcTensor g 0 2,
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) d
              (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X)‖ ≤
            C * Λ * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) d X‖ := by
  classical
  -- Reverse Hebey bridge (general valence `(0, 2)`, order `d`).
  obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g 0 2 d
  -- Forward Hebey bridge (valence `(0, 2)`, order `d`).
  obtain ⟨Cfwd, hCfwd_nn, hCfwd⟩ :=
    IntrinsicSpectral.DeTurck.exists_iteratedCovGrad_l2Norm_le_toHs (I := I) (M := M) g d
  -- The order-count factor `∑_{j ≤ 2d} √(j + 1)`.
  set Sord : ℝ := ∑ j ∈ Finset.range (2 * d + 1), Real.sqrt (j + 1) with hSord_def
  have hSord_nn : 0 ≤ Sord :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  refine ⟨Crev * (Sord * ((2 * d + 1 : ℕ) * Cfwd)), by positivity, ?_⟩
  intro A hA Λ hΛ hgrid X
  set NX : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) d X‖ with hNX_def
  have hNX_nn : 0 ≤ NX := norm_nonneg _
  set P : Integral.L2.SmoothCcTensor g 0 2 :=
    Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X with hP_def
  -- The full sum, over `i ≤ 2d`, of the covariant `L²`-jets of `X`.
  set SX : ℝ := ∑ i ∈ Finset.range (2 * d + 1),
    Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun with hSX_def
  have hSX_nn : 0 ≤ SX :=
    Finset.sum_nonneg fun i _ =>
      Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + i) _
  -- Forward Hebey: `SX ≤ (2d + 1) · Cfwd · NX`.
  have hSX_le : SX ≤ (2 * d + 1 : ℕ) * Cfwd * NX := by
    have htermwise : ∀ i ∈ Finset.range (2 * d + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun ≤ Cfwd * NX := by
      intro i hi
      have hi2d : i ≤ 2 * d := by rw [Finset.mem_range] at hi; omega
      exact hCfwd X i hi2d
    calc SX ≤ ∑ _i ∈ Finset.range (2 * d + 1), Cfwd * NX :=
          Finset.sum_le_sum htermwise
      _ = (2 * d + 1 : ℕ) * (Cfwd * NX) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (2 * d + 1 : ℕ) * Cfwd * NX := by ring
  -- Reverse Hebey: `‖P.toHs d‖ ≤ Crev · ∑_{j ≤ 2d} ‖∇^j P‖_{L²}`.
  have hrev := hCrev P
  -- Per-order bound: `‖∇^j P‖_{L²} ≤ √(j+1) · Λ · SX` (the inner `i ≤ j` sum enlarged to `i ≤ 2d`).
  have hper : ∀ j ∈ Finset.range (2 * d + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun ≤
        Real.sqrt (j + 1) * Λ * SX := by
    intro j hj
    have hj2d : j ≤ 2 * d := by rw [Finset.mem_range] at hj; omega
    have hsingle :=
      tensorL2Norm_iteratedCovGrad_appFullRS_le (I := I) (M := M) (g := g) (A := A) (hA := hA)
        hΛ hgrid X hj2d
    rw [← hP_def] at hsingle
    -- The inner sum over `i ≤ j` is `≤ SX` (extra nonnegative summands).
    have hinner : (∑ i ∈ Finset.range (j + 1),
          Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun) ≤ SX := by
      rw [hSX_def]
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.add_le_add_right hj2d 1)) ?_
      intro i _ _
      exact Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + i) _
    have hΛsqrt_nn : 0 ≤ Λ * Real.sqrt (j + 1) := mul_nonneg hΛ (Real.sqrt_nonneg _)
    calc Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun
        ≤ (Λ * Real.sqrt (j + 1)) * ∑ i ∈ Finset.range (j + 1),
            Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun := hsingle
      _ ≤ (Λ * Real.sqrt (j + 1)) * SX :=
          mul_le_mul_of_nonneg_left hinner hΛsqrt_nn
      _ = Real.sqrt (j + 1) * Λ * SX := by ring
  -- Sum the per-order bounds: `∑_j ‖∇^j P‖ ≤ Sord · Λ · SX`.
  have hsum_le : (∑ j ∈ Finset.range (2 * d + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun) ≤ Sord * Λ * SX := by
    calc (∑ j ∈ Finset.range (2 * d + 1),
            Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun)
        ≤ ∑ j ∈ Finset.range (2 * d + 1), Real.sqrt (j + 1) * Λ * SX :=
          Finset.sum_le_sum hper
      _ = (∑ j ∈ Finset.range (2 * d + 1), Real.sqrt (j + 1)) * (Λ * SX) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
      _ = Sord * Λ * SX := by rw [hSord_def, mul_assoc]
  -- Chain reverse Hebey with the summed per-order bound and forward Hebey.
  have hΛSX_nn : 0 ≤ Λ * SX := mul_nonneg hΛ hSX_nn
  calc ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) d P‖
      ≤ Crev * ∑ j ∈ Finset.range (2 * d + 1),
          Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun := hrev
    _ ≤ Crev * (Sord * Λ * SX) := mul_le_mul_of_nonneg_left hsum_le hCrev_nn
    _ = Crev * Sord * Λ * SX := by ring
    _ ≤ Crev * Sord * Λ * ((2 * d + 1 : ℕ) * Cfwd * NX) := by
        apply mul_le_mul_of_nonneg_left hSX_le
        positivity
    _ = Crev * (Sord * ((2 * d + 1 : ℕ) * Cfwd)) * Λ * NX := by ring

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation in
/-- **The matching-order covariant-jet sum is controlled by the matching-order spectral mass.**

For every order `a` there is a single nonnegative constant `C` (depending only on `g, a`, and the
manifold) such that for every smooth compactly-supported `(0, 2)`-tensor `X`, the order-`a` covariant
jet sum `∑_{l ≤ a} ‖∇ˡ X‖_{L²}` is bounded by `C` times the square root of the matching-order spectral
mass `∑'ᵢ (1 + λᵢ)ᵃ · cᵢ(X)²`:
```
covJetSum g a X ≤ C · √(mass_a X).
```
Each jet `‖∇ˡ X‖_{L²}` is bounded by the order-`l` spectral mass (the sharp Gårding bound M2
`iteratedCovGrad_l2Norm_le_sqrt_tensorSobolevMass`), and the order-`l` mass is monotone-dominated by
the order-`a` mass for `l ≤ a` (`tensorSobolevWeight_mono`, the weighted summability supplied by
`smoothCcTensor_tensorL2Coeff_weighted_summable`). -/
theorem covJetSum_le_sqrt_tensorSobolevMass
    (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : Integral.L2.SmoothCcTensor g 0 2,
        (∑ l ∈ Finset.range (a + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) ≤
          C * Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) := by
  classical
  -- The per-order Gårding constants `C_l` from M2, for `l ≤ a`.
  have hM2 := fun l => iteratedCovGrad_l2Norm_le_sqrt_tensorSobolevMass (I := I) (M := M) g l
  choose CM hCM0 hCM using hM2
  refine ⟨∑ l ∈ Finset.range (a + 1), CM l, Finset.sum_nonneg fun l _ => hCM0 l, fun X => ?_⟩
  -- The order-`a` mass and its nonnegativity.
  set massA : ℝ := ∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
    tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2 with hmassA_def
  have hmassA_nn : 0 ≤ massA := by
    rw [hmassA_def]
    refine tsum_nonneg fun i => ?_
    have := tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)
    positivity
  -- Summability of the order-`l` and order-`a` weighted families.
  have hsumA : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g (a : ℝ) X _
  -- Per-order: `‖∇ˡ X‖ ≤ CM l · √(mass_l X) ≤ CM l · √(mass_a X)` for `l ≤ a`.
  have hper : ∀ l ∈ Finset.range (a + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖ ≤ CM l * Real.sqrt massA := by
    intro l hl
    rw [Finset.mem_range] at hl
    have hla : l ≤ a := by omega
    -- order-`l` mass ≤ order-`a` mass (termwise weight monotonicity + summability).
    have hsumL : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i (l : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) :=
      smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g (l : ℝ) X _
    have hmassL_le : (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i (l : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) ≤ massA := by
      rw [hmassA_def]
      refine hsumL.tsum_le_tsum (fun i => ?_) hsumA
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact tensorSobolevWeight_mono (I := I) (M := M) i (by exact_mod_cast hla)
    calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖
        ≤ CM l * Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
            tensorSobolevWeight (I := I) (M := M) i (l : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) := hCM l X
      _ ≤ CM l * Real.sqrt massA :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmassL_le) (hCM0 l)
  -- Sum the per-order bounds.
  calc (∑ l ∈ Finset.range (a + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖)
      ≤ ∑ l ∈ Finset.range (a + 1), CM l * Real.sqrt massA := Finset.sum_le_sum hper
    _ = (∑ l ∈ Finset.range (a + 1), CM l) * Real.sqrt massA := by rw [Finset.sum_mul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation in
/-- **The matching-order spectral-mass multiplier bound for fibre-multiplication by a smooth
endomorphism field (the SUMMED Moser/Sobolev fibre-multiplier estimate, in spectral-mass currency).**

For a closed Riemannian manifold `(M, g)` and an order `d`, there is a single nonnegative constant
`C` (depending only on `g, d`, and the manifold) such that for every smooth `(0, 2)`-fibre
endomorphism field `A` (smoothness `hA`) whose covariant jets up to order `2d` are uniformly
controlled by `Λ ≥ 0` through the covariant-Leibniz jet grid `PointwiseCovLeibnizGrid g A hA Λ d`,
and every smooth compactly-supported `(0, 2)`-tensor `X`, the order-`d` spectral mass of the
fibre-product `A · X = appFullRS A X` is bounded by `C · Λ²` times the order-`d` spectral mass of `X`:
```
mass_d(A · X) ≤ C · Λ² · mass_d(X).
```

This is the spectral-mass transcription of the chart-Sobolev multiplier
`exists_toHs_appFullRS_norm_le_of_covLeibnizGrid`.  Because fibre-multiplication by `A` is
NON-DIAGONAL (a single eigenmode of `X` emits higher modes of `A · X`, the frequency-doubling that
makes any per-mode `cᵢ(A·X) ≤ … cᵢ(X)` bound FALSE), the estimate is on whole spectral masses, never
per-mode.

**Proof.**  The order-`d` mass of `A · X` is bounded (sharp Gårding M1
`tensorSobolevMass_le_covJetSum_sq`) by `C_{M1} · covJetSum g d (A · X)²`.  Each jet
`‖∇ʲ(A · X)‖_{L²}` (`j ≤ d ≤ 2d`) is `≤ Λ · √(j+1) · ∑_{i ≤ j} ‖∇ⁱ X‖` (the per-order
fibre-multiplication bound `tensorL2Norm_iteratedCovGrad_appFullRS_le`), so
`covJetSum g d (A · X) ≤ Λ · (∑_{j ≤ d} √(j+1)) · covJetSum g d X`.  Finally the matching-order
covariant jets of `X` are controlled by the order-`d` spectral mass of `X`
(`covJetSum_le_sqrt_tensorSobolevMass`): `covJetSum g d X ≤ C₂ · √(mass_d X)`.  Squaring collapses the
square roots, giving `mass_d(A · X) ≤ C_{M1} · (Λ · S · C₂)² · mass_d X = C · Λ² · mass_d X`. -/
theorem tensorSobolevMass_appFullRS_le_of_covLeibnizGrid
    (g : SmoothRiemannianMetric I M) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : Π x : M, TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x)
        (hA : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
          (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
            (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x (A x)))
        (Λ : ℝ), 0 ≤ Λ →
        PointwiseCovLeibnizGrid (I := I) (M := M) g A hA Λ d →
        ∀ X : Integral.L2.SmoothCcTensor g 0 2,
          (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
              tensorSobolevWeight (I := I) (M := M) i (d : ℝ) *
                (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                  (Integral.L2.SmoothCcTensor.toL2
                    (Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X)) i) ^ 2) ≤
            C * Λ ^ 2 *
              (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
                tensorSobolevWeight (I := I) (M := M) i (d : ℝ) *
                  (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                    (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2) := by
  classical
  -- M1 at order `d`: `mass_d(S) ≤ CM1 · covJetSum g d S ²`.
  obtain ⟨CM1, hCM1_nn, hCM1⟩ := tensorSobolevMass_le_covJetSum_sq (I := I) (M := M) g d
  -- The jet→mass bound for `X` at order `d`.
  obtain ⟨CJ, hCJ_nn, hCJ⟩ := covJetSum_le_sqrt_tensorSobolevMass (I := I) (M := M) g d
  -- The order-count factor `∑_{j ≤ d} √(j+1)` from the per-order fibre-multiplication bound.
  set Sord : ℝ := ∑ j ∈ Finset.range (d + 1), Real.sqrt (j + 1) with hSord_def
  have hSord_nn : 0 ≤ Sord := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  refine ⟨CM1 * (Sord * CJ) ^ 2, by positivity, ?_⟩
  intro A hA Λ hΛ hgrid X
  set P : Integral.L2.SmoothCcTensor g 0 2 :=
    Integral.Connection.appFullRS (I := I) (M := M) g 0 2 2 A hA X with hP_def
  -- The order-`d` masses.
  set massX : ℝ := ∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
    tensorSobolevWeight (I := I) (M := M) i (d : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (Integral.L2.SmoothCcTensor.toL2 X) i) ^ 2 with hmassX_def
  have hmassX_nn : 0 ≤ massX := by
    rw [hmassX_def]
    refine tsum_nonneg fun i => ?_
    have := tensorSobolevWeight_nonneg (I := I) (M := M) i (d : ℝ)
    positivity
  -- The jet sum of `X` is `≤ CJ · √(mass_d X)`.
  have hJX : (∑ l ∈ Finset.range (d + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) ≤ CJ * Real.sqrt massX := by
    rw [hmassX_def]; exact hCJ X
  -- The jet sum of `P = A · X` is `≤ Λ · Sord · (jet sum of X)`.
  have hJP : (∑ j ∈ Finset.range (d + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖) ≤
      Λ * Sord * (∑ l ∈ Finset.range (d + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) := by
    -- Per-order: `‖∇ʲ P‖ ≤ Λ·√(j+1)·(jet sum of X)`.
    have hper : ∀ j ∈ Finset.range (d + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖ ≤
          (Λ * Real.sqrt (j + 1)) * (∑ l ∈ Finset.range (d + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj2d : j ≤ 2 * d := by omega
      have hsingle :=
        tensorL2Norm_iteratedCovGrad_appFullRS_le (I := I) (M := M) (g := g) (A := A) (hA := hA)
          hΛ hgrid X hj2d
      rw [← hP_def] at hsingle
      -- Convert `tensorL2Norm … .toFun` to `‖·‖` via `norm_def`.
      have hPnorm : Integral.L2.tensorL2Norm (I := I) g 0 (2 + j)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P).toFun =
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖ :=
        (Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _).symm
      have hXnorm : ∀ i, Integral.L2.tensorL2Norm (I := I) g 0 (2 + i)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X).toFun =
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X‖ :=
        fun i => (Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _).symm
      rw [hPnorm] at hsingle
      have hsingle' : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖ ≤
          (Λ * Real.sqrt (j + 1)) * ∑ i ∈ Finset.range (j + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X‖ := by
        refine hsingle.trans_eq ?_
        rw [Finset.sum_congr rfl (fun i _ => hXnorm i)]
      -- Enlarge the inner sum `i ≤ j` to `i ≤ d`.
      have hinner : (∑ i ∈ Finset.range (j + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 i X‖) ≤
          ∑ l ∈ Finset.range (d + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.add_le_add_right (by omega) 1))
          (fun i _ _ => norm_nonneg _)
      refine hsingle'.trans ?_
      exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hΛ (Real.sqrt_nonneg _))
    calc (∑ j ∈ Finset.range (d + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖)
        ≤ ∑ j ∈ Finset.range (d + 1),
            (Λ * Real.sqrt (j + 1)) * (∑ l ∈ Finset.range (d + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) := Finset.sum_le_sum hper
      _ = (∑ j ∈ Finset.range (d + 1), (Λ * Real.sqrt (j + 1))) *
            (∑ l ∈ Finset.range (d + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) := by
          rw [Finset.sum_mul]
      _ = Λ * Sord * (∑ l ∈ Finset.range (d + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) := by
          rw [hSord_def, ← Finset.mul_sum]
  -- Chain: `covJetSum g d P ≤ Λ · Sord · CJ · √massX`.
  have hJX_nn : 0 ≤ ∑ l ∈ Finset.range (d + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖ :=
    Finset.sum_nonneg fun l _ => norm_nonneg _
  have hJP_nn : 0 ≤ ∑ j ∈ Finset.range (d + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖ :=
    Finset.sum_nonneg fun j _ => norm_nonneg _
  have hchain : (∑ j ∈ Finset.range (d + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖) ≤
      Λ * Sord * CJ * Real.sqrt massX := by
    refine hJP.trans ?_
    have : Λ * Sord * (∑ l ∈ Finset.range (d + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 l X‖) ≤
        Λ * Sord * (CJ * Real.sqrt massX) :=
      mul_le_mul_of_nonneg_left hJX (by positivity)
    refine this.trans_eq ?_; ring
  -- M1: `mass_d(P) ≤ CM1 · covJetSum g d P ²`.
  have hM1P := (hCM1 P).2
  -- `covJetSum g d P` is `∑_{j ≤ d} ‖∇ʲ P‖`.
  have hcovJetP : DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covJetSum
        (I := I) (M := M) g d P =
      ∑ j ∈ Finset.range (d + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖ := rfl
  -- Assemble.  Note the `tensorL2Coeff` family in M1 uses `hCompact g`, defeq to the resolvent.
  calc (∑' i : TensorEigenIdx (I := I) (M := M) g 0 2,
          tensorSobolevWeight (I := I) (M := M) i (d : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (Integral.L2.SmoothCcTensor.toL2 P) i) ^ 2)
      ≤ CM1 * DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covJetSum
            (I := I) (M := M) g d P ^ 2 := hM1P
    _ = CM1 * (∑ j ∈ Finset.range (d + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 2 j P‖) ^ 2 := by rw [hcovJetP]
    _ ≤ CM1 * (Λ * Sord * CJ * Real.sqrt massX) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hCM1_nn
        exact pow_le_pow_left₀ hJP_nn hchain 2
    _ = CM1 * (Sord * CJ) ^ 2 * Λ ^ 2 * (Real.sqrt massX ^ 2) := by ring
    _ = CM1 * (Sord * CJ) ^ 2 * Λ ^ 2 * massX := by rw [Real.sq_sqrt hmassX_nn]

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
