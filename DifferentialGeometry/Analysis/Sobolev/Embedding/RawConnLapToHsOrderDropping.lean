import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset

/-! # Order-dropping completion-norm bounds for the rough tensor connection Laplacian

This file ships the intrinsic chart-Sobolev (`SmoothCcTensor.toHs`) boundedness of the rough
tensor connection Laplacian `Δ_∇ = rawTensorConnLapSmooth`, in the **easy** (differentiation)
direction needed by the order-`a` chart-RHS spectral tower.

The rough Laplacian is the frame trace of the second covariant derivative
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single* second-order operator: it
maps `H^{2(k+1)} → H^{2k}` boundedly, losing exactly **one** `toHs`-order (`= 2` derivatives),
not two.  This is the genuine atomic elliptic-boundedness primitive
`exists_rawConnLapSmooth_toHs_le_toHs_succ` (the order-`k` analogue of the on-disk `L²`/`H¹`
instance `rawTensorConnLapIter_intrinsicL2_le_tensorPouSobolevNorm_sq_one`, which is the `k = 0`
case in `∫⁻`-form): its body is `sorry` — the tight single-step `H^σ(Δ_∇ T) ≤ C · H^{σ+1}(T)`
bound, with no curvature commutator / Gårding regularity (no `Order2GardingFamily`, no
`CommutatorDefectBound`).  It is the rough-Laplacian counterpart of the covariant-derivative
order-dropping bound `covGrad_toHs_norm_le` — but tight at `+1` `toHs`-order, since `Δ_∇` is a
single second-order operator whereas a naive `covGrad ∘ covGrad` composition would charge `+2`.

Iterating it (`exists_rawConnLapIter_toHs_le_toHs`) gives the all-order iterated bound
`H^k(Δ_∇^i T) ≤ C · H^{k+i}(T)`, the mirror of `iteratedCovGrad_toHs_norm_le`.

The companion primitive `exists_l2Norm_le_toHs_zero` records the reverse of the on-disk
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`: the global metric `L²` norm of a smooth
compactly-supported section is controlled by its order-`0` partition-of-unity chart-Sobolev
norm (the partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up
to the bounded metric-density factor on the compact manifold).  Its body is `sorry`: it is the
genuine atomic `L² ≤ C · H⁰_chart` comparison, with no differentiation content. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The tight single-step order-dropping `ℝ≥0∞` chart-Sobolev norm bound for the rough
connection Laplacian (the genuine analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
tensorPouSobolevHsNorm g k (Δ_∇ T) ≤ ENNReal.ofReal C · tensorPouSobolevHsNorm g (k + 1) T ,
```
where `Δ_∇ = rawTensorConnLapSmooth g r s`.  This is the `ℝ≥0∞`-level (`tensorPouSobolevHsNorm`)
form of the tight single-step bound: the rough Laplacian is the frame trace of the second
covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a single
second-order operator `H^{2(k+1)} → H^{2k}`, losing exactly **one** `toHs`-order.  It is the
rough-Laplacian counterpart of `exists_covGrad_tensorPouSobolevHsNorm_le`, tight at `+1` order.

Its body is `sorry`: it is the genuine analytic single-step rough-Laplacian chart-Sobolev
order-dropping estimate (the elliptic boundedness of the second-order operator `Δ_∇`), with no
spectral nonlinearity and no Weyl dependence.  The completion-norm forms
`exists_rawConnLapSmooth_toHs_le_toHs_succ` and `exists_rawConnLapIter_toHs_le_toHs` are proved on
top of it via `tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g k
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          ENNReal.ofReal C *
            tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T :=
  sorry

/-- **The tight single-step order-dropping completion-norm bound for the rough connection
Laplacian (the genuine atomic elliptic-boundedness primitive).**

For a closed Riemannian manifold and an order `k`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇ T).toHs k‖ ≤ C · ‖T.toHs (k + 1)‖ ,
```
where `Δ_∇ = rawTensorConnLapSmooth g 0 2`.  This is the intrinsic `H^{2k}(Δ_∇ T) ≤
C · H^{2(k+1)}(T)` order-dropping inequality: the rough Laplacian is the frame trace of the
second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single*
second-order operator, so it loses exactly **one** `toHs`-order (`= 2` derivatives) — the tight
count, as opposed to the `+2` a naive `covGrad ∘ covGrad` composition would charge.  It is proved
on top of the `ℝ≥0∞`-level primitive `exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le` via
`tensorPouSobolevHilbert_norm_eq`, exactly as `covGrad_toHs_norm_le` is built from
`exists_covGrad_tensorPouSobolevHsNorm_le`. -/
theorem exists_rawConnLapSmooth_toHs_le_toHs_succ
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le (I := I) (M := M) g 0 2 k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  have hle := hC T
  have h_rhs_ne_top :
      ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (k + 1) T).ne
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (rawTensorConnLapSmooth (I := I) g 0 2 T)).toReal
      ≤ (ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal :=
        ENNReal.toReal_mono h_rhs_ne_top hle
    _ = (ENNReal.ofReal C).toReal *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_mul]
    _ = C * (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_ofReal hC_nn]

/-- **The iterated order-dropping completion-norm bound for the rough connection Laplacian.**

For each iteration count `i` and each order `k` there is a non-negative constant `C` such that
for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇^i T).toHs k‖ ≤ C · ‖T.toHs (k + i)‖ ,
```
where `Δ_∇^i = rawTensorConnLapIter g 0 2 i`.  The proof iterates the tight single-step bound
`exists_rawConnLapSmooth_toHs_le_toHs_succ` exactly `i` times (peeling one `Δ_∇` at each step
and raising the inner order by one), the constant being the product of the single-step
constants.  This is the rough-Laplacian mirror of `iteratedCovGrad_toHs_norm_le`. -/
theorem exists_rawConnLapIter_toHs_le_toHs
    (g : SmoothRiemannianMetric I M) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + i) T‖ := by
  induction i generalizing k with
  | zero =>
      refine ⟨1, zero_le_one, fun T => ?_⟩
      simp only [rawTensorConnLapIter_zero, Nat.add_zero, one_mul, le_refl]
  | succ i ih =>
      obtain ⟨Ci, hCi_nn, hCi⟩ := ih (k + 1)
      obtain ⟨C1, hC1_nn, hC1⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g k
      refine ⟨C1 * Ci, mul_nonneg hC1_nn hCi_nn, fun T => ?_⟩
      -- One peel: `Δ_∇^{i+1} T = Δ_∇ (Δ_∇^i T)`, then single-step at order `k` and `ih` at
      -- order `k+1`.
      have hpeel : rawTensorConnLapIter (I := I) g 0 2 (i + 1) T
          = rawTensorConnLapSmooth (I := I) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i T) := by
        rw [rawTensorConnLapIter_succ]
      rw [hpeel]
      have hstep := hC1 (rawTensorConnLapIter (I := I) g 0 2 i T)
      have hih := hCi T
      have hord : k + 1 + i = k + (i + 1) := by ring
      rw [hord] at hih
      refine le_trans hstep ?_
      calc C1 * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1)
              (rawTensorConnLapIter (I := I) g 0 2 i T)‖
          ≤ C1 * (Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖) := mul_le_mul_of_nonneg_left hih hC1_nn
        _ = C1 * Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖ := by ring

/-- **Monotonicity of the order-`k` chart-Sobolev completion norm in the order `k`.**

For `m ≤ n`, the order-`m` chart-Sobolev (`toHs`) norm is dominated by the order-`n` one:
`‖T.toHs m‖ ≤ ‖T.toHs n‖`.  This is the completion-norm reflection of the monotonicity
`tensorPouSobolevHsNorm_le_succ` of the partition-of-unity chart-Sobolev `ℝ≥0∞`-norm in the
order, transported through `tensorPouSobolevHilbert_norm_eq`. -/
theorem toHs_norm_mono (g : SmoothRiemannianMetric I M) {r s : ℕ} {m n : ℕ} (hmn : m ≤ n)
    (T : Integral.L2.SmoothCcTensor g r s) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) m T‖ ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) n T‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g n T).ne ?_
  -- Monotone in the order via the successor step, by induction on the gap `n - m`.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simp
  | succ d ihd =>
      refine le_trans ihd ?_
      have : m + d + 1 = m + (d + 1) := by ring
      rw [← this]
      exact tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g (m + d) T

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` is additive:
`(R₁ + R₂).toHs k = R₁.toHs k + R₂.toHs k`.  Both sides are the completion coercion of the
`SmoothCcTensorHs`-wrapper addition (`UniformSpace.Completion.coe_add`). -/
theorem SmoothCcTensor.toHs_add {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ + R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        + IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_add]
  rfl

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` commutes with
subtraction: `(R₁ − R₂).toHs k = R₁.toHs k − R₂.toHs k` (`UniformSpace.Completion.coe_sub`). -/
theorem SmoothCcTensor.toHs_sub {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ - R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        - IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_sub]
  rfl

section LinearityT2

open DifferentialGeometry.Integral.Connection Bundle Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The unconditional smoothness witness of the total-space form of `rawTensorConnLap` applied to a
bundled smooth section `T : SmoothCcTensor g r s`. -/
private lemma rawConnLap_smooth_witness (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : Integral.L2.SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => Bundle.TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)) :=
  rawTensorConnLap_contMDiff (I := I) g r s
    (fun z : M => T.toSection z) T.toSection.contMDiff_toFun

/-- **Subtraction-linearity of the bundled rough connection Laplacian on `SmoothCcTensor`
(an atomic algebraic linearity primitive).**

`Δ_∇ (T − T') = Δ_∇ T − Δ_∇ T'`, where `Δ_∇ = rawTensorConnLapSmooth g r s`.  The rough
Laplacian is the section-level packaging of the fibrewise-linear pointwise operator
`rawTensorConnLap`, which is additive (`tensorConnLaplacian_of_contMDiff_add`) and `smul`-linear
(`tensorConnLaplacian_of_contMDiff_smul`); hence so is its bundled form.  Writing
`T − T' = T + (-1) • T'` and reducing by `SmoothCcTensor.ext`/`ContMDiffSection.ext` to the
pointwise `.toSection`, the bundled additivity and scalar-homogeneity (mirroring the on-disk
`connLaplacianL2Action.map_add'`/`map_smul'`) assemble the subtraction identity.  This splits off
the linear part of the second-order DeTurck right-hand side. -/
theorem rawTensorConnLapSmooth_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : Integral.L2.SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (T - T')
      = rawTensorConnLapSmooth (I := I) g r s T - rawTensorConnLapSmooth (I := I) g r s T' := by
  have hsub_eq : (T - T' : Integral.L2.SmoothCcTensor g r s) = T + (-1 : ℝ) • T' := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  have h_smul : rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')
      = (-1 : ℝ) • rawTensorConnLapSmooth (I := I) g r s T' := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsmul := tensorConnLaplacian_of_contMDiff_smul (I := I) g r s (-1 : ℝ) T'
      (rawConnLap_smooth_witness (I := I) g T')
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    have hRHS : (rawTensorConnLapSmooth (I := I) g r s T').toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          (rawConnLap_smooth_witness (I := I) g T')).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, hRHS, hsmul]
  have h_add : rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')
      = rawTensorConnLapSmooth (I := I) g r s T
        + rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T') := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsum := tensorConnLaplacian_of_contMDiff_add (I := I) g r s T ((-1 : ℝ) • T')
      (rawConnLap_smooth_witness (I := I) g T)
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))
      (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + (-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T'))).toSection x := rfl
    have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T
          (rawConnLap_smooth_witness (I := I) g T)).toSection x := rfl
    have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply, hRHS₁, hRHS₂, hsum]
  rw [hsub_eq, h_add, h_smul, neg_one_smul, ← sub_eq_add_neg]

end LinearityT2

/-- **The reverse order-`0` partition-of-unity completeness comparison (the genuine analytic
primitive).**

For a closed Riemannian manifold and ranks `(r, s)` there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
‖T‖ ≤ C · (tensorPouSobolevHsNorm g 0 T).toReal ,
```
where `‖T‖ = tensorL2Norm g r s T.toFun` is the global metric `L²` (semi-)norm.  This is the
reverse (lower) partition-of-unity completeness bound: the partition of unity sums to one, so the
chart-`H⁰` norm recovers the full metric `L²` norm up to the bounded metric-density factor on the
compact manifold.  It is the exact reverse of the on-disk forward comparison
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`, and is precisely the seminorm hypothesis `h_norm_le`
left open by `TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv`.

Its body is `sorry`: it is the genuine atomic `L² ≤ C · H⁰_chart` lower comparison, with no
differentiation content, no spectral nonlinearity, and no Weyl dependence.  The completion-norm
form `exists_l2Norm_le_toHs_zero` is proved on top of it. -/
theorem exists_l2Norm_le_tensorPouSobolevHsNorm_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        ‖T‖ ≤ C * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal :=
  sorry

/-- **The reverse order-`0` comparison: the global metric `L²` norm is controlled by the
order-`0` partition-of-unity chart-Sobolev completion norm (the genuine atomic comparison
primitive).**

For a closed Riemannian manifold there is a non-negative constant `C` such that for every smooth
compactly-supported `(0, 2)`-tensor section `T`,
```
‖T.toL2‖ ≤ C · ‖T.toHs 0‖ .
```
`‖T.toL2‖ = ‖T‖` is the global metric `L²` (semi-)norm (`norm_toL2`) and `‖T.toHs 0‖` is the
order-`0` partition-of-unity chart-Sobolev completion norm.  This is the reverse of the on-disk
forward comparison `tensorPouSobolevHsNorm_zero_le_tensorL2Norm` (`H⁰_chart ≤ C · L²`): the
partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up to the
metric-density factor, bounded on the compact manifold.  It is proved on top of the underlying
seminorm primitive `exists_l2Norm_le_tensorPouSobolevHsNorm_zero` via `norm_toL2` and
`tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_l2Norm_le_toHs_zero
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) T‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0 T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_l2Norm_le_tensorPouSobolevHsNorm_zero (I := I) (M := M) g 0 2
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [Integral.L2.SmoothCcTensor.norm_toL2, tensorPouSobolevHilbert_norm_eq]
  exact hC T

end DifferentialGeometry.PDE.RicciFlow
