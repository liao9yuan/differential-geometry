import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceParallelContraction
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-! # The pointwise full-window product grid of the cometric quadratic-trace product

The intrinsic squared fibre norm of the order-`p` covariant gradient of the **twice-applied cometric
double trace** (`(0, 6) → (0, 4) → (0, 2)`) of a slot-permuted bare tensor product of two rank-`3`
sections is dominated, at every point, by the **zero-jet-inclusive full-window product grid** in the
two factors' covariant jets:
```
rfns(∇^p (DDtr(perm σ (S ⊗ T))))(x)
  ≤ Cd · ∑_{i ≤ p} rfns(∇^i S)(x) · (∑_{l ≤ p − i} rfns(∇^l T)(x)),
```
with `Cd` independent of the point AND of the two factor sections.

This is the quadratic-TRACE analogue of the parallel rank-reducing single-contraction grid
(`crossCorrParallelContraction_iteratedCovGrad_rfns_fullWindowProductGrid_le`,
`ParallelContractionPointwiseGrid.lean`), the pointwise primitive beneath the quadratic Cross part
of the segment-metric Ricci difference: the Cross section is, by the structural bridge
`crossSection_eq_cometricDoubleDoubleTrace_loweredCocycleProduct`
(`SegmentMetricCurvatureDifferenceCrossTraceProduct.lean`), the `−2`-scaled antisymmetrised pair of
exactly such twice-traced slot-permuted bare products of `(0, 3)` lowered connection-difference
factors.  It composes three sorry-free ingredients: the two parallel cometric `g₀⁻¹` double-trace
rank-reducing contractions (`cometricDoubleTraceContraction g₀ 4` for `(0,6) → (0,4)` and
`cometricDoubleTraceContraction g₀ 2` for `(0,4) → (0,2)`, each entering through the clean one-term
jet grid `ParallelRankReducingContraction.rfns_iteratedCovGrad_le`), the slot-permutation fibre
isometry of every covariant jet (`riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor`), and the
proven bare two-section bilinear-product covariant-jet diagonal grid
(`RfnsBilinearProduct.rfns_iteratedCovGrad_prod_le_diagGrid` at the bare-product instance
`bareTensorRfnsBilinearProduct g₀ 3 3`, whose constant `mu · 4^p` is factor-uniform).

The **cocycle-telescope difference companion** bounds the same twice-traced permuted object on the
polarized two-arm carrier `(A₁ − A₂) ⊗ A₁ + A₂ ⊗ (A₁ − A₂)` (the bilinear telescope of
`A₁ ⊗ A₁ − A₂ ⊗ A₂`, the shape `crossProductPolarized` realises with `A_k` the endpoints' lowered
connection differences) by the full-window product grid carrying the **cocycle difference**
`A₁ − A₂` in the outer sum and BOTH endpoints in the inner sum — both-endpoints base, per the
zero-base lesson (`A₂ = 0` kills an `(A₂)`-only base while the first arm `(A₁ − A₂) ⊗ A₁` survives).

The window is the **full** `i + l ≤ p` triangle and the bound is a **product** of the two single-jet
sums (never a pointwise two-arm *sum* — that bilinear form is Lean-refuted), so these primitives stay
in the admissible product-grid family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The pointwise full-window product-grid covariant-jet bound of the cometric quadratic-trace
product.**  At every point `x`, the intrinsic squared fibre norm of the order-`p` covariant gradient
of the twice-applied cometric double trace (`(0, 6) → (0, 4) → (0, 2)`) of the `σ`-slot-permuted bare
tensor product of two rank-`3` sections `S`, `T` is bounded by the zero-jet-inclusive full-window
product grid
```
rfns(∇^p (DDtr(perm σ (S ⊗ T))))(x)
  ≤ Cd · ∑_{i ≤ p} rfns(∇^i S)(x) · (∑_{l ≤ p − i} rfns(∇^l T)(x)),
```
with a nonnegative constant `Cd` independent of `x` **and of the factor sections `S`, `T`** (it is
the product of the two cometric double-trace envelope constants and the bare-product grid constant
`mu · 4^p`); the factor-uniformity is what the family-uniform quadratic-Cross consumers require.

The outer sum carries the first factor `S`'s jets; the inner sum carries the second factor `T`'s
jets — the orientation of the two-section bare bilinear-product grid. -/
theorem cometricQuadraticTraceProduct_iteratedCovGrad_rfns_fullWindowProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6)) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (S T : SmoothCcTensor g₀ 0 3) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x
          ((iteratedCovGrad g₀ 0 2 p
              (cometricDoubleTraceRecOp (I := I) g₀ 2 0
                (cometricDoubleTraceRecOp (I := I) g₀ 4 0
                  (permuteCcTensor (I := I) g₀ σ
                    (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T))))).toSection x) ≤
        Cd * ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i S).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad g₀ 0 3 l T).toSection x) := by
  classical
  refine ⟨(cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
      ((cometricDoubleTraceContraction (I := I) g₀ 4).kappa *
        ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 3).mu * (4 : ℝ) ^ p)),
    mul_nonneg (cometricDoubleTraceContraction (I := I) g₀ 2).kappa_nonneg
      (mul_nonneg (cometricDoubleTraceContraction (I := I) g₀ 4).kappa_nonneg
        (mul_nonneg (bareTensorRfnsBilinearProduct (I := I) g₀ 3 3).mu_nonneg (by positivity))),
    fun S T x => ?_⟩
  have h42 := (cometricDoubleTraceContraction (I := I) g₀ 2).rfns_iteratedCovGrad_le p 0
    (cometricDoubleTraceRecOp (I := I) g₀ 4 0
      (permuteCcTensor (I := I) g₀ σ (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T))) x
  have h64 := (cometricDoubleTraceContraction (I := I) g₀ 4).rfns_iteratedCovGrad_le p 0
    (permuteCcTensor (I := I) g₀ σ (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T)) x
  have hgrid := (bareTensorRfnsBilinearProduct (I := I) g₀ 3 3).rfns_iteratedCovGrad_prod_le_diagGrid
    p (a := 0) (b := 0) S T x
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x
          ((iteratedCovGrad g₀ 0 2 p
              (cometricDoubleTraceRecOp (I := I) g₀ 2 0
                (cometricDoubleTraceRecOp (I := I) g₀ 4 0
                  (permuteCcTensor (I := I) g₀ σ
                    (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T))))).toSection x)
      ≤ (cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + p) x
            ((iteratedCovGrad g₀ 0 4 p
                (cometricDoubleTraceRecOp (I := I) g₀ 4 0
                  (permuteCcTensor (I := I) g₀ σ
                    (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T)))).toSection x) := h42
    _ ≤ (cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
          ((cometricDoubleTraceContraction (I := I) g₀ 4).kappa *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + p) x
              ((iteratedCovGrad g₀ 0 6 p
                  (permuteCcTensor (I := I) g₀ σ
                    (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T))).toSection x)) :=
        mul_le_mul_of_nonneg_left h64
          (cometricDoubleTraceContraction (I := I) g₀ 2).kappa_nonneg
    _ = (cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
          ((cometricDoubleTraceContraction (I := I) g₀ 4).kappa *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + p) x
              ((iteratedCovGrad g₀ 0 6 p
                  (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T)).toSection x)) := by
        rw [riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) g₀ σ
          (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) S T) p x]
    _ ≤ (cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
          ((cometricDoubleTraceContraction (I := I) g₀ 4).kappa *
            ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 3).mu * (4 : ℝ) ^ p *
              ∑ i ∈ Finset.range (p + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                    ((iteratedCovGrad g₀ 0 3 i S).toSection x)
                  * ∑ l ∈ Finset.range (p + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                        ((iteratedCovGrad g₀ 0 3 l T).toSection x))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgrid
            (cometricDoubleTraceContraction (I := I) g₀ 4).kappa_nonneg)
          (cometricDoubleTraceContraction (I := I) g₀ 2).kappa_nonneg
    _ = (cometricDoubleTraceContraction (I := I) g₀ 2).kappa *
          ((cometricDoubleTraceContraction (I := I) g₀ 4).kappa *
            ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 3).mu * (4 : ℝ) ^ p)) *
          ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i S).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad g₀ 0 3 l T).toSection x) := by ring

/-- **The full-window double sum over the triangle `{(i, l) : i + l ≤ p}` is symmetric in the two
weight families.**  `∑_{i ≤ p} a i · ∑_{l ≤ p − i} b l = ∑_{i ≤ p} b i · ∑_{l ≤ p − i} a l`: both
sides enumerate the products `a i · b l` over the symmetric triangle `i + l ≤ p`.  Local restatement
(the sibling in `ParallelContractionPointwiseGrid.lean` is `private`). -/
private theorem windowProductSum_swap (p : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (p + 1), a i * ∑ l ∈ Finset.range (p + 1 - i), b l)
      = ∑ i ∈ Finset.range (p + 1), b i * ∑ l ∈ Finset.range (p + 1 - i), a l := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun s => ⟨s.2, s.1⟩) (fun s => ⟨s.2, s.1⟩)
  · rintro ⟨i, l⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨i, l⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨i, l⟩ h; rfl
  · rintro ⟨i, l⟩ h; rfl
  · rintro ⟨i, l⟩ h
    simp only []
    ring

/-- **Slot permutation distributes over a section sum.**  `permuteCcTensor g₀ σ` is a fibrewise slot
reindexing, hence additive: its unit model is the `domDomCongr σ` of the operand's
(`permuteCcTensor_unitModel`), and `domDomCongr` is linear.  Local restatement at the
`SmoothCcTensor` level (the subtractive sibling lives `private` in
`SegmentMetricCurvatureDifferenceCovJet.lean`; no additivity lemma for `permuteCcTensor` is on
disk). -/
private theorem permuteCcTensor_add_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A + B) =
      DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        + DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A + B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A + B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DifferentialGeometry.PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A + B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DifferentialGeometry.PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DifferentialGeometry.PDE.DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have haddval : (A + B).toSection x = A.toSection x + B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  have haddval' : ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
        + DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        + (DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ (A + B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A + B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          + (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [haddval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          + Tensor0SBundle.Tensor0SSpace.toModel
          ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ A
            + DifferentialGeometry.PDE.DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [haddval']; rfl

/-- **The section-level cometric double-trace operator is additive.**  `cometricDoubleTraceRecOp` is
the operator-field action `appCc` of a fixed field, additive in the contracted section
(`appCc_add_right`).  Local restatement (only the subtractive `cometricDoubleTraceRecOp_sub` is on
disk). -/
private theorem cometricDoubleTraceRecOp_add_local (g₀ : SmoothRiemannianMetric I M) (q a : ℕ)
    (A B : Integral.L2.SmoothCcTensor g₀ 0 ((q + 2) + a)) :
    cometricDoubleTraceRecOp (I := I) g₀ q a (A + B) =
      cometricDoubleTraceRecOp (I := I) g₀ q a A + cometricDoubleTraceRecOp (I := I) g₀ q a B :=
  appCc_add_right (I := I) (M := M) g₀ ((q + 2) + a) (q + a)
    (cometricDoubleTraceFieldRec (I := I) g₀ q a) A B

/-- **The pointwise full-window product-grid covariant-jet bound of the cometric quadratic-trace
product on the polarized cocycle-telescope carrier.**  At every point `x`, the intrinsic squared
fibre norm of the order-`p` covariant gradient of the twice-applied cometric double trace of the
`σ`-slot-permuted **polarized** two-arm bare-product carrier
`(A₁ − A₂) ⊗ A₁ + A₂ ⊗ (A₁ − A₂)` (the bilinear telescope of `A₁ ⊗ A₁ − A₂ ⊗ A₂`, the shape the
Cross part's `crossProductPolarized` realises with `A_k` the endpoints' lowered connection
differences) is dominated by the zero-jet-inclusive **full-window product grid** carrying the
cocycle difference `A₁ − A₂` in the outer sum and BOTH fixed endpoints in the inner sum:
```
rfns(∇^p (DDtr(perm σ ((A₁−A₂) ⊗ A₁ + A₂ ⊗ (A₁−A₂)))))(x)
  ≤ Cd · ∑_{i ≤ p} rfns(∇^i (A₁ − A₂))(x) · (∑_{l ≤ p − i} (rfns(∇^l A₁)(x) + rfns(∇^l A₂)(x))),
```
with a nonnegative constant `Cd` independent of `x` **and of the sections `A₁`, `A₂`**.

This is the quadratic-trace counterpart of the proven contraction bilinear-difference grid
(`crossCorrParallelContraction_iteratedCovGrad_rfns_bilinearDifference_fullWindowProductGrid_le`):
both telescope arms are single quadratic-trace products
(`cometricQuadraticTraceProduct_iteratedCovGrad_rfns_fullWindowProductGrid_le`), the first arm
arrives with the cocycle in the outer sum directly, the second arm's grid is reoriented by the
triangle window swap `windowProductSum_swap` (its cocycle arrives in the inner sum), and monotone
term-dropping lands both in the shared cocycle-outer × both-endpoints-inner grid.

**Non-vacuity.**  At `A₁ = A₂` the cocycle factor vanishes, so the carrier is `0` and both sides are
`0`; a zero `Cd` is rejected whenever the cocycle is genuinely present.  The inner sum runs over
BOTH endpoints — the single-endpoint base is refuted by the zero-base witness (`A₂ = 0` makes an
`A₂`-only inner sum vanish identically while the first arm is `(A₁) ⊗ A₁ ≠ 0`). -/
theorem cometricQuadraticTraceProduct_iteratedCovGrad_rfns_cocycleTelescope_fullWindowProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6)) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (A₁ A₂ : SmoothCcTensor g₀ 0 3) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + p) x
          ((iteratedCovGrad g₀ 0 2 p
              (cometricDoubleTraceRecOp (I := I) g₀ 2 0
                (cometricDoubleTraceRecOp (I := I) g₀ 4 0
                  (permuteCcTensor (I := I) g₀ σ
                    (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) (A₁ - A₂) A₁
                      + bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) A₂ (A₁ - A₂)))))).toSection x) ≤
        Cd * ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₂).toSection x)) := by
  classical
  obtain ⟨Cq, hCq0, hCq⟩ :=
    cometricQuadraticTraceProduct_iteratedCovGrad_rfns_fullWindowProductGrid_le (I := I) g₀ σ p
  refine ⟨2 * Cq + 2 * Cq, by positivity, fun A₁ A₂ x => ?_⟩
  have h1 := hCq (A₁ - A₂) A₁ x
  have h2 := hCq A₂ (A₁ - A₂) x
  have hsplit : cometricDoubleTraceRecOp (I := I) g₀ 2 0
      (cometricDoubleTraceRecOp (I := I) g₀ 4 0
        (permuteCcTensor (I := I) g₀ σ
          (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) (A₁ - A₂) A₁
            + bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) A₂ (A₁ - A₂)))) =
      (cometricDoubleTraceRecOp (I := I) g₀ 2 0
          (cometricDoubleTraceRecOp (I := I) g₀ 4 0
            (permuteCcTensor (I := I) g₀ σ
              (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) (A₁ - A₂) A₁)))
        + cometricDoubleTraceRecOp (I := I) g₀ 2 0
          (cometricDoubleTraceRecOp (I := I) g₀ 4 0
            (permuteCcTensor (I := I) g₀ σ
              (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) A₂ (A₁ - A₂))))) := by
    refine Eq.trans (congrArg
      (fun W => cometricDoubleTraceRecOp (I := I) g₀ 2 0
        (cometricDoubleTraceRecOp (I := I) g₀ 4 0 W))
      (permuteCcTensor_add_local (I := I) g₀ σ
        (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) (A₁ - A₂) A₁)
        (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) A₂ (A₁ - A₂)))) ?_
    refine Eq.trans (congrArg (cometricDoubleTraceRecOp (I := I) g₀ 2 0)
      (cometricDoubleTraceRecOp_add_local (I := I) g₀ 4 0
        (permuteCcTensor (I := I) g₀ σ
          (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) (A₁ - A₂) A₁))
        (permuteCcTensor (I := I) g₀ σ
          (bareProd (I := I) g₀ 3 3 (a := 0) (b := 0) A₂ (A₁ - A₂))))) ?_
    exact cometricDoubleTraceRecOp_add_local (I := I) g₀ 2 0 _ _
  rw [hsplit, PDE.RicciFlow.iteratedCovGrad_add]
  simp only [Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + p) x _ _) ?_
  have hswap :
      (∑ i ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((iteratedCovGrad g₀ 0 3 i A₂).toSection x)
            * ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad g₀ 0 3 l (A₁ - A₂)).toSection x))
        = ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad g₀ 0 3 l A₂).toSection x) :=
    windowProductSum_swap p _ _
  rw [hswap] at h2
  have hA1le :
      (∑ i ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
            * ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad g₀ 0 3 l A₁).toSection x))
        ≤ ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₂).toSection x)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun l _ => le_add_of_nonneg_right
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l) x _))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x _)
  have hA2le :
      (∑ i ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
              ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
            * ∑ l ∈ Finset.range (p + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad g₀ 0 3 l A₂).toSection x))
        ≤ ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i (A₁ - A₂)).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l A₂).toSection x)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun l _ => le_add_of_nonneg_left
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l) x _))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x _)
  have hb1 := mul_le_mul_of_nonneg_left hA1le hCq0
  have hb2 := mul_le_mul_of_nonneg_left hA2le hCq0
  linarith [h1, h2, hb1, hb2]

end Connection
end Integral
end DifferentialGeometry
