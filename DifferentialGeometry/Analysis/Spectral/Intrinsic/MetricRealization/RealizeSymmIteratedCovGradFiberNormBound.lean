import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge

/-! # The order-`i` realize-jet `riemannianFiberNormSq` domination for the metric-realization map

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the intrinsic `riemannianFiberNormSq` (`rfns`) form of the
metric-realization map's **no-derivative-gain** covariant-jet bound: the order-`i` covariant gradient
of the symmetric realized tensor `realizeSymmCcTensor g₀ T` has its intrinsic squared fibre norm
dominated by the order-`≤ i` covariant jets of the underlying perturbation `T`,
```
rfns(∇^i (realizeSymmCcTensor g₀ T))(x) ≤ C · ∑_{l ≤ i} rfns(∇^l T)(x),
```
the structural step by which the covariant FTC expansion's metric difference `g₁ − g₂` (whose `inner`
is the realized form `ccTensorBilinSymm g₀ (T₁ − T₂)`) has its covariant jets controlled by the
*perturbation difference*'s covariant jets — the single high derivative landing on the perturbation
factor.

This is a **low anchor** for the metric-jet covariant-derivative theory: it depends only on the
realization map's `‖·‖` no-derivative-gain bound (`flipCcTensor_iteratedCovGrad_norm_eq`, the slot-swap
fibre isometry of every `∇^i`) and the `rfns = ‖·‖²` installed-bundle bridge
(`norm_eq_sqrt_tensorInnerPointwise`, `riemannianFiberNormSq_eq_tensorInnerPointwise`), both proven
(sorry-free) over the metric-realization and Riemannian-fibre-norm foundations.  It is extracted to its
own file so that both the segment-metric Ricci–DeTurck right-hand-side covariant-jet expansion and the
connection-difference-field Koszul covariant-jet tower can consume it without a file-level import cycle
between them.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- **The installed-`RiemannianBundle` fibre norm of a tensor value is the square root of its
`rfns`.**  Under the installed Riemannian-bundle instance `tensorRS_riemannianBundle g r s`, the
section-value fibre norm `‖S.toSection x‖` equals `Real.sqrt (riemannianFiberNormSq g r s x
(S.toSection x))`.  This is the bundle bridge `norm_eq_sqrt_tensorInnerPointwise` with the
frame-norm bridge `riemannianFiberNormSq_eq_tensorInnerPointwise` substituted for the model inner
product. -/
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : Integral.L2.SmoothCcTensor g r s) (x : M) :
    (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace r s I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖S.toSection x‖) =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace r s I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M)
    g r s x (S.toSection x)]
  exact Integral.Connection.norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x
    (S.toSection x)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`i` realize-jet `rfns` domination for the metric-realization map.**

For every order `i`, there is a single nonnegative constant `C` such that for every base point `x`
and every smooth compactly-supported `(0,2)`-tensor `T`, the intrinsic squared fibre norm of the
order-`i` covariant gradient of the symmetric realized tensor `realizeSymmCcTensor g₀ T` is dominated
by `C` times the sum of the intrinsic squared fibre norms of the order-`≤ i` covariant gradients of
the underlying tensor `T`:
```
rfns(∇^i (realizeSymmCcTensor g₀ T))(x) ≤ C · ∑_{l ≤ i} rfns(∇^l T)(x).
```

This is the `rfns` form of the realization map's no-derivative-gain bound
`iteratedCovGrad_norm_realizeSymm_le_jetSum` (`‖∇^i realizeSymm T‖ ≤ C₀ · ∑_{l ≤ i} ‖∇^l T‖`):
squaring the fibre-norm bound (`riemannianFiberNormSq_toSection_eq_norm_sq_installed`,
`rfns = ‖·‖²` under the installed instance) and dominating `(∑_{l ≤ i} aₗ)² ≤ (i + 1) · ∑_{l ≤ i} aₗ²`
by Cauchy–Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`), so `C := C₀² · (i + 1)`.  Proved outright; no
posit.  This is the structural step by which the covariant FTC expansion's metric difference
`g₁ − g₂` (whose `inner` is the realized form `ccTensorBilinSymm g₀ (T₁ − T₂)`) has its covariant jets
controlled by the *perturbation difference*'s covariant jets — the single high derivative landing on
the perturbation factor. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T)).toSection x) ≤
          C * ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) := by
  classical
  -- The rfns constant is `i + 1` (the uniform `‖·‖` realize bound has constant `1`, re-derived
  -- inline below; squaring with Cauchy–Schwarz gives the `(i + 1)` factor).
  refine ⟨(i + 1 : ℕ), by positivity, fun T x => ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
  -- Abbreviate the per-order installed fibre norms `aₗ := ‖∇^l T‖`.
  set a : ℕ → ℝ := fun l =>
      (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x‖) with ha_def
  have ha_nn : ∀ l, 0 ≤ a l := by
    intro l
    rw [ha_def]
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
    exact norm_nonneg _
  -- The realize-jet fibre norm `B := ‖∇^i realizeSymm T‖` (installed instance).
  set B : ℝ := ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
      (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖ with hB_def
  have hB_nn : 0 ≤ B := norm_nonneg _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1), a l :=
    Finset.sum_nonneg fun l _ => ha_nn l
  -- Uniform `‖·‖` realize bound with constant `1`: `B = ‖∇^i (½T + ½flip)‖ ≤ ½‖∇^i T‖ + ½‖∇^i flip‖`
  -- `= ‖∇^i T‖ = a i ≤ ∑_{l ≤ i} aₗ` (the slot swap is a fibre isometry of every `∇^i`).
  have hflip_norm := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ T i x
  have hdecomp :
      PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T) =
        (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T) := by
    rw [realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      iteratedCovGrad_smul, iteratedCovGrad_smul]
  have hB_le_ai : B ≤ a i := by
    rw [hB_def, ha_def]
    change ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖ ≤
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T).toSection x‖
    rw [hdecomp]
    rw [show ((1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T +
          (1 / 2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T)).toSection x =
        (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T).toSection x +
          (1 / 2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
            (flipCcTensor (I := I) g₀ T)).toSection x from by
      rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
        SmoothCcTensor.toSection_smul]; rfl]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [hflip_norm]
  have hai_le_sum : a i ≤ ∑ l ∈ Finset.range (i + 1), a l :=
    Finset.single_le_sum (fun l _ => ha_nn l) (Finset.mem_range.mpr (Nat.lt_succ_self i))
  have hB_le_sum : B ≤ ∑ l ∈ Finset.range (i + 1), a l := le_trans hB_le_ai hai_le_sum
  -- `rfns(·) = ‖·‖²` (installed instance), via the `sqrt`-bridge squared.
  have hrfns_eq_sq : ∀ (l : ℕ) (S : Integral.L2.SmoothCcTensor g₀ 0 2),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x) =
        (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + l) I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
        ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S).toSection x‖) ^ 2 := by
    intro l S
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g₀ 0 (2 + l)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l S) x]
    rw [Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)]
  -- The LHS rfns `= B²`; the RHS sum `= ∑ aₗ²`.
  rw [hrfns_eq_sq i (realizeSymmCcTensor (I := I) g₀ T)]
  rw [show (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + i)
      ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T)).toSection x‖) = B from rfl]
  have hsum_rfns_eq : (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) =
      ∑ l ∈ Finset.range (i + 1), a l ^ 2 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hrfns_eq_sq l T, ha_def]
  rw [hsum_rfns_eq]
  -- `B² ≤ (∑ aₗ)² ≤ (i + 1) · ∑ aₗ²` via Cauchy–Schwarz.
  have hBsq : B ^ 2 ≤ (∑ l ∈ Finset.range (i + 1), a l) ^ 2 :=
    pow_le_pow_left₀ hB_nn hB_le_sum 2
  have hCS : (∑ l ∈ Finset.range (i + 1), a l) ^ 2 ≤
      (Finset.range (i + 1)).card * ∑ l ∈ Finset.range (i + 1), a l ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hCS
  exact le_trans hBsq (by exact_mod_cast hCS)

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
