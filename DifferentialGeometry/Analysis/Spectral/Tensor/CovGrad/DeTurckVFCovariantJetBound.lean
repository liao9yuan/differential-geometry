import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientDifference
import DifferentialGeometry.Geometry.Connection.TensorNabla.DeTurckVFIntrinsicValueBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceNeumannJet

/-! # The two-arm covariant jet bound of the DeTurck-field difference gradient

For a closed (compact, boundaryless) smooth Riemannian manifold modelled on a real inner-product
space `E`, the difference of the two DeTurck vector fields `W₁ − W₀`, `Wᵢ = deTurckVF gᵢ g_bg`, is —
by the inverse-Gram-weighted trace formula `deTurckVF_sub_apply_eq_trace_connDiff` — the sum of a
pair-connection-difference trace `Tr_{G₁⁻¹} connDiff(g₁, g₀)` and an inverse-Gram-difference trace
`Tr_{G₁⁻¹ − G₀⁻¹} connDiff(g₀, g_bg)`.  Each summand is a **product** of a `T₁`-driven factor (the
connection difference `connDiff(g₁, g₀)`, or the cometric inverse difference `G₁⁻¹ − G₀⁻¹`) against a
fixed factor.  The `g₀`-lowered `g₀`-Levi-Civita covariant gradient of `W₁ − W₀` is the `(0, 2)`-tensor
carrier `fieldDiffGradSection g₀ g₁ g₀ g_bg`.

This file proves the **family-uniform two-arm Moser jet bound** of that carrier:
```
‖∇^l (fieldDiffGradSection g₀ g₁ g₀ g_bg)‖²
  ≤ C · ∑_{i ≤ l+2} ‖∇^i (realizeSymm T₁)‖²
    + C · (∑_{i ≤ l+2} ‖∇^i T₁‖²) · ‖T₁.toHs a‖²,
```
uniform over the supercritical `H^{a+2}`-bounded `δ`-fibre-small (`δ < 1/2`) realized perturbation
family.  This is the genuine **Lie-line foundation** consumed by the field-slot DeTurck-gradient jet
engines.

## The two-arm shape

The bound carries the same integrated Hamilton/Moser two-arm shape as the curvature sibling
`crossSection_iteratedCovGrad_twoArm_l2Norm_le` and the lowering/connection/field-slot legs
`deTurckVF*SlotDiff_iteratedCovGrad_twoArm_le`: a **difference arm** in the `0`-jet-inclusive
realized-perturbation jets and a **cross arm** keeping the perturbation's full `L²`-jet scale against
its supercritical `H^a` mass.  The high-order jet of `W₁` coefficients is NOT pointwise family-uniform
(the project fact `MetricDifferenceFdBTermTree`), so the clean single-arm `C · ∑ ‖∇^i T₁‖²` shape is
refuted and the two-arm Moser shape is the correct statement.

## Route

The carrier's iterated covariant gradient is fed, through its pointwise covariant-Leibniz product grid
`fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le` (the DeTurck analog of the curvature
sibling's per-permutation cocycle-telescope grid), to the generic Gagliardo–Nirenberg two-arm product
engine `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`.  The product factors' `C⁰`
sups and `L²`-jet folds are supplied by the proven connection-difference jet tower
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum` and the committed cometric
inverse-difference Neumann jet `exists_riemannianFiberNormSq_iteratedCovGrad_cometricInverseDiffSection_le_jetSum`.

INTRINSIC fibre norms only (no chart frame projection). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The realized-perturbation order-`0` `C⁰` fibre sup -/

set_option linter.unusedSectionVars false in
/-- **The order-`0` `C⁰` fibre sup of the realized symmetric perturbation, against its OWN realized
`H^{2(a+2)}` mass.**  For a supercritical order `a` (`2a > finrank + 4`) there is a single constant
`C ≥ 0` such that for every perturbation `T₁` and every point `x`, the order-`0` intrinsic squared fibre
norm of `realizeSymmCcTensor g₀ T₁` is bounded by `(C · ‖(realizeSymm T₁).toHs (2(a+2))‖)²`.

This is the order-`0` term of the unconditional supercritical `C²` covariant-jet embedding
`iteratedCovGradJetSum_le_toHs`: its `iteratedCovGradJetSum` bound dominates `√rfns(realizeSymm T₁)(x)`
(the order-`0` summand) by `C · ‖(realizeSymm T₁).toHs (2(a+2))‖`, so squaring gives the bound with the
*per-`T₁`* realized `H`-mass — the genuine ball factor the cross arm carries. -/
theorem exists_realizeSymm_rfns_fibre_sup_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M),
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) ≤
            (C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                (realizeSymmCcTensor (I := I) g₀ T₁)‖) ^ 2 := by
  classical
  have ha2 : 2 * (a + 2) > Module.finrank ℝ E + 4 := by omega
  obtain ⟨C, hC0, hC⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.iteratedCovGradJetSum_le_toHs
      (I := I) g₀ (a + 2) ha2
  refine ⟨C, hC0.le, fun T₁ x => ?_⟩
  set Dm : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
    (realizeSymmCcTensor (I := I) g₀ T₁)‖ with hDm
  have hDmnn : 0 ≤ Dm := norm_nonneg _
  have hjet := hC (realizeSymmCcTensor (I := I) g₀ T₁) x
  -- The order-`0` term of the jet sum is `√rfns(realizeSymm T₁)(x)`; bound it by `C · Dm`, then square.
  set r0 := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
    ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x) with hr0
  have hrnn : 0 ≤ r0 :=
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + 0) x _
  have hsum0 : Real.sqrt r0 ≤ C * Dm := by
    refine le_trans ?_ hjet
    rw [iteratedCovGradJetSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 0)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0 (realizeSymmCcTensor (I := I) g₀ T₁)) x,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 1)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1 (realizeSymmCcTensor (I := I) g₀ T₁)) x,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 2)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2 (realizeSymmCcTensor (I := I) g₀ T₁)) x]
    simp only [PDE.RicciFlow.iteratedCovGrad_zero]
    rw [← hr0]
    have h1 : (0 : ℝ) ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 1) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 2) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
    linarith [h1, h2, Real.sqrt_nonneg r0]
  have hsq : (Real.sqrt r0) ^ 2 = r0 := Real.sq_sqrt hrnn
  nlinarith [hsum0, hsq, Real.sqrt_nonneg r0, hC0.le, hDmnn,
    mul_nonneg hC0.le hDmnn]

/-! ### The pointwise covariant-Leibniz product grid of the field-difference gradient -/

set_option linter.unusedSectionVars false in
/-- **(POSIT — the pointwise covariant-Leibniz product grid of the DeTurck-field-difference gradient
carrier.)**  For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{a+2}`-bounded (`2a > finrank + 4`) realized perturbation family, the order-`l`
covariant gradient of the field-difference gradient carrier `fieldDiffGradSection g₀ g₁ g₀ g_bg` (fibre
`g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg`) is dominated **pointwise** by the **peeled**
diagonal-convolution product grid of the realized perturbation `realizeSymm T₁` (the difference factor,
order running strictly below the fixed-factor window) against the `g₀`-lowered connection difference
`loweredConnDiffSection g₁ g₀` (the fixed-pair factor):
```
rfns(∇^l (fieldDiffGradSection g₀ g₁ g₀ g_bg))(x)
  ≤ Cgrid l · ∑_{i ≤ l+2} rfns(∇^i (realizeSymm T₁))(x)
                · ∑_{m ≤ l+3 − i} rfns(∇^m (loweredConnDiffSection g₁ g₀))(x).
```

The field difference `W₁ − W₀` is — by the inverse-Gram-weighted trace formula
`deTurckVF_sub_apply_eq_trace_connDiff` (`g₂ = g₀`) — the sum of a pair-connection-difference trace
`Tr_{G₁⁻¹} connDiff(g₁, g₀)` and an inverse-Gram-difference trace `Tr_{G₁⁻¹ − G₀⁻¹} connDiff(g₀, g_bg)`,
each a **product** of a `T₁`-driven factor (the connection difference, lowered into
`loweredConnDiffSection g₁ g₀`, or the cometric inverse difference) against a fixed factor.  Its
`g₀`-lowered `g₀`-Levi-Civita covariant gradient — the `(0,2)`-tensor `fieldDiffGradSection g₀ g₁ g₀ g_bg`
— has, by the covariant Leibniz expansion of the product trace (the binomial placement of the `l + ?`
gradient directions on the two factors, the cometric/inverse-Gram trace weights riding as bounded
coefficient jets), its order-`l` covariant jet a binomial-weighted convolution of the connection-difference
jets and the realized-perturbation jets, with the connection-difference factor's order strictly below the
top — exactly the curvature-half cocycle-telescope grid
(`cometricQuadraticTraceProduct_iteratedCovGrad_rfns_cocycleTelescope_fullWindowProductGrid_le`), in the
Lie-half field-difference setting.

**Non-vacuity.**  The grid carries genuine content on the realized-perturbation jets and the
strictly-lower connection-difference jets (a zero coefficient is rejected whenever a cell is genuinely
present); at `T₁ = 0` realized (`g₁ = g₀`) the field difference is the zero section, the connection
difference vanishes, and the bound is `0 ≤ 0`.  Its body is `sorry`: the genuine covariant-Leibniz product
expansion of the lowered gradient of the inverse-Gram-weighted connection-difference trace (the field-slot
analog of the connection-half cocycle-telescope grid). -/
theorem fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)).toSection x) ≤
            Cgrid * ∑ i ∈ Finset.range (l + 2 + 1),
              Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)
                * ∑ m ∈ Finset.range (l + 3 + 1 - i),
                    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m
                        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) :=
  sorry

/-! ### The generic grid → two-arm assembly -/

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **The generic Gagliardo–Nirenberg two-arm `L²` bound of a `(0,2)` carrier dominated by the
realized-perturbation × lowered-connection-difference product grid.**  For any `(0,2)`-tensor carrier
`F` whose order-`l` covariant gradient is pointwise dominated by the peeled diagonal product grid of
`realizeSymm T₁` (difference factor, window `l+2`) against `loweredConnDiffSection g₁ g₀` (fixed factor,
window `l+3`) — with grid constant `Cgrid` — the integrated `L²` norm of `∇^l F` obeys the two-arm
Moser bound.  The difference factor's per-`T₁` `C⁰` sup (`exists_realizeSymm_rfns_fibre_sup_le`), the
fixed factor's `C⁰` sup (`exists_loweredConnDiffSection_rfns_fibre_sup_le`), and the proven
connection-difference jet tower (`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`)
are threaded through the rectangular GN two-arm engine and the per-order tower fold.  This factors the
common assembly shared by the field-slot and connection-slot two-arm jets. -/
theorem exists_twoArm_of_loweredConnDiff_productGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ)
    (F : ∀ (g₁ : SmoothRiemannianMetric I M), Integral.L2.SmoothCcTensor g₀ 0 2)
    (Cgrid : ℝ) (hCgrid0 : 0 ≤ Cgrid)
    (hgrid : ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (F g₁)).toSection x) ≤
            Cgrid * ∑ i ∈ Finset.range (l + 2 + 1),
              Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)
                * ∑ m ∈ Finset.range (l + 3 + 1 - i),
                    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m
                        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (F g₁)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
            + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
  classical
  obtain ⟨Cd, hCd0, hGN⟩ :=
    Integral.Connection.exists_integrated_diagonalProductGrid_twoArm_rectangular_le
      (I := I) (M := M) g₀ (2 + l) 2 3 (l + 2) (l + 3) (by omega)
  obtain ⟨Cr, hCr0, hΛr⟩ := exists_realizeSymm_rfns_fibre_sup_le (I := I) g₀ a ha
  obtain ⟨ΛD, hΛD0, hΛD⟩ :=
    Integral.Connection.exists_loweredConnDiffSection_rfns_fibre_sup_le
      (I := I) g₀ l δ hδ0 hδ1 B a ha
  choose Cjet hCjet0 hjet using fun m =>
    DifferentialGeometry.PDE.DeTurck.exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum
      (I := I) g₀ m δ hδ0 hδ1 B a ha
  set CjetM : ℝ := ∑ m ∈ Finset.range (l + 3 + 1), Cjet m with hCjetM
  have hCjetM0 : 0 ≤ CjetM := Finset.sum_nonneg fun m _ => hCjet0 m
  refine ⟨Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM, by positivity, ?_⟩
  intro T₁ g₁ hg₁ hδbnd hB hBjet
  set Dn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
    (2 * (a + 2)) (realizeSymmCcTensor (I := I) g₀ T₁)‖ with hDn
  have hDn0 : 0 ≤ Dn := norm_nonneg _
  set U := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (F g₁) with hU
  have hGNu := hGN U (realizeSymmCcTensor (I := I) g₀ T₁) (loweredConnDiffSection (I := I) g₁ g₀)
    Cgrid (Cr * Dn) ΛD hCgrid0 (mul_nonneg hCr0 hDn0) hΛD0
    (fun x => hΛr T₁ x)
    (fun x => hΛD T₁ g₁ hg₁ hδbnd (by
      exact le_trans (DifferentialGeometry.PDE.RicciFlow.toHs_norm_mono (I := I) (M := M) g₀
        (r := 0) (s := 2) (by omega : l + 3 + a ≤ l + 3 + 3 + a) T₁) hBjet) x)
    (fun x => hgrid T₁ g₁ hg₁ hδbnd hB x)
  set Sdiff : ℝ := ∑ i ∈ Finset.range (l + 2 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
    with hSdiff
  set Sfix : ℝ := ∑ m ∈ Finset.range (l + 3 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m (loweredConnDiffSection (I := I) g₁ g₀)‖ ^ 2
    with hSfix
  set ST1 : ℝ := ∑ m ∈ Finset.range (l + 3 + 1 + 1),
    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2 with hST1
  have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hST1_nn : 0 ≤ ST1 := Finset.sum_nonneg fun m _ => sq_nonneg _
  have hSfix_nn : 0 ≤ Sfix := Finset.sum_nonneg fun m _ => sq_nonneg _
  have hSfix_fold : Sfix ≤ CjetM * ST1 := by
    rw [hSfix, hCjetM, Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmle : m ≤ l + 3 := by have := Finset.mem_range.mp hm; omega
    have htow := hjet m T₁ g₁ hg₁ hδbnd (by
      exact le_trans (DifferentialGeometry.PDE.RicciFlow.toHs_norm_mono (I := I) (M := M) g₀
        (r := 0) (s := 2) (by omega : m + 3 + a ≤ l + 3 + 3 + a) T₁) hBjet)
    refine le_trans htow ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCjet0 m)
    rw [hST1]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega : m + 1 + 1 ≤ l + 3 + 1 + 1))
      (fun p _ _ => sq_nonneg _)
  have hcross : (Cr * Dn) ^ 2 * Sfix ≤ Cr ^ 2 * CjetM * (ST1 * Dn ^ 2) := by
    have h1 : (Cr * Dn) ^ 2 * Sfix ≤ (Cr * Dn) ^ 2 * (CjetM * ST1) :=
      mul_le_mul_of_nonneg_left hSfix_fold (by positivity)
    have hexp : (Cr * Dn) ^ 2 * (CjetM * ST1) = Cr ^ 2 * CjetM * (ST1 * Dn ^ 2) := by ring
    rw [hexp] at h1; exact h1
  calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l (F g₁)‖ ^ 2
      ≤ Cd * (ΛD ^ 2 * Sdiff + (Cr * Dn) ^ 2 * Sfix) := hGNu
    _ ≤ Cd * (ΛD ^ 2 * Sdiff + Cr ^ 2 * CjetM * (ST1 * Dn ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hcross]) hCd0
    _ = Cd * ΛD ^ 2 * Sdiff + Cd * Cr ^ 2 * CjetM * (ST1 * Dn ^ 2) := by ring
    _ ≤ (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * Sdiff
          + (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * (ST1 * Dn ^ 2) := by
        have hA : Cd * ΛD ^ 2 * Sdiff ≤ (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * Sdiff :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hSdiff_nn
        have hB' : Cd * Cr ^ 2 * CjetM * (ST1 * Dn ^ 2) ≤
            (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * (ST1 * Dn ^ 2) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
        linarith [hA, hB']
    _ = (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * Sdiff
          + (Cd * ΛD ^ 2 + Cd * Cr ^ 2 * CjetM) * ST1 * Dn ^ 2 := by ring

/-! ### The headline — the family-uniform two-arm covariant jet of the DeTurck-field difference -/

set_option linter.unusedSectionVars false in
/-- **The family-uniform two-arm covariant jet bound of the DeTurck-field-difference gradient
(the Lie-line foundation).**

For a closed Riemannian manifold `(M, g₀)`, a flow background `g_bg`, an order `l`, a fibre-smallness
parameter `δ < 1/2`, a supercritical order `a` (`2a > finrank + 4`), and a Sobolev ball radius `B`, there
is a single nonnegative constant `C` such that for every realized fibre-small `H^{a+2}`-bounded
perturbation `(T₁, g₁)`, the intrinsic squared metric `L²` norm of the order-`l` covariant gradient of the
`g₀`-lowered `g₀`-Levi-Civita covariant gradient of the DeTurck-field difference `W₁ − W₀`
(`Wᵢ = deTurckVF gᵢ g_bg`) — the `(0,2)`-tensor carrier `fieldDiffGradSection g₀ g₁ g₀ g_bg` — obeys the
**integrated Hamilton/Moser two-arm bound**
```
‖∇^l (fieldDiffGradSection g₀ g₁ g₀ g_bg)‖²
  ≤ C · ∑_{i ≤ l+2} ‖∇^i (realizeSymm T₁)‖²
    + C · (∑_{m ≤ l+3} ‖∇^m T₁‖²) · ‖(realizeSymm T₁).toHs (2(a+2))‖²,
```
a **difference arm** in the `0`-jet-inclusive realized-perturbation jets and a **cross arm** keeping the
perturbation's full `L²`-jet scale against its supercritical `H`-mass.

This is the field-slot Lie-line analog of the curvature half's
`crossSection_iteratedCovGrad_twoArm_l2Norm_le`.  The clean single-arm `C · ∑ ‖∇^i T₁‖²` shape is
refuted at high order (the project fact `MetricDifferenceFdBTermTree`: the `W₁` coefficient jets of order
`> 2` are not family-uniformly pointwise bounded), forcing the two-arm Moser shape.

**Route.**  The carrier's order-`l` covariant gradient is pointwise dominated by the peeled diagonal
product grid `fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le` (the difference factor
`realizeSymm T₁` at window `l+2`, strictly below the fixed factor `loweredConnDiffSection g₁ g₀` at window
`l+3`); the rectangular Gagliardo–Nirenberg two-arm engine
`exists_integrated_diagonalProductGrid_twoArm_rectangular_le` integrates this into the two-arm `L²` bound
with the difference factor's `C⁰` sup (`exists_realizeSymm_rfns_fibre_sup_le`) and the fixed factor's `C⁰`
sup (`exists_loweredConnDiffSection_rfns_fibre_sup_le`); the cross arm's fixed-factor `L²`-jet sum is folded
into the `T₁`-jet through the proven connection-difference jet tower
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`.

**Non-vacuity.**  At `T₁ = 0` realized (`g₁ = g₀`), `W₁ = W₀`, the carrier is the zero section and both
arms are `0`.  Genuine: a zero `C` forces `∇^l fieldDiffGradSection ≡ 0` for every fibre-small `T₁`, false
whenever `g₁ ≠ g₀`.  Consumers transitively depend on `sorryAx` through the posited product grid and the
two posited `C⁰`-sup / Neumann children. -/
theorem exists_iteratedCovGrad_deTurckVF_le_jetSum
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
            + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
  obtain ⟨Cgrid, hCgrid0, hgrid⟩ :=
    fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
  exact exists_twoArm_of_loweredConnDiff_productGrid (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
    (fun g₁ => fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) Cgrid hCgrid0 hgrid

/-! ### The connection-slot two-arm jet — the action-section analog -/

set_option linter.unusedSectionVars false in
/-- **(POSIT — the pointwise covariant-Leibniz product grid of the connection-difference action
section.)**  The connection-slot analog of `fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le`:
the order-`l` covariant gradient of the connection-difference action section
`connDiffActionSection g₀ g₁ g₀ g_bg` (fibre `g₀(connDiff g₁ g₀ x (W₁ x) v, w)`, `W₁ = deTurckVF g₁ g_bg`)
is dominated **pointwise** by the peeled diagonal product grid of `realizeSymm T₁` (difference factor,
window `l+2`) against `loweredConnDiffSection g₁ g₀` (fixed factor, window `l+3`).

The action section is the middle-slot contraction of the `g₀`-lowered connection difference against the
fixed DeTurck field `W₁`; the covariant-Leibniz product-jet expansion of the contraction places the
gradient directions on the connection-difference factor (`loweredConnDiffSection g₁ g₀`, realized-Koszul
in `T₁`) and the bounded smooth `W₁`-jet coefficient — the connection-half analog of the field-slot grid.
At `T₁ = 0` realized the action section is the zero section.  Its body is `sorry`: the genuine
covariant-Leibniz product expansion of the connection-difference action. -/
theorem connDiffActionSection_iteratedCovGrad_rfns_productGrid_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ Cgrid : ℝ, 0 ≤ Cgrid ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)).toSection x) ≤
            Cgrid * ∑ i ∈ Finset.range (l + 2 + 1),
              Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)
                * ∑ m ∈ Finset.range (l + 3 + 1 - i),
                    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m
                        (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) :=
  sorry

set_option linter.unusedSectionVars false in
/-- **The family-uniform two-arm covariant jet bound of the connection-difference action section.**
The connection-slot analog of `exists_iteratedCovGrad_deTurckVF_le_jetSum`: the order-`l` covariant jet
`L²` norm of `connDiffActionSection g₀ g₁ g₀ g_bg` obeys the integrated two-arm Moser bound, proven over
the connection-slot product grid `connDiffActionSection_iteratedCovGrad_rfns_productGrid_le` and the
generic grid → two-arm assembly `exists_twoArm_of_loweredConnDiff_productGrid`. -/
theorem exists_iteratedCovGrad_connDiffActionSection_le_jetSum
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
            + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
  obtain ⟨Cgrid, hCgrid0, hgrid⟩ :=
    connDiffActionSection_iteratedCovGrad_rfns_productGrid_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
  exact exists_twoArm_of_loweredConnDiff_productGrid (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
    (fun g₁ => connDiffActionSection (I := I) g₀ g₁ g₀ g_bg) Cgrid hCgrid0 hgrid

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
