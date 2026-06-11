import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets

/-! # The pairwise connection-difference Koszul identity and the δ-separated cross-correction
difference jet bound (the shared Core-II section-jet bridge)

For two pairs of smooth Riemannian metrics `g₁, g₂` realizing perturbations `T₁, T₂` over a common
background `g₀` on a closed (compact, boundaryless) smooth manifold `M` modelled on a real
inner-product space `E`, this file supplies the two shared **Core-II section-jet bridge** children
beneath the difference-arm of the sealed Ricci–DeTurck right-hand-side covariant-jet expansion.  Both
children are *pairwise* (`g₁, g₂`-difference) generalizations of the single-metric connection-difference
covariant-jet machinery of `ConnectionDifferenceFieldJets.lean`.

## What the bridge is

The single-metric file proves the section-level `g₀`-lowered Koszul identity
(`koszulCombSection`, the clean linear part `2·loweredConnDiffSection + 2·crossCorrectionSection`) and
its iterated-jet bricks (`koszulCombSection_iteratedCovGrad_rfns_le`, sorry-free, and the
fibre-small-gated `crossCorrectionSection_iteratedCovGrad_topRest_split`).  The Ricci *difference* arm
needs the **difference** of two such single-metric pieces, collected onto the single difference factor
`T₁ − T₂` (one high derivative).  Two children carry this:

* `loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff` — the **pure structural identity**
  promoting the proven pointwise difference-of-differences Koszul formula
  (`connDiff_diff_koszul_realize_diffFactor`, `SegmentMetricRicciSectionIdentity.lean`) to the
  `(0, 3)`-section level: the `g₀`-lowered connection-difference difference equals the clean
  permuted-`covGrad` combination on the realized difference factor `realizeSymmCcTensor g₀ (T₁ − T₂)`
  (the single difference factor, one high derivative) minus the cross-correction difference.  No bound;
  proved by unit-extensionality (`tensor0s_ext_unitZero`) over the pointwise identity and the
  connection-difference cocycle (`connDiff_cocycle`).

* `crossCorrectionDiff_iteratedCovGrad_topRest_split` — the genuine **deep shared bottom**: the
  pairwise δ-separated cross-correction *difference* jet bound.  It is the pair-generalization of the
  single-metric `crossCorrectionSection_iteratedCovGrad_topRest_split`, in the consumer-minimal
  Hamilton/Moser two-arm form (a difference-arm piece carrying the single high derivative on the
  realized difference factor, plus a fixed-pair cross piece carrying the endpoint jets against the
  difference's order-`a` chart-Sobolev `C⁰` mass), uniform over the supercritical `H^{a+2}`-bounded
  fibre-small perturbation family.  Its body is `sorry`: a new frontier leaf, the genuine deep
  cross-correction-difference covariant-Leibniz content.

These two children, together with the sorry-free `koszulCombSection_iteratedCovGrad_rfns_le`
difference-arm and the parallel rank-reducing curvature trace
(`ParallelRankReducingContraction.rfns_iteratedCovGrad_le`, `(0, 3) → (0, 2)`), are the shared bottom
the difference-arm covariant-jet consumers reduce over. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ### Child (A): the pairwise structural Koszul identity (no bound)

The section-level promotion of the proven pointwise difference-of-differences Koszul formula
`connDiff_diff_koszul_realize_diffFactor`.  This is a pure algebraic identity of `(0, 3)`-sections,
proved by unit-extensionality. -/

set_option linter.unusedSectionVars false in
/-- **(Child A — the pairwise structural Koszul identity.)**  The `g₀`-lowered connection-difference
*difference* `2·loweredConnDiffSection g₁ g₀ − 2·loweredConnDiffSection g₂ g₀` equals the clean
permuted-`covGrad` combination on the realized single difference factor
`w := realizeSymmCcTensor g₀ (T₁ − T₂)`,
```
R + permute (swap 0 1) R − permute c[0,2,1] R,    R := covGrad g₀ 0 2 w,
```
(the same three slot readings of the realized covariant-derivative evaluation
`covDerivRealizeEval g₀ (T₁ − T₂)` that build `koszulCombSection`) **minus** the cross-correction
difference `2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂`.

This is the section-level form of the pointwise identity `connDiff_diff_koszul_realize_diffFactor`
(carrying the single high derivative on the difference factor).  There is **no bound**: it is a pure
structural `(0, 3)`-section equality.  Proved by unit-extensionality (`tensor0s_ext_unitZero`): the
unit-evaluated model form of the left side is `2·g₀(connDiff g₁ g₂ b a, c)` (the connection-difference
cocycle `connDiff_cocycle` collapses the lowered difference onto the difference connection), and the
two right-hand summands' unit-evaluated model forms are the `covDerivRealizeEval g₀ (T₁ − T₂)`
combination (`covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval`, transported by the slot reindexing
`permuteCcTensor_unitModel`) and the cross-correction value
`2·ccTensorBilinSymm g₀ Tₖ (connDiff gₖ g₀ b a) c` (`crossCorrectionSection_toModel_apply`); the
pointwise Koszul difference formula closes the fibre identity. -/
theorem loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w) :
    (2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀
        - (2 : ℝ) • loweredConnDiffSection (I := I) g₂ g₀ =
      (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
        + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)))
        - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1]
            (Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
              (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))))
      - ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂) := by
  classical
  set R := Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂)) with hR
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 3)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  -- The realized covariant-derivative unit-model of `R` on a tangent triple.
  have hRu : ∀ w : Fin 3 → TangentSpace I x,
      Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x w =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (w 0) (w 1) (w 2) := by
    intro w
    rw [hR, Analysis.Parabolic.TensorSpectral.unitModel]
    have h := covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x
      (w 0) (w 1) (w 2)
    have hwtuple : (![w 0, w 1, w 2] : Fin 3 → TangentSpace I x) = w := by
      funext i; fin_cases i <;> rfl
    rw [hwtuple] at h
    exact h
  -- LHS unit-evaluated model form: the lowered connection-difference difference, then the cocycle.
  have hL : Tensor0SSpace.toModel
      (((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀
          - (2 : ℝ) • loweredConnDiffSection (I := I) g₂ g₀).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      2 * g₀.inner x (connDiff (I := I) g₁ g₂ x (v 1) (v 0)) (v 2) := by
    have hsec : ((2 : ℝ) • loweredConnDiffSection (I := I) g₁ g₀
            - (2 : ℝ) • loweredConnDiffSection (I := I) g₂ g₀).toSection =
        (2 : ℝ) • (loweredConnDiffSection (I := I) g₁ g₀).toSection
          - (2 : ℝ) • (loweredConnDiffSection (I := I) g₂ g₀).toSection := by
      rw [Integral.L2.SmoothCcTensor.toSection_sub,
        Integral.L2.SmoothCcTensor.toSection_smul, Integral.L2.SmoothCcTensor.toSection_smul]
    rw [hsec, ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_smul,
      ContMDiffSection.coe_smul, Pi.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.smul_apply]
    rw [hunit] at *
    have hvtuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    rw [hvtuple,
      loweredConnDiffSection_toModel_apply (I := I) g₁ g₀ x (v 0) (v 1) (v 2),
      loweredConnDiffSection_toModel_apply (I := I) g₂ g₀ x (v 0) (v 1) (v 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, smul_eq_mul]
    rw [connDiff_cocycle (I := I) g₁ g₂ g₀ x (v 1) (v 0), map_sub, ContinuousLinearMap.sub_apply]
    ring
  -- The cross-correction difference unit-evaluated model form.
  have hCross : Tensor0SSpace.toModel
      (((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      2 * ccTensorBilinSymm (I := I) g₀ T₁ x (connDiff (I := I) g₁ g₀ x (v 1) (v 0)) (v 2)
        - 2 * ccTensorBilinSymm (I := I) g₀ T₂ x (connDiff (I := I) g₂ g₀ x (v 1) (v 0)) (v 2) := by
    have hsec : ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
            - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂).toSection =
        (2 : ℝ) • (crossCorrectionSection (I := I) g₁ g₀ T₁).toSection
          - (2 : ℝ) • (crossCorrectionSection (I := I) g₂ g₀ T₂).toSection := by
      rw [Integral.L2.SmoothCcTensor.toSection_sub,
        Integral.L2.SmoothCcTensor.toSection_smul, Integral.L2.SmoothCcTensor.toSection_smul]
    rw [hsec, ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_smul,
      ContMDiffSection.coe_smul, Pi.smul_apply, Pi.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.smul_apply]
    rw [hunit] at *
    have hvtuple : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
    rw [hvtuple,
      crossCorrectionSection_toModel_apply (I := I) g₁ g₀ T₁ x (v 0) (v 1) (v 2),
      crossCorrectionSection_toModel_apply (I := I) g₂ g₀ T₂ x (v 0) (v 1) (v 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, smul_eq_mul]
  -- The middle (clean combination) unit-evaluated model form: the three slot readings of `R`.
  have hP1 := permuteCcTensor_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R x
  have hP2 := permuteCcTensor_unitModel (I := I) g₀ c[(0 : Fin 3), 2, 1] R x
  have hMid : Tensor0SSpace.toModel
      ((R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
          - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 0) (v 1) (v 2)
        + covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 1) (v 0) (v 2)
        - covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 2) (v 0) (v 1) := by
    rw [show (R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
          - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
            (unitZeroSec (I := I) (M := M) x) =
        R.toSection x (unitZeroSec (I := I) (M := M) x)
          + (permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R).toSection x
              (unitZeroSec (I := I) (M := M) x)
          - (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
              (unitZeroSec (I := I) (M := M) x) from by
      rw [Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_add,
        ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
    simp only [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
    have e0 : Tensor0SSpace.toModel (R.toSection x (unitZeroSec (I := I) (M := M) x)) v =
        covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 0) (v 1) (v 2) := by
      have hmod : Tensor0SSpace.toModel (R.toSection x (unitZeroSec (I := I) (M := M) x)) v =
          Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3 R x v := rfl
      rw [hmod]; exact hRu v
    have e1 : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
          (unitZeroSec (I := I) (M := M) x)) v =
        covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 1) (v 0) (v 2) := by
      have hmod : Tensor0SSpace.toModel
          ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R).toSection x
            (unitZeroSec (I := I) (M := M) x)) v =
          Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
            (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) R) x v := rfl
      rw [hmod, hP1, ContinuousMultilinearMap.domDomCongr_apply]
      exact hRu _
    have e2 : Tensor0SSpace.toModel
        ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
          (unitZeroSec (I := I) (M := M) x)) v =
        covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x (v 2) (v 0) (v 1) := by
      have hmod : Tensor0SSpace.toModel
          ((permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
            (unitZeroSec (I := I) (M := M) x)) v =
          Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 3
            (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R) x v := rfl
      rw [hmod, hP2, ContinuousMultilinearMap.domDomCongr_apply]
      exact hRu _
    rw [e0, e1, e2]
  -- Assemble: rewrite both sides' unit-model and close by the pointwise Koszul difference formula.
  rw [show (((R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
            - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R)
          - ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
              - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂)).toSection x
        (unitZeroSec (I := I) (M := M) x)) =
      (R + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) R
            - permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 2, 1] R).toSection x
          (unitZeroSec (I := I) (M := M) x)
        - ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
            - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂).toSection x
            (unitZeroSec (I := I) (M := M) x) from by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]]
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hMid, hCross, hL]
  -- The pointwise difference-of-differences Koszul formula on `(v 0, v 1, v 2)`.
  have hkos := connDiff_diff_koszul_realize_diffFactor (I := I) g₁ g₂ g₀ T₁ T₂ hr1 hr2 x
    (v 0) (v 1) (v 2)
  simp only [smoothExtensionTangent_eq] at hkos
  linarith [hkos]

/-! ### Child (B): the pairwise δ-separated cross-correction difference jet bound (frontier leaf)

The genuine deep shared bottom: the pair-generalization of the single-metric
`crossCorrectionSection_iteratedCovGrad_topRest_split`, in the consumer-minimal Hamilton/Moser two-arm
form.  **Restated to the integrated `L²`-norm-squared two-arm shape** (the pointwise per-`x` form is
false; see below) and matched to the Lie-half consumer `symLoweredDeTurckVF_iteratedCovGrad_topRest_split`
(`DeTurckVFCovGradTopRestSplit.lean`).  Its body is `sorry` — a new frontier leaf. -/

/-- **(Child B — the pairwise δ-separated cross-correction difference jet bound, integrated two-arm
form, frontier leaf.)**  For the two fibre-small `H^{a+2}`-bounded perturbations `T₁, T₂` realized by
`g₁, g₂` over `g₀`, the squared metric `L²` norm of the order-`j` covariant gradient of the
cross-correction *difference* `2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂`
is dominated by the **integrated Hamilton/Moser two-arm sum** — a difference-arm piece carrying the
single high derivative on the realized difference factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` up to
`∇^{j+2}w`, plus a fixed-pair cross piece carrying the endpoint jets against the difference's order-`a`
chart-Sobolev `C⁰` mass — with a nonnegative `j`-indexed constant `Cd j` uniform over the perturbation
family:
```
‖∇^j (2·crossCorrectionSection g₁ g₀ T₁ − 2·crossCorrectionSection g₂ g₀ T₂)‖²
  ≤ Cd j · ∑_{i ≤ j+2} ‖∇^i w‖²
    + (1/4) · (∑_{i ≤ j+2} (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖²,
```
where `‖·‖` is the metric `L²` (semi)norm (`‖S‖² = ∫ rfns(S) dμ`).  This is the form the single
consumer — the Lie-half assembly `symLoweredDeTurckVF_iteratedCovGrad_topRest_split` — actually reads.

**Why INTEGRATED, not pointwise (the former statement was false).**  An earlier *pointwise* per-`x`
`rfns` two-arm form (`rfns(∇^j diff)(x) ≤ Cd·∑ rfns(∇^i w)(x) + (1/4)·(∑(rfns(∇^i T₁)+rfns(∇^i T₂)))·
‖(T₁−T₂).toHs a‖²`) shares the exact disease Lean-refuted in the Lie half: at a joint high-frequency
concentration the middle covariant-Leibniz terms `∇^p w ⊛ ∇^{j+2−p}(fixed)` (both factors of order
`≈ j/2`) are covered by neither arm — for `j > 2a` the left side carries frequency content `|ξ|^j`
against a right side capped at `|ξ|^{2a}`.  This is Gagliardo–Nirenberg interpolation content, true only
after integration.  The bound is therefore stated at the integrated `L²`-norm-squared level (the form
its consumer reads); the honest covariant-Leibniz shape is a pointwise *diagonal product grid*
`rfns(∇^j diff)(x) ≤ Cd·∑_{i+l≤j+2} rfns(∇^i w)(x)·(rfns(∇^l T₁)(x)+rfns(∇^l T₂)(x))`, converted to the
two `L²` arms by the integrated engine `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`.

**Decomposition (the engine the proof rides).**  The cross-correction
`cc(gₖ,Tₖ) = crossCorrParallelContraction g₀ (realizeSymm Tₖ) (loweredConnDiff gₖ g₀)` is the parallel
`g₀`-single cometric contraction `hₖ ⌟ Dₖ` (`crossCorrParallelContraction_eq_crossCorrectionSection`,
`CrossCorrectionParallelContraction.lean`); its bilinear difference factorizes
`cc₁ − cc₂ = (h₁−h₂) ⌟ D₁ + h₂ ⌟ (D₁−D₂)` (`crossCorrParallelContraction_sub_left/_right`, sorry-free),
with `h₁−h₂ = w` the difference factor.  Each arm's `∇^{j}` covariant-Leibniz diagonal product grid is
delivered by the cross-correction contraction's diagonal `rfns` jet grid (the
`RfnsBilinearProduct g₀ 2 3 3` instance assembled in `CrossCorrectionParallelContraction.lean`); the
fixed factors `D₁, D₂` fold into the `T₁, T₂` jets by `exists_riemannianFiberNormSq_iteratedCovGrad_
loweredConnDiff_le_jetSum`, and the difference factor's `C⁰` mass is the supercritical embedding `ha`.
The two diagonal grids are then integrated by the GN two-arm engine into the difference arm `Cd j·∑
‖∇^i w‖²` and the cross arm `(1/4)·(∑(‖∇^i T₁‖²+‖∇^i T₂‖²))·‖(T₁−T₂).toHs a‖²`.

**Non-vacuity.**  Both arms carry genuine content: the difference arm carries `∇^{j+2}w` (a zero `Cd`
falsifies it whenever the cross-correction difference is genuinely present), and the cross arm carries
**both** fixed-pair endpoints `T₁, T₂`.  At `T₁ = T₂` the cross-correction difference vanishes
(`ccTensorBilinSymm g₀ 0 = 0`), `w = 0` and `‖(T₁ − T₂).toHs a‖ = 0`, so the bound is `0 ≤ 0`.  NO
value-bounded operator shape, NO pointwise-`C^{>2}`-jet claim, NO spectral-nonlinearity, NO Weyl
dependence.  Its body is `sorry`: BLOCKED on the public cross-correction-contraction diagonal `rfns`
jet grid (the in-progress `RfnsBilinearProduct g₀ 2 3 3` deliverable of
`CrossCorrectionParallelContraction.lean`); given that grid, the proof is the telescope above plus the
GN two-arm engine. -/
theorem crossCorrectionDiff_iteratedCovGrad_topRest_split
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) :
    ∃ Cd : ℕ → ℝ, (∀ j, 0 ≤ Cd j) ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
        ∀ j : ℕ,
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 j
                ((2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁
                  - (2 : ℝ) • crossCorrectionSection (I := I) g₂ g₀ T₂)‖ ^ 2 ≤
            Cd j * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + (1 / 4 : ℝ) * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

end DeTurck
end PDE
end DifferentialGeometry
