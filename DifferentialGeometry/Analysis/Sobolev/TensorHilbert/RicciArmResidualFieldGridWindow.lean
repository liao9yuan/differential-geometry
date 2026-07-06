import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid

/-!
# Capped bounded-factor grid windows for the arm-0 residual coefficient fields

The two capped bounded-factor grid towers of the leader-signed M-dossier (§iii, children
C-QUAD and C-BGR): pointwise bounds, at the bounded-factor grid of cap `i + 1` over the
window `i + 3` in the perturbation jets, for the covariant gradients of the
input-slot-symmetrized arm-0 residual coefficient fields `gInvDiffQuadResidualField`
(DEF-1, the mechanism-B `A ⋆ A` quadratic residual) and `bgRDiffRefoldRemainderField`
(DEF-2, the bg-R difference and refold remainder), generic in a perturbed metric
`g₁ = g₀ + P`, with the constant `P`-uniform and `δ₀`-dependent, no ball binder — the
statements mirror the M-child capped-grid target of
`RicciThreeArmCorrectionFieldTameEnvelope` binder-for-binder, so the eventual assembly
glue composes through `ccInputSymm_add` and `riemannianFiberNormSq_add_le` without
friction.

Both towers are posited here as clearly-labelled deferred inputs (`sorry`) with
consumer-minimal statements, per the dossier's fill architecture; every consumer
transitively depends on `sorryAx` until they land.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
/-- Dossier child C-QUAD: pointwise capped-grid bound for the covariant gradients of the
input-slot-symmetrized mechanism-B quadratic residual field
`ccInputSymm (gInvDiffQuadResidualField g₀ g₁)` (DEF-1), generic in a perturbed metric
`g₁ = g₀ + P`, at the bounded-factor grid of cap `i + 1` over the window `i + 3` in the
`P`-jets, with `C` `P`-uniform and `δ₀`-dependent.

LEG-COUNT LAW at birth (fork-4 rule): the field carries TWO connection-difference legs
(`A ⋆ A`; each `connDiff` is one `g₁⁻¹` raise), so the constant construction of any fill
must carry the two-leg rate `(1/(1 − δ₀))²` — placed in the `C`-construction, never as a
naked cap literal: the statement is literal-free (the `∃ C` bounded-factor-grid form
absorbs the rate) and `δ₀ < 1` is fixed in the outer binder, so the two-leg factor is
finite. A `(1 − δ)¹`-rated cap is FALSE at two legs: lane X witness (`n = 2`, pure trace
`T = −c • g₀`, `δ = 3/4`): `32400 > 10368`; lane Y witness (`n = 1`, `S¹`, `δ = 3/4`):
`1296 > 81` — the `n = 1` tightness of the two-leg rate. Lane Z cert class (`A`–`I`
transcript): `2√n³·δ/(1−δ)² ≤ 4√n³·δ/(1−δ)` at `δ ≤ 1/2` — no such literal appears here;
the construction stays finite at each finrank `n = 1, 2, 3`.

MECHANISM B (grid_witness `n = 2`, the direct test bed, leader-certified
`/tmp/grid_witness.lean`): the quadratic one-jet residual occupies total grid weight
`k = i + 2` with per-factor order at most `i + 1` (`mainB`: `comb = −1/4` on the symmetric
datum at the one-jet witness, degree-2 homogeneous), which the cap `i + 1` over the window
`i + 3` accommodates — cells `e = (a + 1, b + 1)`, `a + b = i`.

SUP-ANCHOR law: the `k = 0` grid cell (`1 ≤` the window, by
`Combinatorics.one_le_boundedFactorGridWindow`) carries the order-zero fibre sup; the
pointwise anchor class for the generic-`g₁` field is the compactness bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor`, with the `P`-uniform rate through the
mechanism-B fibre bound (`rfns_connDiffBiContrFib_self_le_of_lt_one`: the `A ⋆ A` fibre
norm is controlled by `‖∇P‖⁴`, the `(1,1)` cell of the capped grid).

DEFERRED INPUT (`sorry`): consumers transitively depend on `sorryAx` until this lands. -/
theorem rfns_iteratedCovGrad_gInvDiffQuadResidualFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := sorry

set_option linter.unusedVariables false in
/-- Dossier child C-BGR: pointwise capped-grid bound for the covariant gradients of the
input-slot-symmetrized bg-R difference and refold remainder field
`ccInputSymm (bgRDiffRefoldRemainderField g₀ g₁)` (DEF-2), generic in a perturbed metric
`g₁ = g₀ + P`, at the bounded-factor grid of cap `i + 1` over the window `i + 3` in the
`P`-jets, with `C` `P`-uniform and `δ₀`-dependent.

LEG-COUNT LAW at birth: the field carries at most ONE inverse-metric leg — the bg-R trace
difference has zero legs (fixed background `R₀`, compact sup; frames enter at the zero
jet), the Ricci-fold remainder is zero-jet in the weight against `R₀` (zero legs), and the
`(∇♯)K`-residual carries exactly one `g₁`-raise at the zero jet (one leg) — so the
constant construction of any fill carries the one-leg rate `(1/(1 − δ₀))¹`, placed in the
`C`-construction, never as a naked cap literal; `δ₀ < 1` in the outer binder keeps it
finite, `4√n³·δ/(1−δ)`-class at each finrank `n = 1, 2, 3` (`√n³ = 1, 2√2, 3√3`). The
two-leg violations of the lane X/Y witnesses (`32400 > 10368`; `1296 > 81`) do not arise
here: the `A ⋆ A` two-leg content is DEF-1's, not this field's.

MECHANISM B (grid_witness `n = 2`, leader-certified `/tmp/grid_witness.lean`): on the
one-jet witness the residual content sits at total grid weight `k = i + 2` with per-factor
order at most `i + 1` (the `(∇♯)`-leg is one-jet in `P` against the one-jet Koszul of the
metric-difference weight), inside the capped window.

SUP-ANCHOR law: the `k = 0` grid cell (`1 ≤` the window, by
`Combinatorics.one_le_boundedFactorGridWindow`) carries the order-zero fibre sup; the
pointwise anchor class is the compactness bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor`, with the realized-path precedent
`exists_ricciArmOrder0BgRCommCoeffField_realizedFam_rfns_ballUniform` for the bg-R trace
summand.

DEFERRED INPUT (`sorry`): consumers transitively depend on `sorryAx` until this lands. -/
theorem rfns_iteratedCovGrad_bgRDiffRefoldRemainderFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSymm (I := I) (M := M) g₀
                (bgRDiffRefoldRemainderField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := sorry

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
