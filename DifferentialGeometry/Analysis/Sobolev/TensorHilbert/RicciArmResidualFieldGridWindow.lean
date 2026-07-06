import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower

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

The C-QUAD tower is proven (TRANSIT): the input-slot symmetrization is opened into its
`appCcRS`/`ccSlotSwapField` average, the quadratic subject is converted onto the two
`connDiffSection` jet towers by the posited fixed-`g₀`-frame conversion child
(`exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid`,
a clearly-labelled deferred input, `sorry`), and the capped window assembles through
`exists_rfns_iteratedCovGrad_connDiffSection_tgrid` and the bounded-factor grid product
calculus. The C-BGR tower remains posited as a clearly-labelled deferred input (`sorry`)
with a consumer-minimal statement, per the dossier's fill architecture; every consumer of
either tower transitively depends on `sorryAx` until the outstanding inputs land.
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

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedVariables false in
/-- Fixed-`g₀`-frame / product-engine conversion for the mechanism-B quadratic residual
(the C-QUAD tower's conversion child): the `g₀`-covariant `i`-jets of the `A ⋆ A`
double-`g₀`-orthoframe bi-contraction `gInvDiffQuadResidualField g₀ g₁` are controlled by
the diagonal product grid of the two `connDiffSection g₁ g₀` jet towers, with a constant
depending on `g₀` and `i` only.

LEG-COUNT LAW at birth: ZERO inverse-metric legs cross this estimate — both `g₁⁻¹` raises
of the `A ⋆ A` content stay inside the quoted `connDiffSection` jets on the right, and the
bi-contraction frames are the FIXED `g₀`-orthoframes
(`connDiffBiContrFib g₁ g₀ g₁ g₀ x = connDiffBiContrFibFixedFrame … (smoothOrthoFrame g₀ x) x`),
so `K` is built from `g₀`-frame-jet sups and finrank/card combinatorics alone: no `δ`
binder, no rate denominator, `P`-uniform by construction. The two-leg rate
`(1/(1 − δ₀))²` of the C-QUAD fill enters only through the consuming glue's two citations
of `exists_rfns_iteratedCovGrad_connDiffSection_tgrid` (`CA j₁ * CA j₂`), never here.

SMALL-LITERALS: literal-free `∃ K`-form — no numeric cap appears.

SUP-ANCHOR: the `i = 0` instance is the pointwise anchor — the quadratic fibre is bounded
by `K 0` times the squared `connDiffSection` fibre pair, which the consuming tgrid tower
rates as a `δ`-rated `P`-uniform fibre cap under `∃C`-before-`∀g₁` (the
`rfns_connDiffBiContrFib_self_le_of_lt_one` class: `C * ‖∇P‖⁴`, the `(1,1)` grid cell);
no compactness bound on any `g₁`-dependent object.

Diagonal witness: at `g₁ = g₀` both sides vanish (`connDiff_self`,
`gInvDiffQuadResidualField_self`) — the estimate is tight and non-vacuous there.

DEFERRED INPUT (`sorry`): consumers transitively depend on `sorryAx` until this lands. -/
theorem exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          K i * ∑ j₁ ∈ Finset.range (i + 1), ∑ j₂ ∈ Finset.range (i + 1 - j₁),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x) := sorry

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
realized pointwise anchor is a `δ`-rated `P`-uniform fibre cap under `∃C`-before-`∀g₁`
(erratum-#2 class): the conversion child at `i = 0` composed with the
`exists_rfns_iteratedCovGrad_connDiffSection_tgrid` fibre instance — consistent with the
mechanism-B fibre bound (`rfns_connDiffBiContrFib_self_le_of_lt_one`: the `A ⋆ A` fibre
norm is controlled by `‖∇P‖⁴`, the `(1,1)` cell of the capped grid). The only compactness
bound in the fill (`exists_bound_riemannianFiberNormSq_smoothCcTensor`) is applied to the
`g₁`-INDEPENDENT `ccSlotSwapField` jets, which are trivially `P`-uniform.

TRANSIT: proven by opening `ccInputSymm` into its `appCcRS`/`ccSlotSwapField` average,
converting the quadratic subject onto the two `connDiffSection` jet towers via the posited
conversion child
`exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid`
(a `sorry` deferred input), and assembling the capped window through
`exists_rfns_iteratedCovGrad_connDiffSection_tgrid`, the `appCcRS` diagonal-product-grid
engine, and `boundedFactorGridWindow_mul_le`/`boundedFactorGridWindow_mono`; consumers
transitively depend on `sorryAx` until the child lands. -/
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
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_rfns_iteratedCovGrad_gInvDiffQuadResidualField_connDiffSection_diagonalProductGrid
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set Cq : ℕ → ℝ := fun n => K n *
    ∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
      CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) with hCq_def
  have hCq_nn : ∀ n, 0 ≤ Cq n := by
    intro n
    refine mul_nonneg (hK_nn n) (Finset.sum_nonneg fun j₁ _ => Finset.sum_nonneg fun j₂ _ => ?_)
    exact mul_nonneg (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
      (Combinatorics.windowPairCellCount_nonneg _ _)
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hAjet : ∀ j : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        CA j * Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
      intro j
      have h := hCA g₁ P htie hδ_le hδ0 hbound j x
      have heq : (∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.boundedFactorGridWindow b (j + 1) (j + 2) := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
      rw [← heq]
      exact h
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hK g₁ n x) ?_
      have hsum : (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                (connDiffSection (I := I) g₁ g₀)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
          (∑ j₁ ∈ Finset.range (n + 1), ∑ j₂ ∈ Finset.range (n + 1 - j₁),
            CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2)) * W := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₁ hj₁ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j₂ hj₂ => ?_
        rw [Finset.mem_range] at hj₁ hj₂
        have hA₁ := hAjet j₁
        have hA₂ := hAjet j₂
        have hrfns₂_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + j₂) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j₂ (connDiffSection (I := I) g₁ g₀)).toSection x)
        have hwin₁_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) :=
          Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₁) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₁
                  (connDiffSection (I := I) g₁ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j₂) x
                ((iteratedCovGrad (I := I) g₀ 1 2 j₂
                  (connDiffSection (I := I) g₁ g₀)).toSection x)
            ≤ (CA j₁ * Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2)) *
                (CA j₂ * Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) :=
              mul_le_mul hA₁ hA₂ hrfns₂_nn
                (mul_nonneg (hCA_nn j₁) hwin₁_nn)
          _ = (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (j₁ + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (j₂ + 1) (j₂ + 2)) := by ring
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.boundedFactorGridWindow b (i + 1) (j₁ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (j₂ + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _))
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((j₁ + 2) + (j₂ + 2) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (j₁ + 2)
                (j₂ + 2) (by omega) (by omega)
          _ ≤ (CA j₁ * CA j₂) * (Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn j₁) (hCA_nn j₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              rw [hW_def]
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CA j₁ * CA j₂ * Combinatorics.windowPairCellCount (j₁ + 2) (j₂ + 2) * W := by
              ring
      refine le_trans (mul_le_mul_of_nonneg_left hsum (hK_nn n)) (le_of_eq ?_)
      simp only [hCq_def]
      ring
    have hsubject : ccInputSymm (I := I) (M := M) g₀
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
            + appCcRS (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁
          + appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 2 2
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
              (ccSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) ≤ Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 2 2
            (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
            (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 2 2
        (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
        (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2
                (gInvDiffQuadResidualField (I := I) (M := M) g₀ g₁)
                (ccSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (appCcGdiag (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (appCcGdiag (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

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
