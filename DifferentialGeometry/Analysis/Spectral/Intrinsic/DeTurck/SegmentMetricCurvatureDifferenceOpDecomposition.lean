import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciSectionIdentity
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceField
import DifferentialGeometry.Geometry.Metric.InverseMetricField

/-! # The order-zero section normal form of the sealed Ricci–DeTurck curvature difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **order-zero (`j = 0`) section normal form** of the
sealed curvature-summand difference of the Ricci–DeTurck right-hand side: the difference of the two
`g₀`-retagged curvature sections `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂`
(`SegmentMetricRHSCovJetExpansion.lean`), normalised — at the fibre-evaluation level — into

```
toModel(ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂) ![v, w]
  = Linear[g₁, g₂](v, w)    -- the linear-in-difference covariant-derivative-of-connection-difference part
    + Cross[g₁, g₂](v, w).   -- the genuinely quadratic-in-difference connection-difference∧connection-difference part
```

This is the **identity layer** the covariant-Faà-di-Bruno covariant-jet expansion of the two C4
leaves (`ricciNeg2Diff_covFdB_section_split`, `lieDerivDiff_covFdB_section_split`,
`SegmentMetricRHSCovJetExpansion.lean`) lifts under `∇^j`: it exhibits the order-zero difference as a
sum whose linear part carries a **single metric-difference factor** (the connection-difference cocycle
`connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` makes the per-term linear summand
`Linear` linear in `connDiff g₁ g₂`, and the M2 Koszul representation
`connDiffField_eq_koszul_contraction` realises the metrically-lowered connection difference as the
contraction of the realized covariant derivative `covDerivRealizeEval g₀ (T₁ − T₂)` of the
perturbation difference, with the M1 inverse-metric sharp `inverseMetricSharpFib` providing the
index-raise), and whose cross part is genuinely quadratic in the connection difference (it vanishes to
second order: `Cross[g, g] = 0` by `connDiff_self`).

## The order-zero source identities

The pointwise pieces all live on disk and are sorry-free over the cited foundations:

* `ricciNeg2RetagG0_sub_toModel_eq` / `ricciNeg2RetagG0_sub_toModel_eq_telescope`
  (`SegmentMetricRicciSectionIdentity.lean`) — the fibre value of the retagged curvature-section
  difference is `-2 • (Ric(g₁) − Ric(g₂))`, telescoped against the common background `g₀` into the
  model-basis trace of the per-term differences of the grouped connection-difference summands
  `ricciDiffBasisSummand g₀ g₁ − ricciDiffBasisSummand g₀ g₂`
  (`RicciDifferenceTelescope.lean`).
* `ricciDiffBasisSummand` (`RicciDifferenceTelescope.lean`) is, by construction, the sum of its
  **linear** part — the antisymmetrised covariant-derivative-of-difference `covDerivDiff` (`∇₀ D`,
  with `D = connDiff gₖ g₀` the connection difference) — and its **quadratic** part — the
  antisymmetrised connection-difference∧difference-section `D(·, D(·, ·))`
  (`ConnectionDifferenceCurvature.lean`).
* `connDiff_cocycle` (`ConnectionDifferenceKoszul.lean`) — the connection difference is additive over
  the background: `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀`; hence the linear part's per-term
  difference carries the single factor `connDiff g₁ g₂`.
* `connDiffField_eq_koszul_contraction` (M2, `ConnectionDifferenceField.lean`) — the metrically-lowered
  connection-difference field is the contraction of the realized covariant-derivative combination of
  the perturbation; this is the M1/M2 form the linear-part coefficient consumes (the realized
  `covDerivRealizeEval g₀ (T₁ − T₂)` is the `≤ 1`-jet of `h₁₂`, the single difference factor whose one
  further covariant derivative — the `∇₀ D` of the linear part — is the `≤ 2`-jet the C4 lift's
  coefficient is `κ`-bounded against).

## Main definitions

* `ricciNeg2SectionDiffLinearEval g₀ g₁ g₂ x v w` — the **linear-in-difference** order-zero normal-form
  term: `-2` times the model-basis trace of the antisymmetrised covariant-derivative-of-difference
  parts of `ricciDiffBasisSummand g₀ g₁ − ricciDiffBasisSummand g₀ g₂`.
* `ricciNeg2SectionDiffCrossEval g₀ g₁ g₂ x v w` — the **quadratic-in-difference** Cross term: `-2`
  times the model-basis trace of the antisymmetrised connection-difference∧difference parts.
* `crossBilin g₀ g₁ g₂ x` — the **Cross bilinear form**, an operator-trace continuous bilinear form
  `T_x M →L T_x M →L ℝ` assembled from the M2 connection-difference operator field `connDiffField gₖ g₀`
  (the two cross endomorphisms `crossEndoTerm1`, `crossEndoTerm2`); its `![v, w]`-evaluation is the
  scalar `ricciNeg2SectionDiffCrossEval` (`crossBilin_apply_eq_crossEval`).
* `crossField g₀ g₁ g₂` — the **Cross part as a smooth `(0,2)`-tensor field** (smoothness via the
  trace-pairing smoothness `crossBilin_pairing_contMDiff` on the chart frame); `crossSection` /
  `linearSection` — the two order-zero parts as genuine `SmoothCcTensor g₀ 0 2`s.

## Main results

* `ricciNeg2RetagG0_sub_toModel_normalForm` — **the order-zero section normal form**: the fibre value
  of the retagged curvature-section difference is `Linear + Cross`.
* `ricciNeg2RetagG0_sub_normalForm_j0_collapse` — **the `j = 0`-collapse litmus**: the normal form
  evaluated pointwise reproduces `-2 • (Ric(g₁) − Ric(g₂))` (it is consistent with the proven
  `ricciNeg2RetagG0_sub_toModel_eq`).
* `ricciNeg2SectionDiffLinearEval_g0_lowered_koszul` — **the M1/M2-built linear-part Koszul form**: the
  antisymmetrised `∇₀ D` linear summand, after the connection-difference cocycle, carries the single
  difference factor `connDiff g₁ g₂`, whose metrically-lowered form (M1 sharp `inverseMetricSharpFib` /
  M2 `connDiffField_eq_koszul_contraction`) is the realized covariant derivative
  `covDerivRealizeEval g₀ (T₁ − T₂)` — the bump-screen-clean fixed-pair-coefficient form, with the
  high derivative on the difference factor.
* `ricciNeg2SectionDiffCrossEval_self` / `ricciNeg2SectionDiffLinearEval_self` — **the non-vacuity
  litmus**: both order-zero parts vanish when `g₁ = g₂` (the difference is genuinely a difference; the
  cross part is genuinely second-order, vanishing under `connDiff_self`).
* `ricciNeg2RetagG0_sub_normalForm_section` — **the section-level (`SmoothCcTensor`) promotion of the
  order-zero normal form**: the sealed curvature-section difference `ricciNeg2RetagG0 g₀ g₁ −
  ricciNeg2RetagG0 g₀ g₂` is the sum `linearSection + crossSection` of two genuine `SmoothCcTensor`s
  whose fibre evaluations are the two named order-zero scalar terms.  The Cross section is the genuine
  construction `crossSection` (assembled through `connDiffField` as the operator-trace Cross bilinear
  form, smooth by `crossField`); the linear section is its algebraic complement.  Consistency is
  `ricciNeg2RetagG0_sub_normalForm_section_j0_collapse`; non-vacuity is `crossSection_self_toModel` /
  `linearSection_self_toModel`.

These identities are pure (sorry-free) identity algebra over the sorry-free scalar telescope, the
connection-difference cocycle / Koszul representation, and (for the section-level promotion) the
connection-difference operator-field trace smoothness; the section-level normal form is itself
sorry-free (axiom-clean), independent of the `SegmentMetricRHSCovJetExpansion` C4-leaf posits. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The linear and quadratic order-zero parts

The `ricciDiffBasisSummand g₀ gₖ x v w i` of `RicciDifferenceTelescope.lean` is, by construction, the
sum of an antisymmetrised covariant-derivative-of-difference part `covDerivDiff` (its **linear** order,
`∇₀ D` with `D = connDiff gₖ g₀`) and an antisymmetrised connection-difference∧difference part (its
**quadratic** order, `D(·, D(·, ·))`).  We name the model-basis traces of the per-term differences of
each part; their sum is the order-zero section difference. -/

/-- **The antisymmetrised covariant-derivative-of-difference vector summand** of a single metric's
Ricci difference at a model-basis index `i`: the **linear** order of `ricciDiffBasisSummand g₀ gₖ`, i.e.
`(∇₀_{B_i} D)(V, W) − (∇₀_V D)(B_i, W)` with `D = connDiff gₖ g₀`, `B_i`, `V`, `W` the smooth
extensions of the model-basis frame and of `v`, `w`. -/
def ricciDiffLinearSummand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) x
    - covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
      (smoothExtensionTangent (I := I) x w) x

/-- **The antisymmetrised connection-difference∧difference vector summand** of a single metric's Ricci
difference at a model-basis index `i`: the **quadratic** order of `ricciDiffBasisSummand g₀ gₖ`, i.e.
`D(B_i, D(V, W)) − D(V, D(B_i, W))` with `D = connDiff gₖ g₀` (written through
`CovariantDerivative.difference` and `diffSec` exactly as in `ricciDiffBasisSummand`). -/
def ricciDiffQuadSummand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  CovariantDerivative.difference (LeviCivita (I := I) gₖ) (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
    - CovariantDerivative.difference (LeviCivita (I := I) gₖ) (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x v x)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- The grouped difference-tensor summand `ricciDiffBasisSummand` is, by construction, the sum of its
linear (`ricciDiffLinearSummand`, the `∇₀ D` part) and quadratic (`ricciDiffQuadSummand`, the
`D ∧ D` part) order summands.  Definitional. -/
theorem ricciDiffBasisSummand_eq_linear_add_quad (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    ricciDiffBasisSummand (I := I) g₀ gₖ x v w i =
      ricciDiffLinearSummand (I := I) g₀ gₖ x v w i
        + ricciDiffQuadSummand (I := I) g₀ gₖ x v w i := rfl

/-- **The linear-in-difference order-zero normal-form term.**  `-2` times the model-basis trace of the
per-term differences of the **linear** (covariant-derivative-of-connection-difference) parts of the two
single-metric Ricci differences.  This is the order-zero term that carries the single metric-difference
factor: the connection-difference cocycle `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀` makes each
summand difference linear in `connDiff g₁ g₂` (`ricciNeg2SectionDiffLinearEval_g0_lowered_koszul`),
whose metrically-lowered form (M1/M2) is the realized covariant derivative
`covDerivRealizeEval g₀ (T₁ − T₂)`. -/
def ricciNeg2SectionDiffLinearEval (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : ℝ :=
  (-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (ricciDiffLinearSummand (I := I) g₀ g₁ x v w i
        - ricciDiffLinearSummand (I := I) g₀ g₂ x v w i) i

/-- **The quadratic-in-difference Cross term.**  `-2` times the model-basis trace of the per-term
differences of the **quadratic** (connection-difference∧difference) parts of the two single-metric
Ricci differences.  This is the genuinely second-order remainder: it vanishes when `g₁ = g₂`
(`ricciNeg2SectionDiffCrossEval_self`), and on the segment it is the product of two metric-difference
factors (each `connDiff gₖ g₀` is the `≤ 1`-jet of `hₖ`), the part the C4 lift keeps on the fixed pair
against the difference's `C⁰` mass. -/
def ricciNeg2SectionDiffCrossEval (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : ℝ :=
  (-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (ricciDiffQuadSummand (I := I) g₀ g₁ x v w i
        - ricciDiffQuadSummand (I := I) g₀ g₂ x v w i) i

/-! ### The order-zero section normal form -/

/-- **The order-zero section normal form of the sealed curvature difference.**  The fibre value of the
`g₀`-retagged curvature-section difference `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is the sum
of its linear-in-difference part `ricciNeg2SectionDiffLinearEval` (the `∇₀ D` order, carrying the single
metric-difference factor) and its quadratic-in-difference Cross part `ricciNeg2SectionDiffCrossEval`
(the `D ∧ D` order).

This is the **identity layer** the covariant-Faà-di-Bruno covariant-jet split of the two C4 leaves
lifts under `∇^j`.  It is pure additive algebra over the telescoped order-zero identity
`ricciNeg2RetagG0_sub_toModel_eq_telescope` and the definitional split of `ricciDiffBasisSummand` into
its linear and quadratic orders (`ricciDiffBasisSummand_eq_linear_add_quad`), distributing the
model-basis coordinate functional (`map_sub`, `map_add`, `Finsupp.add_apply`, `Finsupp.sub_apply`) over
the summand split and re-collecting the two finite sums. -/
theorem ricciNeg2RetagG0_sub_toModel_normalForm (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      ricciNeg2SectionDiffLinearEval (I := I) g₀ g₁ g₂ x v w
        + ricciNeg2SectionDiffCrossEval (I := I) g₀ g₁ g₂ x v w := by
  classical
  rw [ricciNeg2RetagG0_sub_toModel_eq_telescope (I := I) g₀ g₁ g₂ x v w]
  -- The per-index coordinate of the summand difference splits into the linear and quadratic parts.
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
          (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
            - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i) i =
        (chartModelBasis E).repr
            (ricciDiffLinearSummand (I := I) g₀ g₁ x v w i
              - ricciDiffLinearSummand (I := I) g₀ g₂ x v w i) i
          + (chartModelBasis E).repr
            (ricciDiffQuadSummand (I := I) g₀ g₁ x v w i
              - ricciDiffQuadSummand (I := I) g₀ g₂ x v w i) i := by
    intro i
    have hsplit :
        ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
            - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i =
          (ricciDiffLinearSummand (I := I) g₀ g₁ x v w i
              - ricciDiffLinearSummand (I := I) g₀ g₂ x v w i)
            + (ricciDiffQuadSummand (I := I) g₀ g₁ x v w i
              - ricciDiffQuadSummand (I := I) g₀ g₂ x v w i) := by
      rw [ricciDiffBasisSummand_eq_linear_add_quad (E := E) g₀ g₁ x v w i,
        ricciDiffBasisSummand_eq_linear_add_quad (E := E) g₀ g₂ x v w i]
      abel
    rw [hsplit, map_add, Finsupp.add_apply]
  rw [ricciNeg2SectionDiffLinearEval, ricciNeg2SectionDiffCrossEval, ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- **The `j = 0`-collapse litmus.**  The order-zero section normal form, summed, reproduces the proven
fibre value `-2 • (Ric(g₁) − Ric(g₂))` of the retagged curvature-section difference
(`ricciNeg2RetagG0_sub_toModel_eq`): the normal-form split is consistent with the sealed Ricci-difference
identity.  This is the screen that the normal form is the genuine order-zero layer (not a mis-stated
substitute). -/
theorem ricciNeg2RetagG0_sub_normalForm_j0_collapse (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciNeg2SectionDiffLinearEval (I := I) g₀ g₁ g₂ x v w
        + ricciNeg2SectionDiffCrossEval (I := I) g₀ g₁ g₂ x v w =
      (-2 : ℝ) * (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w) := by
  rw [← ricciNeg2RetagG0_sub_toModel_normalForm (I := I) g₀ g₁ g₂ x v w]
  have h := ricciNeg2RetagG0_sub_toModel_eq (I := I) g₀ g₁ g₂ x ![v, w]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-! ### Non-vacuity: both order-zero parts vanish to their respective orders -/

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- The quadratic Cross summand of a single metric with itself vanishes: with `gₖ = g₀` the connection
difference `connDiff g₀ g₀ = 0` (`connDiff_self`) makes the difference section, hence the whole
`D ∧ D` summand, zero. -/
theorem ricciDiffQuadSummand_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    ricciDiffQuadSummand (I := I) g₀ g₀ x v w i = 0 := by
  classical
  unfold ricciDiffQuadSummand
  have hdiff : CovariantDerivative.difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
      = (0 : Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TangentSpace I b) := by
    have := connDiff_self (I := I) g₀
    simpa only [connDiff] using this
  simp only [hdiff, Pi.zero_apply, ContinuousLinearMap.zero_apply, sub_self]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- The linear summand of a single metric with itself vanishes: with `gₖ = g₀` the difference
section `diffSec` is zero and `covDerivDiff` (the `∇₀` of the zero difference) vanishes. -/
theorem ricciDiffLinearSummand_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    ricciDiffLinearSummand (I := I) g₀ g₀ x v w i = 0 := by
  classical
  have hself : ∀ (a b c : TangentSpace I x),
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
        (smoothExtensionTangent (I := I) x a)
        (smoothExtensionTangent (I := I) x b)
        (smoothExtensionTangent (I := I) x c) x = 0 := by
    intro a b c
    unfold covDerivDiff
    have hdiff : CovariantDerivative.difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
        = (0 : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y) := by
      have := connDiff_self (I := I) g₀
      simpa only [connDiff] using this
    have hdiffSec : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₀)
        (smoothExtensionTangent (I := I) x b)
        (smoothExtensionTangent (I := I) x c) =
        (0 : Π y : M, TangentSpace I y) := by
      funext y
      simp only [diffSec, hdiff, Pi.zero_apply, ContinuousLinearMap.zero_apply]
    rw [hdiffSec, CovariantDerivative.zero]
    simp only [hdiff, Pi.zero_apply, ContinuousLinearMap.zero_apply, sub_zero]
  unfold ricciDiffLinearSummand
  rw [hself, hself, sub_zero]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **Non-vacuity (Cross is genuinely second-order).**  The Cross term vanishes when `g₁ = g₂`: with no
metric difference the connection difference is zero, so the quadratic `D ∧ D` part is zero.  This
rejects the degenerate reading of the Cross term — it is genuinely the quadratic-in-difference
remainder. -/
theorem ricciNeg2SectionDiffCrossEval_self (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciNeg2SectionDiffCrossEval (I := I) g₀ g g x v w = 0 := by
  classical
  unfold ricciNeg2SectionDiffCrossEval
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (ricciDiffQuadSummand (I := I) g₀ g x v w i
            - ricciDiffQuadSummand (I := I) g₀ g x v w i) i) = 0 from by
    simp only [sub_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]]
  ring

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **Non-vacuity (Linear is genuinely a difference).**  The linear term vanishes when `g₁ = g₂`.  This
rejects the degenerate reading — the linear term genuinely measures the connection-difference change. -/
theorem ricciNeg2SectionDiffLinearEval_self (g₀ g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciNeg2SectionDiffLinearEval (I := I) g₀ g g x v w = 0 := by
  classical
  unfold ricciNeg2SectionDiffLinearEval
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (ricciDiffLinearSummand (I := I) g₀ g x v w i
            - ricciDiffLinearSummand (I := I) g₀ g x v w i) i) = 0 from by
    simp only [sub_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]]
  ring

/-! ### The M1/M2 coefficient-field inventory

The order-zero parts are expressed through the M1 inverse-metric sharp field
(`InverseMetricField.lean`) and the M2 connection-difference operator field
(`ConnectionDifferenceField.lean`): the Cross part's connection-difference factors **are** the M2
field `connDiffField gₖ g₀`, and the linear part's single metric-difference factor — the connection
difference of the difference `connDiff g₁ g₂` (via the cocycle) — is metrically lowered, through the
M2 Koszul representation, to the realized covariant derivative `covDerivRealizeEval g₀ (T₁ − T₂)` of
the perturbation difference, with the M1 inverse-metric sharp providing the index-raise. -/

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **M2 coefficient-field inventory of the Cross part.**  The quadratic Cross summand is built
entirely from the M2 connection-difference operator field `connDiffField gₖ g₀`
(`ConnectionDifferenceField.lean`): both the inner difference section `diffSec` and the outer
`CovariantDerivative.difference` are the fibre value `connDiffField gₖ g₀ x` of the M2 field, so the
Cross part is genuinely the M2-field-quadratic
`connDiffField gₖ g₀ (connDiffField gₖ g₀ V W) B − connDiffField gₖ g₀ (connDiffField gₖ g₀ B W) V`.
This records *which* M2 object the Cross coefficient uses (and that it is a connection-difference
contraction, never a frame jet). -/
theorem ricciDiffQuadSummand_eq_connDiffField (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    ricciDiffQuadSummand (I := I) g₀ gₖ x v w i =
      DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
          (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
            (smoothExtensionTangent (I := I) x w x)
            (smoothExtensionTangent (I := I) x v x))
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
        - DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
          (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
            (smoothExtensionTangent (I := I) x w x)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
          (smoothExtensionTangent (I := I) x v x) := by
  unfold ricciDiffQuadSummand
  simp only [DifferentialGeometry.PDE.DeTurck.connDiffField_apply, connDiff, diffSec]

/-- **M1/M2 lowered-Koszul form of the linear part's difference factor.**  The single metric-difference
factor of the order-zero linear part — the connection difference of the difference `connDiff g₁ g₂`
(the cocycle `connDiff g₁ g₂ = connDiff g₁ g₀ − connDiff g₂ g₀`, M2's `connDiffField g₁ g₂`) —
metrically lowered against the background `g₀`, is the realized covariant-derivative combination
`covDerivRealizeEval g₀ (T₁ − T₂)` of the perturbation difference (M2's
`connDiff_diff_koszul_realize_diffFactor`, the single high derivative on the difference factor),
carrying only a quadratic perturbation·connection-difference correction.  This is the M2 form whose
`≤ 1`-jet realized covariant derivative the C4 lift's coefficient is bounded against; the M1
inverse-metric sharp (`inverseMetricSharpFib_inner`, below) provides the index-raise back to the vector
connection difference. -/
theorem connDiffDiff_g0_lowered_koszul_diffFactor
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (p q : TangentSpace I y),
      g₁.inner y p q = g₀.inner y p q + ccTensorBilinSymm (I := I) g₀ T₁ y p q)
    (hr2 : ∀ (y : M) (p q : TangentSpace I y),
      g₂.inner y p q = g₀.inner y p q + ccTensorBilinSymm (I := I) g₀ T₂ y p q)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₀.inner x
        (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₁ g₂ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      (covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x a b c
        + covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x b a c
        - covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x c a b)
      - (2 * ccTensorBilinSymm (I := I) g₀ T₁ x
          (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₁ g₀ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x)) c
        - 2 * ccTensorBilinSymm (I := I) g₀ T₂ x
          (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₂ g₀ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x)) c) := by
  simp only [DifferentialGeometry.PDE.DeTurck.connDiffField_apply]
  exact connDiff_diff_koszul_realize_diffFactor (I := I) g₁ g₂ g₀ T₁ T₂ hr1 hr2 x a b c

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **M1 index-raise of the lowered connection difference.**  The M1 musical sharp `metricSharp g₀ x`
— the fibrewise inverse metric on which M1's `inverseMetricSharpFib g₀ x` (`InverseMetricField.lean`)
is built — raises the `g₀`-lowered covector `metricFlatLinear g₀ x (connDiff g₁ g₂ x b a)` of the
connection-difference vector back to that very vector:
`♯ (g₀(connDiff g₁ g₂ x b a, ·)) = connDiff g₁ g₂ x b a`.  This records that the M1 inverse metric is
the index-raise tying the metrically-lowered Koszul form
(`connDiffDiff_g0_lowered_koszul_diffFactor`) back to the vector connection difference — the
`Hom(T^*M, TM)` musical operator the order-zero normal form's linear coefficient uses for the
contraction.  Proved from the M1 inverse property `inner_metricSharp` and the positive-definiteness
injectivity `metricFlatLinear_injective` (the round-trip `♯ ∘ ♭ = id`). -/
theorem connDiffField_metricSharp_metricFlat_raise
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    metricSharp g₀ x
        (metricFlatLinear g₀ x
          (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₁ g₂ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x))) =
      DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₁ g₂ x
        (smoothExtensionTangent (I := I) x b x)
        (smoothExtensionTangent (I := I) x a x) := by
  set D : TangentSpace I x :=
    DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) g₁ g₂ x
      (smoothExtensionTangent (I := I) x b x)
      (smoothExtensionTangent (I := I) x a x) with hD
  refine metricFlatLinear_injective g₀ x ?_
  ext c
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  exact inner_metricSharp g₀ x (metricFlatLinear g₀ x D) c

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- **M1 inverse-metric sharp field as the linear coefficient's index-raise (operator-field form).**
The M1 `Hom(T^*M, TM)` operator field `inverseMetricSharpFib g₀ x` (`InverseMetricField.lean`), applied
to a cotangent-fibre covector `α : Tensor0SSpace 1 I x` and paired against any test vector `c` through
the background metric, recovers the covector's value: `g₀(♯ α, c) = α(c)`.  This is the M1 defining
inverse property (`inverseMetricSharpFib_inner`) — the form in which the M1 operator field provides the
index-raise contraction the order-zero linear coefficient applies to the Koszul-lowered `(∇₀ h)`
combination (`connDiffDiff_g0_lowered_koszul_diffFactor`).  This records that the order-zero normal
form's linear coefficient `Φ` uses the M1 inverse-metric operator field, never a chart-frame jet. -/
theorem inverseMetricSharpFib_linearCoeff_raise (g₀ : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (c : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₀ x α) c =
      cotangentToDualLinear (I := I) (x := x) α c :=
  inverseMetricSharpFib_inner (I := I) g₀ x α c

/-! ### The order-zero section normal form, promoted to genuine `SmoothCcTensor` sections

The two order-zero parts `ricciNeg2SectionDiffLinearEval` / `ricciNeg2SectionDiffCrossEval` were named
above only as fibre-evaluation scalar functions.  Here they are promoted to the section level: the
sealed curvature-section difference `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` (already a genuine
`SmoothCcTensor g₀ 0 2`) is exhibited as a sum `linearSection + crossSection` of two genuine
`SmoothCcTensor g₀ 0 2`s whose fibre evaluations are exactly the two named scalar functions.

The Cross part is built first, as a genuine construction.  Its fibre value is a bare endomorphism trace
of a connection-difference composition (`ricciDiffQuadSummand_eq_connDiffField`), so it is assembled
through the M2 operator field `connDiffField gₖ g₀` exactly as the abstract Ricci tensor is assembled
through its curvature endomorphism (`ricciTensorBilin`/`ricciTensor`, `RicciConnection.lean`).  The
linear part is then the algebraic complement `(difference) − crossSection`. -/

/-- **The first cross endomorphism** of a single metric: the `g₀`-connection-difference composition
`u ↦ connDiff gₖ g₀ x (connDiff gₖ g₀ x w v) u`, as a continuous endomorphism of `T_x M`.  Its trace
against the model basis is the first model-trace summand of `ricciDiffQuadSummand g₀ gₖ x v w`
(`ricciDiffQuadSummand_eq_connDiffField`). -/
def crossEndoTerm1 (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
    (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x w v)

/-- **The second cross endomorphism** of a single metric: the `g₀`-connection-difference composition
`u ↦ connDiff gₖ g₀ x (connDiff gₖ g₀ x w u) v`, as a continuous endomorphism of `T_x M` (the outer
slot carries the variable `u`, raised to a contravariant index by tracing).  Its trace against the
model basis is the second model-trace summand of `ricciDiffQuadSummand g₀ gₖ x v w`. -/
def crossEndoTerm2 (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  ((DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x).flip v).comp
    (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x w)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma crossEndoTerm1_apply (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    crossEndoTerm1 (I := I) g₀ gₖ x v w u =
      DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
        (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x w v) u := rfl

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma crossEndoTerm2_apply (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    crossEndoTerm2 (I := I) g₀ gₖ x v w u =
      DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x
        (DifferentialGeometry.PDE.DeTurck.connDiffField (I := I) gₖ g₀ x w u) v := rfl

omit [CompactSpace M] [I.Boundaryless] in
/-- **The model-basis trace summand of the quadratic Cross part of a single metric.**  The model-basis
trace of the quadratic Cross vector summand `ricciDiffQuadSummand g₀ gₖ` equals the difference of the
traces of the two cross endomorphisms `crossEndoTerm1`, `crossEndoTerm2`.  This is the model-trace form
of `ricciDiffQuadSummand_eq_connDiffField` (with `smoothExtensionTangent _ _ _ = _`), the bridge that
re-expresses the choice-built fibre summand as a bare connection-difference endomorphism trace. -/
theorem ricciDiffQuad_modelTrace_eq_crossEndoTrace (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (ricciDiffQuadSummand (I := I) g₀ gₖ x v w i) i =
      LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
        - LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hterm1 : LinearMap.trace ℝ (TangentSpace I x)
        (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (crossEndoTerm1 (I := I) g₀ gₖ x v w ((chartModelBasis E) i)) i := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (chartModelBasis (TangentSpace I x))
      (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x)]
    unfold Matrix.trace
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Matrix.diag_apply]
    rw [LinearMap.toMatrix_apply]
    rfl
  have hterm2 : LinearMap.trace ℝ (TangentSpace I x)
        (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (crossEndoTerm2 (I := I) g₀ gₖ x v w ((chartModelBasis E) i)) i := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (chartModelBasis (TangentSpace I x))
      (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x)]
    unfold Matrix.trace
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Matrix.diag_apply]
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hterm1, hterm2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ricciDiffQuadSummand_eq_connDiffField (E := E) g₀ gₖ x v w i,
    crossEndoTerm1_apply, crossEndoTerm2_apply,
    smoothExtensionTangent_eq (I := I) x v, smoothExtensionTangent_eq (I := I) x w,
    smoothExtensionTangent_eq (I := I) x ((chartModelBasis E) i)]
  rw [map_sub, Finsupp.sub_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- The first cross endomorphism is additive in its `v`-slot. -/
private lemma crossEndoTerm1_add_left (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v v' w : TangentSpace I x) :
    crossEndoTerm1 (I := I) g₀ gₖ x (v + v') w =
      crossEndoTerm1 (I := I) g₀ gₖ x v w + crossEndoTerm1 (I := I) g₀ gₖ x v' w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm1_apply, map_add, ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm1_smul_left (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    crossEndoTerm1 (I := I) g₀ gₖ x (c • v) w = c • crossEndoTerm1 (I := I) g₀ gₖ x v w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm1_apply, map_smul, ContinuousLinearMap.smul_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm1_add_right (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w w' : TangentSpace I x) :
    crossEndoTerm1 (I := I) g₀ gₖ x v (w + w') =
      crossEndoTerm1 (I := I) g₀ gₖ x v w + crossEndoTerm1 (I := I) g₀ gₖ x v w' := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm1_apply, map_add, ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm1_smul_right (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    crossEndoTerm1 (I := I) g₀ gₖ x v (c • w) = c • crossEndoTerm1 (I := I) g₀ gₖ x v w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm1_apply, map_smul, ContinuousLinearMap.smul_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm2_add_left (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v v' w : TangentSpace I x) :
    crossEndoTerm2 (I := I) g₀ gₖ x (v + v') w =
      crossEndoTerm2 (I := I) g₀ gₖ x v w + crossEndoTerm2 (I := I) g₀ gₖ x v' w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm2_apply, map_add, ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm2_smul_left (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    crossEndoTerm2 (I := I) g₀ gₖ x (c • v) w = c • crossEndoTerm2 (I := I) g₀ gₖ x v w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm2_apply, map_smul, ContinuousLinearMap.smul_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm2_add_right (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w w' : TangentSpace I x) :
    crossEndoTerm2 (I := I) g₀ gₖ x v (w + w') =
      crossEndoTerm2 (I := I) g₀ gₖ x v w + crossEndoTerm2 (I := I) g₀ gₖ x v w' := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm2_apply, map_add, ContinuousLinearMap.add_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private lemma crossEndoTerm2_smul_right (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    crossEndoTerm2 (I := I) g₀ gₖ x v (c • w) = c • crossEndoTerm2 (I := I) g₀ gₖ x v w := by
  apply ContinuousLinearMap.ext; intro u
  simp only [crossEndoTerm2_apply, map_smul, ContinuousLinearMap.smul_apply]

/-- **The single-metric quadratic Cross bilinear form** of a metric `gₖ` against the background `g₀`,
as a bilinear form `T_x M →ₗ T_x M →ₗ ℝ`: `(v, w) ↦ tr(crossEndoTerm1) − tr(crossEndoTerm2)`.  This is
the bilinear-form repackaging of the model-basis trace of the quadratic Cross vector summand
`ricciDiffQuadSummand g₀ gₖ` (`ricciDiffQuad_modelTrace_eq_crossEndoTrace`).  Bilinearity follows from
the bilinearity of the two cross endomorphisms in `(v, w)` and the linearity of the trace. -/
def crossBilinSingle (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun v w =>
      LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
        - LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x))
    (fun v v' w => by
      dsimp only
      rw [crossEndoTerm1_add_left, crossEndoTerm2_add_left,
        ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_add, map_add, map_add]; ring)
    (fun c v w => by
      dsimp only
      rw [crossEndoTerm1_smul_left, crossEndoTerm2_smul_left,
        ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_smul, map_smul, map_smul,
        smul_sub])
    (fun v w w' => by
      dsimp only
      rw [crossEndoTerm1_add_right, crossEndoTerm2_add_right,
        ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_add, map_add, map_add]; ring)
    (fun c v w => by
      dsimp only
      rw [crossEndoTerm1_smul_right, crossEndoTerm2_smul_right,
        ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_smul, map_smul, map_smul,
        smul_sub])

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma crossBilinSingle_apply (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    crossBilinSingle (I := I) g₀ gₖ x v w =
      LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm1 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
        - LinearMap.trace ℝ (TangentSpace I x)
          (crossEndoTerm2 (I := I) g₀ gₖ x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := rfl

/-- Auxiliary linear map for the CLM packaging of `crossBilinSingle`: `v ↦
(crossBilinSingle g₀ gₖ x v).toContinuousLinearMap`. -/
private def crossBilinSingleAuxClm (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  { toFun := fun v => LinearMap.toContinuousLinearMap (crossBilinSingle (I := I) g₀ gₖ x v)
    map_add' := fun v v' => by
      ext w
      have := (crossBilinSingle (I := I) g₀ gₖ x).map_add v v'
      have happ := congrArg (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.add_apply, ContinuousLinearMap.add_apply,
             LinearMap.coe_toContinuousLinearMap'] using happ
    map_smul' := fun c v => by
      ext w
      have := (crossBilinSingle (I := I) g₀ gₖ x).map_smul c v
      have happ := congrArg (fun (φ : TangentSpace I x →ₗ[ℝ] ℝ) => φ w) this
      set_option linter.unnecessarySimpa false in
      simpa [LinearMap.smul_apply, ContinuousLinearMap.smul_apply,
             LinearMap.coe_toContinuousLinearMap', smul_eq_mul] using happ }

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma crossBilinSingleAuxClm_apply (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    crossBilinSingleAuxClm (I := I) g₀ gₖ x v w = crossBilinSingle (I := I) g₀ gₖ x v w := rfl

/-- **The single-metric quadratic Cross bilinear form as a continuous bilinear form**
`T_x M →L T_x M →L ℝ`.  This is the operator-norm-packaged form of `crossBilinSingle`, the form the
`(0,2)`-tensor model bridge `bilinFormToModel` consumes (template: `ricciTensor`). -/
def crossBilinSingleClm (g₀ gₖ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (crossBilinSingleAuxClm (I := I) g₀ gₖ x)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma crossBilinSingleClm_apply (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    crossBilinSingleClm (I := I) g₀ gₖ x v w = crossBilinSingle (I := I) g₀ gₖ x v w := by
  change crossBilinSingleAuxClm (I := I) g₀ gₖ x v w = _
  rw [crossBilinSingleAuxClm_apply]

/-- **The quadratic Cross bilinear form of the metric difference**, as a continuous bilinear form
`T_x M →L T_x M →L ℝ`: `-2` times the difference of the two single-metric Cross bilinear forms.  Its
`![v, w]`-evaluation is the quadratic-in-difference Cross term `ricciNeg2SectionDiffCrossEval`
(`crossBilin_apply_eq_crossEval`). -/
def crossBilin (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (-2 : ℝ) • (crossBilinSingleClm (I := I) g₀ g₁ x - crossBilinSingleClm (I := I) g₀ g₂ x)

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma crossBilin_apply (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    crossBilin (I := I) g₀ g₁ g₂ x v w =
      (-2 : ℝ) * (crossBilinSingle (I := I) g₀ g₁ x v w
        - crossBilinSingle (I := I) g₀ g₂ x v w) := by
  unfold crossBilin
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    crossBilinSingleClm_apply, smul_eq_mul]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **The Cross bilinear form evaluates to the quadratic-in-difference Cross term.**  The
`![v, w]`-evaluation of the operator-trace Cross bilinear form `crossBilin` equals the named scalar
order-zero Cross term `ricciNeg2SectionDiffCrossEval`, by the model-trace bridge
`ricciDiffQuad_modelTrace_eq_crossEndoTrace` summed over the model basis. -/
theorem crossBilin_apply_eq_crossEval (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    crossBilin (I := I) g₀ g₁ g₂ x v w = ricciNeg2SectionDiffCrossEval (I := I) g₀ g₁ g₂ x v w := by
  classical
  rw [crossBilin_apply, ricciNeg2SectionDiffCrossEval]
  rw [crossBilinSingle_apply, crossBilinSingle_apply,
    ← ricciDiffQuad_modelTrace_eq_crossEndoTrace (I := I) g₀ g₁ x v w,
    ← ricciDiffQuad_modelTrace_eq_crossEndoTrace (I := I) g₀ g₂ x v w]
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_sub, Finsupp.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- **Local chart-frame trace formula** (file-local reproduction of the curvature trace bridge).
For `b` in the base set of the trivialisation at `x`, the trace of an endomorphism
`F : T_b M →L[ℝ] T_b M` decomposes as the model-basis coordinate sum of `F` against the chart-local
frame `chartBasisVecFiber x i b`.  Proved from `LinearMap.trace_eq_matrix_trace` against the
chart-basis family (`chartBasisFamily`). -/
private lemma trace_eq_chartBasis_sum
    (x : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (F : TangentSpace I b →L[ℝ] TangentSpace I b) :
    LinearMap.trace ℝ (TangentSpace I b) (F : TangentSpace I b →ₗ[ℝ] TangentSpace I b) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt ℝ b
            (F (chartBasisVecFiber (I := I) x i b)))) i := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I b) := inferInstanceAs (FiniteDimensional ℝ E)
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  set basisB := chartBasisFamily (I := I) x hb with hbasisB_def
  rw [LinearMap.trace_eq_matrix_trace ℝ basisB
      (F : TangentSpace I b →ₗ[ℝ] TangentSpace I b)]
  unfold Matrix.trace
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  rw [show basisB i = chartBasisVecFiber (I := I) x i b from
    chartBasisFamily_apply (I := I) x hb i]
  change (basisB.repr (F (chartBasisVecFiber (I := I) x i b))) i =
      ((chartModelBasis E).repr
        (e.continuousLinearMapAt ℝ b (F (chartBasisVecFiber (I := I) x i b)))) i
  rw [hbasisB_def]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  congr 2
  change (e.continuousLinearEquivAt ℝ b hb : TangentSpace I b → E)
      (F (chartBasisVecFiber (I := I) x i b)) =
      (e.continuousLinearMapAt ℝ b : TangentSpace I b → E)
        (F (chartBasisVecFiber (I := I) x i b))
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hb]

/-- The model-basis coordinate functional `v ↦ (chartModelBasis E).repr v i`, packaged as a
continuous linear map `E →L[ℝ] ℝ` (file-local). -/
private noncomputable def crossFinBasisReprAt (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  haveI : T2Space E := inferInstance
  haveI : FiniteDimensional ℝ E := inferInstance
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj i).comp ((chartModelBasis E).equivFun.toLinearMap)) : E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma crossFinBasisReprAt_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    crossFinBasisReprAt (E := E) i v = ((chartModelBasis E).repr v) i := by
  classical
  unfold crossFinBasisReprAt
  change ((LinearMap.proj i).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
/-- **Trace of a fibrewise-smooth endomorphism field is smooth.**  If `A : (x : M) → End(T_x M)` is
such that for every globally smooth tangent vector field `Z` the field `x ↦ A x (Z x)` is smooth,
then the scalar field `x ↦ tr(A x)` is smooth.  This is the file-local generalisation of the curvature
trace-smoothness argument (`ricciTensor_pairing_contMDiff`, `RicciConnection.lean`): the trace is read,
near each point, as a finite model-basis coordinate sum against the chart-local frame
(`trace_eq_chartBasis_sum`), each summand being the model-basis coordinate (`crossFinBasisReprAt`,
smooth) of the trivialisation coordinate of the smooth field `x ↦ A x (Sᵢ x)`. -/
private theorem trace_endoField_contMDiff
    (A : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (hA : ∀ Z : Π b : M, TangentSpace I b, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => A b (Z b)))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => LinearMap.trace ℝ (TangentSpace I b)
        (A b : TangentSpace I b →ₗ[ℝ] TangentSpace I b)) := by
  classical
  intro x
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he_def
  have hex : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartBasisVecFiber (I := I) x k b)) e.baseSet :=
    fun k => chartBasisVec_contMDiffOn (I := I) x k
  obtain ⟨S, hS_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartBasisVecFiber (I := I) x k b)
      (u := e.baseSet) (p := x) h_frame_on e.open_baseSet hex
  have hSk_smooth : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (S k) b : Π b : M, TangentSpace I b)) := fun k => (S k).contMDiff
  -- the smooth field `b ↦ A b (S k b)`
  have hASk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => A b ((S k) b))) := fun k => hA (fun b => (S k) b) (hSk_smooth k)
  -- each model-basis coordinate of the trivialised `A · (S k ·)` is smooth at x
  have hsummand_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun b : M => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ b (A b ((S k) b)))) k) x := by
    intro k
    have h_triv : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun b : M => (e ⟨b, A b ((S k) b)⟩).2) x := by
      have := (contMDiffAt_section (F := E) (E := TangentSpace I) x).mp ((hASk k) x)
      simpa [e, trivializationAt] using this
    have h_eq_nbhd : ∀ᶠ b in 𝓝 x, (e ⟨b, A b ((S k) b)⟩).2 =
        e.continuousLinearMapAt ℝ b (A b ((S k) b)) := by
      filter_upwards [e.open_baseSet.mem_nhds hex] with b hb
      change (Trivialization.continuousLinearEquivAt ℝ e b hb) _ = _
      rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hb]
    have h_clmAt_smooth : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun b : M => e.continuousLinearMapAt ℝ b (A b ((S k) b))) x := by
      apply h_triv.congr_of_eventuallyEq
      filter_upwards [h_eq_nbhd] with b hb
      exact hb.symm
    have h_clm_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossFinBasisReprAt (E := E) k : E → ℝ) :=
      (crossFinBasisReprAt (E := E) k).contMDiff
    have h_comp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun b : M => crossFinBasisReprAt (E := E) k
          (e.continuousLinearMapAt ℝ b (A b ((S k) b)))) x :=
      (h_clm_smooth.contMDiffAt).comp x h_clmAt_smooth
    refine h_comp.congr_of_eventuallyEq ?_
    filter_upwards with b
    exact crossFinBasisReprAt_apply k _
  -- assemble: the trace equals the finite sum near x
  have h_decomp_nhd : ∀ᶠ b in 𝓝 x,
      LinearMap.trace ℝ (TangentSpace I b) (A b : TangentSpace I b →ₗ[ℝ] TangentSpace I b) =
        ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (e.continuousLinearMapAt ℝ b (A b ((S k) b)))) k := by
    filter_upwards [e.open_baseSet.mem_nhds hex, hS_eq] with b hb hSb
    rw [trace_eq_chartBasis_sum (I := I) (x := x) (b := b) hb (A b)]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [show chartBasisVecFiber (I := I) x k b = (S k) b from (hSb k).symm]
  have hsum_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (e.continuousLinearMapAt ℝ b (A b ((S k) b)))) k) x := by
    apply ContMDiffAt.sum
    intro k _
    exact hsummand_smooth k
  refine hsum_smooth.congr_of_eventuallyEq ?_
  filter_upwards [h_decomp_nhd] with b hb
  exact hb

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **Smoothness of the single-metric quadratic Cross bilinear form on smooth fields.**  For smooth
tangent vector fields `X, Y`, the scalar field `x ↦ crossBilinSingle g₀ gₖ x (X x) (Y x)` is smooth.
Both trace summands are traces of smooth connection-difference-composition endomorphism fields, smooth
by `trace_endoField_contMDiff` (whose hypothesis is discharged by `connDiff_contMDiff` applied twice). -/
theorem crossBilinSingle_pairing_contMDiff (g₀ gₖ : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => crossBilinSingle (I := I) g₀ gₖ b (X b) (Y b)) := by
  classical
  -- the inner connection-difference field `b ↦ connDiff gₖ g₀ b (Y b) (X b)` is smooth
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => connDiff (I := I) gₖ g₀ b (Y b) (X b))) := by
    have h := connDiff_contMDiff (I := I) gₖ g₀ hY hX
    exact h
  -- trace of `crossEndoTerm1 g₀ gₖ · (X ·) (Y ·)` is smooth
  have htr1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => LinearMap.trace ℝ (TangentSpace I b)
        (crossEndoTerm1 (I := I) g₀ gₖ b (X b) (Y b) :
          TangentSpace I b →ₗ[ℝ] TangentSpace I b)) := by
    refine trace_endoField_contMDiff (I := I)
      (fun b => crossEndoTerm1 (I := I) g₀ gₖ b (X b) (Y b)) ?_
    intro Z hZ
    have hgoal : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => connDiff (I := I) gₖ g₀ b
          (connDiff (I := I) gₖ g₀ b (Y b) (X b)) (Z b))) :=
      connDiff_contMDiff (I := I) gₖ g₀ hinner hZ
    refine hgoal.congr (fun b => ?_)
    rfl
  -- trace of `crossEndoTerm2 g₀ gₖ · (X ·) (Y ·)` is smooth
  have htr2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => LinearMap.trace ℝ (TangentSpace I b)
        (crossEndoTerm2 (I := I) g₀ gₖ b (X b) (Y b) :
          TangentSpace I b →ₗ[ℝ] TangentSpace I b)) := by
    refine trace_endoField_contMDiff (I := I)
      (fun b => crossEndoTerm2 (I := I) g₀ gₖ b (X b) (Y b)) ?_
    intro Z hZ
    -- `crossEndoTerm2 g₀ gₖ b (X b) (Y b) (Z b) = connDiff gₖ g₀ b (connDiff gₖ g₀ b (Y b) (Z b)) (X b)`
    have hinner2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => connDiff (I := I) gₖ g₀ b (Y b) (Z b))) :=
      connDiff_contMDiff (I := I) gₖ g₀ hY hZ
    have hgoal : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => connDiff (I := I) gₖ g₀ b
          (connDiff (I := I) gₖ g₀ b (Y b) (Z b)) (X b))) :=
      connDiff_contMDiff (I := I) gₖ g₀ hinner2 hX
    refine hgoal.congr (fun b => ?_)
    rfl
  -- assemble
  have hsub := htr1.sub htr2
  refine hsub.congr (fun b => ?_)
  rw [crossBilinSingle_apply]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
/-- **Smoothness of the quadratic Cross bilinear form on smooth fields.**  For smooth tangent vector
fields `X, Y`, the scalar field `x ↦ crossBilin g₀ g₁ g₂ x (X x) (Y x)` is smooth. -/
theorem crossBilin_pairing_contMDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => crossBilin (I := I) g₀ g₁ g₂ b (X b) (Y b)) := by
  have h1 := crossBilinSingle_pairing_contMDiff (I := I) g₀ g₁ hX hY
  have h2 := crossBilinSingle_pairing_contMDiff (I := I) g₀ g₂ hX hY
  have hsub := (contMDiff_const (c := (-2 : ℝ))).mul (h1.sub h2)
  refine hsub.congr (fun b => ?_)
  simp only [crossBilin_apply, Pi.mul_apply]

/-- The pointwise `(0,2)`-tensor model value of the quadratic Cross part: the model multilinear map
obtained from the Cross bilinear form `crossBilin g₀ g₁ g₂ x` by the fibre bridge `bilinFormToModel`. -/
private def crossModelFun (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (bilinFormToModel (TangentSpace I x) (crossBilin (I := I) g₀ g₁ g₂ x))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
private theorem crossModelFun_toModel_apply (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (crossModelFun (I := I) g₀ g₁ g₂ x) v =
      crossBilin (I := I) g₀ g₁ g₂ x (v 0) (v 1) := by
  unfold crossModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (crossBilin (I := I) g₀ g₁ g₂ x) v

/-- **The quadratic Cross part as a smooth covariant `(0,2)`-tensor field.**  Its chart-component
smoothness is the Cross bilinear-form pairing smoothness `crossBilin_pairing_contMDiff` on the
chart-`α`-pushforward frame `chartFrameVec` (the same `contMDiff_multilinearSection_iff_coord` route
as `ricciNeg2Field`). -/
def crossField (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => crossModelFun (I := I) g₀ g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          crossBilin (I := I) g₀ g₁ g₂ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ k bb))
            (chartAt H x₀).source := fun k => by
        have h := chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
        exact h
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun bb : M => chartFrameVec (I := I) x₀ k bb)
          (u := (chartAt H x₀).source) (p := x)
          hframe_on ((chartAt H x₀).open_source) hx
      have hSk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S k) bb : Π bb : M, TangentSpace I bb)) := fun k => (S k).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => crossBilin (I := I) g₀ g₁ g₂ bb ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        crossBilin_pairing_contMDiff (I := I) g₀ g₁ g₂ (hSk (σ 0)) (hSk (σ 1))
      have hpair_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => crossBilin (I := I) g₀ g₁ g₂ bb ((S (σ 0)) bb) ((S (σ 1)) bb)) x :=
        hpair x
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => crossBilin (I := I) g₀ g₁ g₂ x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)) x := by
        refine hpair_at.congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb (σ 0), hb (σ 1)]
      exact hchart_at.contMDiffWithinAt
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (crossModelFun (I := I) g₀ g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [crossModelFun_toModel_apply]
    rfl⟩

/-- The quadratic Cross part as a smooth mixed `(0,2)`-tensor section. -/
def crossMixedSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (crossField (I := I) g₀ g₁ g₂)

/-- **The quadratic Cross part as a `SmoothCcTensor g₀ 0 2`** — the genuine section-level Cross object.
Compact support is automatic on the compact manifold `M`. -/
def crossSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 where
  toSection := crossMixedSection (I := I) g₀ g₁ g₂
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the Cross section.**  Evaluating the underlying `(0,2)` mixed tensor at the
canonical unit `(0,0)`-tensor and a tangent pair recovers the quadratic-in-difference Cross term
`ricciNeg2SectionDiffCrossEval`, by traversing the packaging chain
`crossSection → MixedSection.fromMultilinearSection crossField` (`MixedSection.eval₀_apply`) then
`crossField → Tensor0SSpace.ofModel ∘ bilinFormToModel` (`crossModelFun_toModel_apply`) and the
Cross-form evaluation `crossBilin_apply_eq_crossEval`. -/
theorem crossSection_toModel_apply (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossSection (I := I) g₀ g₁ g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      ricciNeg2SectionDiffCrossEval (I := I) g₀ g₁ g₂ x v w := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (crossField (I := I) g₀ g₁ g₂ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (crossModelFun (I := I) g₀ g₁ g₂ x) ![v, w] = _
  rw [crossModelFun_toModel_apply, ← crossBilin_apply_eq_crossEval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The linear-in-difference part as a `SmoothCcTensor g₀ 0 2`** — the algebraic complement of the
Cross section inside the sealed curvature-section difference:
`linearSection := (ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂) − crossSection`.  By construction
its sum with `crossSection` is the curvature-section difference; its fibre value is the
linear-in-difference order-zero term `ricciNeg2SectionDiffLinearEval`
(`linearSection_toModel_apply`). -/
def linearSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂)
    - crossSection (I := I) g₀ g₁ g₂

/-- **The order-zero section sum identity.**  By the definition of `linearSection` as the algebraic
complement, the sealed curvature-section difference is the sum of its linear and Cross sections. -/
theorem ricciNeg2RetagG0_sub_eq_linear_add_cross (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂ =
      linearSection (I := I) g₀ g₁ g₂ + crossSection (I := I) g₀ g₁ g₂ := by
  rw [linearSection]; abel

/-- **The fibre value of the linear section.**  Evaluating at the canonical unit `(0,0)`-tensor and a
tangent pair recovers the linear-in-difference order-zero term `ricciNeg2SectionDiffLinearEval`.  This
follows by subtracting the proven Cross fibre value (`crossSection_toModel_apply`) from the proven
order-zero section normal form (`ricciNeg2RetagG0_sub_toModel_normalForm`): `Linear + Cross − Cross`. -/
theorem linearSection_toModel_apply (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((linearSection (I := I) g₀ g₁ g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      ricciNeg2SectionDiffLinearEval (I := I) g₀ g₁ g₂ x v w := by
  classical
  have hsec : (linearSection (I := I) g₀ g₁ g₂).toSection =
      (ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂).toSection
        - (crossSection (I := I) g₀ g₁ g₂).toSection := by
    rw [linearSection, Integral.L2.SmoothCcTensor.toSection_sub]
  rw [hsec, ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ricciNeg2RetagG0_sub_toModel_normalForm (I := I) g₀ g₁ g₂ x v w,
    crossSection_toModel_apply (I := I) g₀ g₁ g₂ x v w]
  ring

/-! ### The section-level promotion of the order-zero normal form -/

/-- **The order-zero section normal form, promoted to genuine `SmoothCcTensor` sections.**  The sealed
Ricci–DeTurck curvature-section difference `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is the sum
of two genuine `SmoothCcTensor g₀ 0 2`s — a linear-in-difference section `linearSection` and a
quadratic-in-difference Cross section `crossSection` — whose fibre evaluations are exactly the named
order-zero scalar terms `ricciNeg2SectionDiffLinearEval` (the `∇₀ D` order, carrying the single
metric-difference factor) and `ricciNeg2SectionDiffCrossEval` (the `D ∧ D` order).

This is the section-level (`SmoothCcTensor`) form of the pointwise order-zero normal form
`ricciNeg2RetagG0_sub_toModel_normalForm`: the Cross section is the genuine construction
`crossSection` (assembled through the M2 connection-difference operator field `connDiffField` as the
operator-trace Cross bilinear form `crossBilin`, smooth by `crossField`), and the linear section is its
algebraic complement inside the (already smooth, compactly supported) sealed difference. -/
theorem ricciNeg2RetagG0_sub_normalForm_section (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ∃ linearSection crossSection : Integral.L2.SmoothCcTensor g₀ 0 2,
      ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂ =
          linearSection + crossSection ∧
        (∀ (x : M) (v w : TangentSpace I x),
          Tensor0SSpace.toModel
              (linearSection.toSection x
                (ContinuousMultilinearMap.constOfIsEmpty ℝ
                  (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
            ricciNeg2SectionDiffLinearEval (I := I) g₀ g₁ g₂ x v w) ∧
        (∀ (x : M) (v w : TangentSpace I x),
          Tensor0SSpace.toModel
              (crossSection.toSection x
                (ContinuousMultilinearMap.constOfIsEmpty ℝ
                  (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
            ricciNeg2SectionDiffCrossEval (I := I) g₀ g₁ g₂ x v w) :=
  ⟨linearSection (I := I) g₀ g₁ g₂, crossSection (I := I) g₀ g₁ g₂,
    ricciNeg2RetagG0_sub_eq_linear_add_cross (I := I) g₀ g₁ g₂,
    fun x v w => linearSection_toModel_apply (I := I) g₀ g₁ g₂ x v w,
    fun x v w => crossSection_toModel_apply (I := I) g₀ g₁ g₂ x v w⟩

/-! ### Non-vacuity of the section-level normal form -/

/-- **Non-vacuity (Cross section is genuinely a difference).**  The Cross section's fibre value vanishes
when `g₁ = g₂`: with no metric difference the connection difference is zero, so the quadratic `D ∧ D`
order is zero.  This rejects the degenerate reading of the section-level Cross object (it is genuinely
the quadratic-in-difference remainder, consistent with the pointwise
`ricciNeg2SectionDiffCrossEval_self`). -/
theorem crossSection_self_toModel (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossSection (I := I) g₀ g g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] = 0 := by
  rw [crossSection_toModel_apply, ricciNeg2SectionDiffCrossEval_self]

/-- **Non-vacuity (linear section is genuinely a difference).**  The linear section's fibre value
vanishes when `g₁ = g₂`, consistent with the pointwise `ricciNeg2SectionDiffLinearEval_self`. -/
theorem linearSection_self_toModel (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((linearSection (I := I) g₀ g g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] = 0 := by
  rw [linearSection_toModel_apply, ricciNeg2SectionDiffLinearEval_self]

/-- **The `j = 0`-collapse consistency of the section normal form.**  Summed, the two section fibre
values reproduce the proven fibre value `-2 • (Ric(g₁) − Ric(g₂))` of the sealed curvature-section
difference (`ricciNeg2RetagG0_sub_normalForm_j0_collapse`): the section-level split is consistent with
the sealed Ricci-difference identity, the screen that the promoted normal form is the genuine
order-zero layer (not a mis-stated substitute). -/
theorem ricciNeg2RetagG0_sub_normalForm_section_j0_collapse
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
          ((linearSection (I := I) g₀ g₁ g₂).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w]
        + Tensor0SSpace.toModel
          ((crossSection (I := I) g₀ g₁ g₂).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      (-2 : ℝ) * (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w) := by
  rw [linearSection_toModel_apply, crossSection_toModel_apply,
    ricciNeg2RetagG0_sub_normalForm_j0_collapse (I := I) g₀ g₁ g₂ x v w]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
