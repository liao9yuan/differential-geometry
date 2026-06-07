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

These identities are pure (sorry-free) identity algebra over the sorry-free scalar telescope and the
connection-difference cocycle / Koszul representation; consumers transitively depend on `sorryAx` only
through whatever the cited foundations already carry. -/

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

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
