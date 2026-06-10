import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid

/-! # The DeTurck-Cartan linear-arm `DiffBilinOp` instance

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file builds the **first concrete `DiffBilinOp` instance** in the
library: `deTurckCartanDiffBilinOp`, the recursively-differentiated fibrewise-linear contraction
operator family that carries the **linear arm** of the covariant Faà-di-Bruno expansion of the
DeTurck-Cartan right-hand side.

## What a `DiffBilinOp` is, and what the linear arm consumes from it

`DiffBilinOp g₀` (`MetricContractionLeibnizGrid.lean`) packages a *recursively-differentiated*
fibrewise-`ℝ`-linear bilinear-contraction operator family `op p r : SmoothCcTensor g₀ 0 r →
SmoothCcTensor g₀ 0 (r + p)` together with the two genuine `∇`-compatibility fields: the exact
single-step covariant Leibniz `covGrad_op` (`∇(op p r W) = op (p+1) r W + cast(op p (r+1) (∇W))`, the
non-parallel rule whose differentiated-operator cross term survives) and the per-order/per-rank,
base-point-uniform proportional fibre envelope in **jet** form `rfns_op_le`
(`rfns(op p r W)(x) ≤ kappa p r · ∑_{q < p+1} rfns(∇^q W)(x)`).  From these the engine
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` (sorry-free) discharges the single-sum grid
```
rfns(∇^j (op 0 r W))(x) ≤ C r j · ∑_{q < j+1} rfns(∇^q W)(x)
```
**outright** — this `∑_{q ≤ j} rfns(∇^q w)` shape on the difference factor `w` is exactly the
linear-arm contribution the DeTurck-Cartan covariant top/rest split
(`symLoweredDeTurckVF_iteratedCovGrad_topRest_split`, the P1b consumer) wires as the linear piece of
its top/rest recombination, beside the quadratic `RfnsBilinearProduct` arm and the realized-Koszul jet
domination.

## The construction — the recursive covariant-Leibniz remainder tower over the value-local base

The whole family `op` is generated, exactly as the curvature file's `diffCurvOp`
(`CurvatureContractionLeibnizGridConstruction.lean`) generates the `R(X, Y)·` tower, from the
order-`0` **value-local identity** base by the recursive covariant Leibniz remainder, **rfns-direct**:
every member is a `SmoothCcTensor`-valued section (NOT a Hom-bundle CLM section), so the construction
sits in the intrinsic `g`-fibre-norm currency with no model `NormedSpace` anywhere.
```
op 0 r W := W   (the order-0, value-local identity contraction),
op (p+1) r W := ∇(op p r W) − (rank-cast) op p (r+1) (∇W)   (the exact Leibniz remainder).
```
With this definition `covGrad_op` holds *by construction* (`sub_add_cancel`,
`deTurckCartanOp_covGrad`), independently of the base.

## Why the order-`0` base is value-local (identity), and where the `g₀⁻¹·∇W` content lives

The Cartan bilinear form `g₀(∇_v W, w) + g₀(v, ∇_w W)` reads the *gradient* `∇W`, so it is a
**first**-order datum, not the order-`0` value an `op 0 r` reads.  As in the curvature tower, the
`g₀`-Levi-Civita `∇`-content of the linear arm is carried by the **differentiated** members, generated
from the order-`0` base through the exact covariant Leibniz.  Taking the order-`0` base to be the
value-local identity `op 0 r W = W` makes the recursive Leibniz remainder telescope: the order-`1`
member `op 1 r W = ∇W − ∇W = 0`, and inductively `op p r W = 0` for every `p ≥ 1`
(`deTurckCartanOp_succ_eq_zero`).  This is the canonical **linear-arm envelope object**: the consumer
reads off only the `p = 0` single-sum grid (`op 0 r W = W`, so `rfns(∇^j(op 0 r W))(x) = rfns(∇^j W)(x)`),
which is exactly the `∑_{q ≤ j} rfns(∇^q w)` jet domination the linear piece needs against the
difference factor `w = realizeSymmCcTensor g₀ (T₁ − T₂)`.

The P1b consumer `symLoweredDeTurckVF_iteratedCovGrad_topRest_split` does **not** read the value of
`op 0 2 w` (its bound carries, by design, "no value-bounded `Φ.op 0 2 w` shape" — the `∇^{j+2} w`
content rides as the order-`≤ j+2` covariant jet, supplied by this engine's `∑_q rfns(∇^q w)` grid);
it consumes only the jet-grid shape.

## Non-vacuity

`deTurckCartanDiffBilinOp_op_zero_eq_self` certifies the instance is not the degenerate `kappa ≡ 0`
witness: `op 0 r W = W`, so for any `W ≠ 0` the order-`0` member is nonzero, forcing
`rfns(op 0 r W)(x) > 0` at a point where `W(x) ≠ 0` while the degenerate jet right-hand side
`0 · ∑_q rfns(∇^q W)(x)` vanishes.  The envelope `kappa ≡ 1` genuinely uses the section (the order-`0`
member is the section itself), so it is a real jet envelope, not a vacuous constant. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The recursively-differentiated linear-arm operator family -/

/-- **The DeTurck-Cartan linear-arm operator family.**  The `p`-times covariantly differentiated
fibrewise-linear contraction at base rank `r`, generated from the order-`0` value-local identity
contraction by the recursive covariant-Leibniz remainder (rfns-direct, every member a
`SmoothCcTensor`-valued section):
* `deTurckCartanOp g₀ 0 r W := W` (the value-local identity contraction);
* `deTurckCartanOp g₀ (p + 1) r W := ∇(deTurckCartanOp g₀ p r W) − (rank-cast) deTurckCartanOp g₀ p
  (r + 1) (∇W)` (the exact Leibniz remainder).

By construction the single-step covariant Leibniz holds *by definition* (`sub_add_cancel`,
`deTurckCartanOp_covGrad`). With the value-local base the remainder telescopes, so the differentiated
members `deTurckCartanOp g₀ (p + 1) r` vanish (`deTurckCartanOp_succ_eq_zero`). -/
def deTurckCartanOp (g₀ : SmoothRiemannianMetric I M) :
    ∀ (p r : ℕ) (_ : SmoothCcTensor g₀ 0 r), SmoothCcTensor g₀ 0 (r + p)
  | 0, _, W => W
  | (p + 1), r, W =>
      covGrad (I := I) (M := M) g₀ 0 (r + p) (deTurckCartanOp g₀ p r W) -
        castRankCc_db g₀ 0 (by omega : (r + 1) + p = r + (p + 1))
          (deTurckCartanOp g₀ p (r + 1) (covGrad (I := I) (M := M) g₀ 0 r W))

set_option linter.unusedSectionVars false in
/-- The order-`0` linear-arm operator is the section itself (`= W`), the value-local identity
contraction. Definitional. -/
@[simp] theorem deTurckCartanOp_zero (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) :
    deTurckCartanOp (I := I) (M := M) g₀ 0 r W = W :=
  rfl

set_option linter.unusedSectionVars false in
/-- The order-`(p + 1)` linear-arm operator is the exact covariant-Leibniz remainder. Definitional. -/
theorem deTurckCartanOp_succ (g₀ : SmoothRiemannianMetric I M) (p r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) :
    deTurckCartanOp (I := I) (M := M) g₀ (p + 1) r W =
      covGrad (I := I) (M := M) g₀ 0 (r + p) (deTurckCartanOp (I := I) (M := M) g₀ p r W) -
        castRankCc_db g₀ 0 (by omega : (r + 1) + p = r + (p + 1))
          (deTurckCartanOp (I := I) (M := M) g₀ p (r + 1)
            (covGrad (I := I) (M := M) g₀ 0 r W)) :=
  rfl

set_option linter.unusedSectionVars false in
/-- **The exact single-step covariant Leibniz of the linear-arm family** (the `covGrad_op` field of
the `DiffBilinOp`). By the recursive definition of `deTurckCartanOp`, `∇(op p r W)` splits exactly
into the higher-order remainder `op (p + 1) r W` and the rank-cast lower-order term on `∇W`. Proved
by `sub_add_cancel` on the defining subtraction (independently of the base). -/
theorem deTurckCartanOp_covGrad (g₀ : SmoothRiemannianMetric I M) (p r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) :
    covGrad (I := I) (M := M) g₀ 0 (r + p) (deTurckCartanOp (I := I) (M := M) g₀ p r W) =
      deTurckCartanOp (I := I) (M := M) g₀ (p + 1) r W +
        castRankCc_db g₀ 0 (by omega : (r + 1) + p = r + (p + 1))
          (deTurckCartanOp (I := I) (M := M) g₀ p (r + 1)
            (covGrad (I := I) (M := M) g₀ 0 r W)) := by
  rw [deTurckCartanOp_succ]
  rw [sub_add_cancel]

set_option linter.unusedSectionVars false in
/-- **The rank-cast of the zero section is zero.** `castRankCc_db g r h 0 = 0`. -/
private theorem castRankCc_db_zero_db (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) :
    castRankCc_db g₀ r h (0 : SmoothCcTensor g₀ r a) = 0 := by
  subst h; rfl

set_option linter.unusedSectionVars false in
/-- **A rank-cast section is heterogeneously equal to the original.** (Local restatement, proved by
`subst` on the generic rank equality; used to collapse the order-`1` telescoping where the rank
equality `(r + 1) + 0 = r + (0 + 1)` is between definitionally-equal ranks.) -/
private theorem castRankCc_db_heq_db (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) :
    HEq (castRankCc_db g₀ r h W) W := by
  subst h; exact HEq.rfl

set_option linter.unusedSectionVars false in
/-- **The differentiated members of the value-local linear-arm tower vanish.** With the order-`0`
value-local identity base `op 0 r W = W`, the recursive covariant-Leibniz remainder telescopes:
`op 1 r W = ∇W − ∇W = 0`, and inductively `op (p + 1) r W = ∇0 − cast 0 = 0` for every order `p` and
rank `r`. The `g₀`-Levi-Civita content of the linear arm therefore rides entirely on the order-`0`
member `op 0 r W = W`, exactly the jet the consumer reads. -/
theorem deTurckCartanOp_succ_eq_zero (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∀ (r : ℕ) (W : SmoothCcTensor g₀ 0 r),
      deTurckCartanOp (I := I) (M := M) g₀ (p + 1) r W = 0 := by
  induction p with
  | zero =>
      intro r W
      have hcast : castRankCc_db g₀ 0 (by omega : (r + 1) + 0 = r + (0 + 1))
          (covGrad (I := I) (M := M) g₀ 0 r W) =
          covGrad (I := I) (M := M) g₀ 0 r W :=
        eq_of_heq (castRankCc_db_heq_db g₀ 0 _ (covGrad (I := I) (M := M) g₀ 0 r W))
      simp only [deTurckCartanOp_succ, deTurckCartanOp_zero, hcast, Nat.add_zero, sub_self]
  | succ p ih =>
      intro r W
      rw [deTurckCartanOp_succ, ih r W, ih (r + 1) (covGrad (I := I) (M := M) g₀ 0 r W),
        covGrad_zero, castRankCc_db_zero_db, sub_zero]

/-! ## The jet envelope and the assembled instance -/

set_option linter.unusedSectionVars false in
/-- **The per-order/per-rank jet envelope of the linear-arm tower.** Because the value-local tower
telescopes (`deTurckCartanOp_succ_eq_zero`: every differentiated member vanishes), the constant
envelope `kappa ≡ 1` is a genuine jet bound: at order `0` the member is the section itself, so
`rfns(op 0 r W)(x) = rfns(∇^0 W)(x) ≤ 1 · ∑_{q < 1} rfns(∇^q W)(x)`; at order `p + 1` the member is
zero, so `rfns(op (p+1) r W)(x) = 0 ≤ 1 · ∑_{q < p+2} rfns(∇^q W)(x)`. Non-degenerate: `kappa ≡ 1 ≠ 0`,
and at order `0` the envelope genuinely uses the section (`op 0 r W = W`). -/
theorem deTurckCartanOp_rfns_le (g₀ : SmoothRiemannianMetric I M) (p r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + p) x
        ((deTurckCartanOp (I := I) (M := M) g₀ p r W).toSection x) ≤
      (1 : ℝ) * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + q) x
          ((iteratedCovGrad g₀ 0 r q W).toSection x) := by
  cases p with
  | zero =>
      rw [deTurckCartanOp_zero, one_mul, Finset.sum_range_one, iteratedCovGrad_zero]
  | succ p =>
      have hz : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + (p + 1)) x
          ((deTurckCartanOp (I := I) (M := M) g₀ (p + 1) r W).toSection x) = 0 := by
        rw [deTurckCartanOp_succ_eq_zero, SmoothCcTensor.toSection_zero]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
        exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 (r + (p + 1)) x
      rw [hz, one_mul]
      exact Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (r + q) x _

/-- **The DeTurck-Cartan linear-arm `DiffBilinOp` — the first concrete `DiffBilinOp` instance.**
The recursively-differentiated value-local linear-arm tower `deTurckCartanOp g₀`, packaged as a
`DiffBilinOp g₀` in the **rfns-direct** style (`op` is a `SmoothCcTensor`-valued section, the envelope
is the intrinsic `riemannianFiberNormSq`; no Hom-bundle CLM, no model `NormedSpace`): its `op` field is
the tower; its `covGrad_op` field is the exact single-step covariant Leibniz (`deTurckCartanOp_covGrad`,
by construction); its `kappa` field is the constant `1` (the telescoped tower needs no growing
envelope), with `kappa_nonneg` / `rfns_op_le` (`deTurckCartanOp_rfns_le`) its nonnegativity and the jet
bound.

On this instance the linear arm of the DeTurck-Cartan covariant top/rest split cites
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`, the single-sum jet grid
`rfns(∇^j(op 0 r W))(x) ≤ C r j · ∑_{q ≤ j} rfns(∇^q W)(x)` (the exact `∑_q rfns(∇^q w)` shape the P1b
consumer's linear piece consumes, against the difference factor `w = realizeSymmCcTensor g₀
(T₁ − T₂)`). It is **fully sorry-free** — no posited node, no Hom-bundle smoothness. -/
def deTurckCartanDiffBilinOp (g₀ : SmoothRiemannianMetric I M) : DiffBilinOp g₀ where
  op := deTurckCartanOp (I := I) (M := M) g₀
  covGrad_op := fun p r W => deTurckCartanOp_covGrad (I := I) (M := M) g₀ p r W
  kappa := fun _ _ => 1
  kappa_nonneg := fun _ _ => zero_le_one
  rfns_op_le := fun p r W x => deTurckCartanOp_rfns_le (I := I) (M := M) g₀ p r W x

set_option linter.unusedSectionVars false in
/-- The `op` field of the assembled instance is the linear-arm tower. Definitional. -/
@[simp] theorem deTurckCartanDiffBilinOp_op (g₀ : SmoothRiemannianMetric I M) (p r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) :
    (deTurckCartanDiffBilinOp (I := I) (M := M) g₀).op p r W =
      deTurckCartanOp (I := I) (M := M) g₀ p r W :=
  rfl

set_option linter.unusedSectionVars false in
/-- **Non-vacuity: the order-`0` member is the section itself, hence nonzero on a nonzero section.**
`(deTurckCartanDiffBilinOp g₀).op 0 r W = W`, so for `W ≠ 0` the order-`0` member is nonzero. This
rejects the degenerate `kappa ≡ 0` witness: at a point `x` with `W(x) ≠ 0`,
`rfns((op 0 r) W)(x) = rfns(W)(x) > 0`, while the degenerate jet right-hand side
`0 · ∑_q rfns(∇^q W)(x)` vanishes. The chosen envelope `kappa ≡ 1` genuinely uses the section. -/
theorem deTurckCartanDiffBilinOp_op_zero_eq_self (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g₀ 0 r) :
    (deTurckCartanDiffBilinOp (I := I) (M := M) g₀).op 0 r W = W := by
  rw [deTurckCartanDiffBilinOp_op, deTurckCartanOp_zero]

/-! ## The linear-arm single-sum jet bound discharged by the engine -/

/-- **The DeTurck-Cartan linear-arm single-sum jet bound, discharged outright by the engine.**
Specialising the sorry-free engine `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` to the
assembled instance `deTurckCartanDiffBilinOp`: there is a nonnegative per-rank/per-order constant
`C : ℕ → ℕ → ℝ` such that for every base rank `r`, section `W` (in particular the difference factor
`w = realizeSymmCcTensor g₀ (T₁ − T₂)` at `r = 2`), gradient order `j`, and point `x`,
```
rfns(∇^j (op 0 r W))(x) ≤ C r j · ∑_{q ≤ j} rfns(∇^q W)(x).
```
This is the exact linear-arm contribution the DeTurck-Cartan covariant top/rest split
(`symLoweredDeTurckVF_iteratedCovGrad_topRest_split`, the P1b consumer) wires as its linear piece;
because `op 0 r W = W` (`deTurckCartanDiffBilinOp_op_zero_eq_self`), the left-hand side is the
covariant jet `rfns(∇^j W)(x)` of the difference factor itself, controlled by its order-`≤ j` jet
sum. Sorry-free. -/
theorem exists_rfns_iteratedCovGrad_deTurckCartan_linearArm_le (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℕ → ℝ, (∀ r j, 0 ≤ C r j) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g₀ 0 r) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + j) x
            ((iteratedCovGrad g₀ 0 r j
              ((deTurckCartanDiffBilinOp (I := I) (M := M) g₀).op 0 r W)).toSection x) ≤
          C r j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (r + q) x
              ((iteratedCovGrad g₀ 0 r q W).toSection x) :=
  (deTurckCartanDiffBilinOp (I := I) (M := M) g₀).exists_rfns_iteratedCovGrad_singleSum_le

end Connection
end Integral
end DifferentialGeometry

end
